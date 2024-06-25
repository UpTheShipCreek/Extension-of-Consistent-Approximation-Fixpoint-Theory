import Init.Classical
import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Basic
import Mathlib.Order.OmegaCompletePartialOrder

import Mathlib.Tactic.Tauto


class BoundedPartialOrder (α : Type u) [PartialOrder α] extends BoundedOrder α

class CompleteLatticeFromOrder (α : Type u) [PartialOrder α] extends SupSet α, InfSet α, Sup α, Inf α, BoundedOrder α where
  le_refl : ∀ (a : α), a ≤ a
  le_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c
  lt_iff_le_not_le : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_antisymm : ∀ (a b : α), a ≤ b → b ≤ a → a = b
  le_sup_left : ∀ (a b : α), a ≤ a ⊔ b
  le_sup_right : ∀ (a b : α), b ≤ a ⊔ b
  sup_le : ∀ (a b c : α), a ≤ c → b ≤ c → a ⊔ b ≤ c
  inf_le_left : ∀ (a b : α), a ⊓ b ≤ a
  inf_le_right : ∀ (a b : α), a ⊓ b ≤ b
  le_inf : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c
  le_sSup : ∀ (s : Set α), ∀ a ∈ s, a ≤ sSup s
  sSup_le : ∀ (s : Set α) (a : α), (∀ b ∈ s, b ≤ a) → sSup s ≤ a
  sInf_le : ∀ (s : Set α), ∀ a ∈ s, sInf s ≤ a
  le_sInf : ∀ (s : Set α) (a : α), (∀ b ∈ s, a ≤ b) → a ≤ sInf s

instance CompleteLatticeFromOrder.toCL {α : Type u} [PartialOrder α] [L : CompleteLatticeFromOrder α] :
  CompleteLattice α where
      le_refl := L.le_refl
      le_top := L.le_top
      bot_le := L.bot_le
      le_trans := L.le_trans
      lt_iff_le_not_le := L.lt_iff_le_not_le
      le_antisymm := L.le_antisymm
      le_sup_left := L.le_sup_left
      le_sup_right := L.le_sup_right
      sup_le := L.sup_le
      inf_le_left := L.inf_le_left
      inf_le_right := L.inf_le_right
      le_inf := L.le_inf
      le_sSup := L.le_sSup
      sSup_le := L.sSup_le
      sInf_le := L.sInf_le
      le_sInf := L.le_sInf

def subtypesCreateType (D : Type u) (D1 D2 : D → Prop) [Nonempty (Subtype D1)] [Nonempty (Subtype D2)] : Prop :=
  ∀ (d : D), D1 d ∨ D2 d

def subtypesContainTopBot (D : Type u) (D1 D2 : D → Prop) [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  : Prop :=
  D1 L.top ∧ D1 L.bot ∧ D2 L.top ∧ D2 L.bot

def interlattice_lub (D : Type u) (D1 D2 : D → Prop) [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [BoundedPartialOrder D]  [L1 :(CompleteLatticeFromOrder (Subtype D1))] : Prop :=
  -- D1 ∪ D2 = D
  (subtypesCreateType D D1 D2) ∧
  -- Both contain the elements ⊥ and ⊤
  (subtypesContainTopBot D D1 D2) ∧
  -- Interlattice lub
  -- b ∈ D2
  ∀ (b : D), D2 b →
    --  S ⊆ D1 such that for every x ∈ S, x ≤ b
    ∀ (S : Set (Subtype D1)), (∀ x, x ∈ S → ↑x ≤ b) →
      -- Then ∨L1 S ≤ b
      ↑(L1.sSup S) ≤ b

def interlattice_glb (D : Type u) (D1 D2 : D → Prop) [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [BoundedPartialOrder D] [L2 : (CompleteLatticeFromOrder (Subtype D2))] : Prop :=
  -- D1 ∪ D2 = D
  (subtypesCreateType D D1 D2) ∧
  -- Both contain the elements ⊥ and ⊤
  (subtypesContainTopBot D D1 D2) ∧
  -- Interlattice glb
  -- a ∈ D1
  ∀ (a : D), D1 a →
    -- S ⊆ D2 such that for every x ∈ S x, ≥ a
    ∀ (S : Set (Subtype D2)), (∀ x, x ∈ S → ↑x ≥ a) →
      -- Then, ∧L2 S ≥ a
      ↑(L2.sInf S) ≥ a


instance {D : Type u} (D1 D2 : D → Prop) [PartialOrder D] : LT (Subtype D1 × Subtype D2) :=
{ lt := λ d d' => (d.1 < d'.1 ∧ d'.2 ≤ d.2) ∨ (d.1 ≤ d'.1 ∧ d'.2 < d.2) }

instance {D : Type u} (D1 D2 : D → Prop) [PartialOrder D] : LE (Subtype D1 × Subtype D2) :=
{ le := λ d d' => d.1 ≤ d'.1 ∧ d'.2 ≤ d.2 }
infixl:50 "≲" => (λ (a b : (Subtype _ × Subtype _)) => a ≤ b)


-- The set of pairs (d1, d2) ∈ (D1, D2) such that d1 ≤ d2
def ordered_product {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] : (Subtype D1 × Subtype D2) → Prop :=
  λ d => (d.1 : D) ≤ (d.2 : D)
prefix:50 "⊗" => ordered_product


def consistent_approximating_operator
  {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) : Prop :=
  -- ∀ d, d' ∈ D1 ⊗ D2
  ∀ (d d' : {x : Subtype D1 × Subtype D2 // ⊗x}),
    -- d ≲ d' →
    d.val  ≲ d' →
      -- A d ≲ A d'
      (A d).val ≲ A d'

def reliable
  {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]
  -- A : D1 ⊗ D2 → D1 ⊗ D2 and monotone
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
  -- (a, b) ∈ D1 ⊗ D2
  (d : {x : Subtype D1 × Subtype D2 // ⊗x}) : Prop :=
  -- (a, b) ≲ A (a, b)
    d.val ≲ A d

-- Prove monotonicity of A1 and A2
-- A symmetric operator A : L² — L² is ≲-monotone if
-- and only if for every y ∈ L, A¹(·,y) is monotone and for every x ∈ L,
-- A¹(z,) is antimonotone (or equivalently, if and only if for every y ∈ L,
-- A²(·,y) is antimonotone and for every x ∈ L, A²(x,·) is monotone)

def boundedSubtype (D : Type u) (D1 D2 D' : D → Prop) [PartialOrder D] [BoundedPartialOrder D] (a : (Subtype D1)) (b : (Subtype D2)) : (Subtype D') → Prop :=
  (λ x => (a : D) ≤ (x : D) ∧ (x : D) ≤ (b : D))

def subTypeTopBotEqTypes_L1 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}]  [PartialOrder D] [L : BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] (h : interlattice_lub D D1 D2) : L1.top = L.top ∧ L1.bot = L.bot := by
  unfold interlattice_lub at h
  let subsTopBot := h.right.left
  unfold subtypesContainTopBot at subsTopBot
  let d1Top := subsTopBot.left
  let d1Bot := subsTopBot.right.left

  -- Equal bots
  have bot_le : L.bot ≤ L1.bot := L.bot_le L1.bot
  have bot_le_bot : L1.bot ≤ L.bot :=
    L1.bot_le (⟨L.bot, d1Bot⟩ : Subtype D1)
  have bot_eq : L1.bot = L.bot :=
    le_antisymm bot_le_bot bot_le

  -- Equal tops
  have top_le : L1.top ≤ L.top := L.le_top L1.top
  have top_le_top : L.top ≤ L1.top :=
    L1.le_top (⟨L.top, d1Top⟩ : Subtype D1)
  have top_eq : L1.top = L.top :=
    le_antisymm top_le top_le_top

  exact ⟨top_eq, bot_eq⟩

def subTypeTopBotEqTypes_L2 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  [L2 : CompleteLatticeFromOrder (Subtype D2)] (h : interlattice_glb D D1 D2) : L2.top = L.top ∧ L2.bot = L.bot := by
  unfold interlattice_glb at h
  have subsTopBot := h.right.left
  unfold subtypesContainTopBot at subsTopBot
  have d2Top := subsTopBot.right.right.left
  have d2Bot := subsTopBot.right.right.right

  -- Equal bots
  have bot_le : L.bot ≤ L2.bot := L.bot_le L2.bot
  have bot_le_bot : L2.bot ≤ L.bot :=
    L2.bot_le (⟨L.bot, d2Bot⟩ : Subtype D2)
  have bot_eq : L2.bot = L.bot :=
    le_antisymm bot_le_bot bot_le

  -- Equal tops
  have top_le : L2.top ≤ L.top := L.le_top L2.top
  have top_le_top : L.top ≤ L2.top :=
    L2.le_top (⟨L.top, d2Top⟩ : Subtype D2)
  have top_eq : L2.top = L.top :=
    le_antisymm top_le top_le_top

  exact ⟨top_eq, bot_eq⟩


def subTypeBoundedByBotContainsBot_L1 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] (b : (Subtype D2)) (h : interlattice_lub D D1 D2) : ((boundedSubtype D D1 D2 D1 L1.bot b) L1.bot) := by
  unfold boundedSubtype
  apply And.intro
  .
    rfl
  .
    let bLeBot := L.bot_le b
    have botL1Leq : L1.bot = L.bot := (subTypeTopBotEqTypes_L1 h).right
    rw[←botL1Leq] at bLeBot
    exact bLeBot

def subTypeBoundedByTopContainsTop_L2 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : (Subtype D1)) (h : interlattice_glb D D1 D2) : ((boundedSubtype D D1 D2 D2 a L2.top) L2.top) := by
  unfold boundedSubtype
  apply And.intro
  .
    have aLeTop := L.le_top a
    have topL2Leq : L2.top = L.top := (subTypeTopBotEqTypes_L2 h).left
    rw[←topL2Leq] at aLeTop
    exact aLeTop
  .
    rfl

def subTypeBoundedByBotHasBotasBottom_L1 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] (b : (Subtype D2)) (_ : interlattice_lub D D1 D2) : (∀ x : Subtype (boundedSubtype D D1 D2 D1 L1.bot b), L1.bot ≤ x) := by
  intro h1
  exact
  (λ x : Subtype (boundedSubtype D D1 D2 D1 L1.bot b)
    => L1.bot_le x
  ) h1


def subTypeBoundedByBotHasBotasBottom_L2 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : (Subtype D1)) (_ : interlattice_glb D D1 D2) : (∀ x : Subtype (boundedSubtype D D1 D2 D2 a L2.top), x ≤ L2.top) := by
  intro h1
  exact
  (λ x : Subtype (boundedSubtype D D1 D2 D2 a L2.top)
    => L2.le_top x
  ) h1

def subTypeBoundedContainsItsSuprem_L1 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] (b : (Subtype D2)) (h : interlattice_lub D D1 D2) : ((boundedSubtype D D1 D2 D1 L1.bot b) (L1.sSup (setOf (boundedSubtype D D1 D2 D1 L1.bot b)))) := by
  unfold interlattice_lub at h
  have inter_property := h.right.right b b.prop (setOf (boundedSubtype D D1 D2 D1 L1.bot b))
  have less_than_b : (∀ x ∈ setOf (boundedSubtype D D1 D2 D1 ⊥ b), ↑x ≤ (b : D)) = True := by
    apply propext
    apply Iff.intro
    .
      tauto
    .
      intro _ _ h2
      exact h2.right
  rw [less_than_b] at inter_property
  simp at inter_property
  have sup_greater_than_lower := L1.bot_le
  tauto

def subTypeBoundedContainsItsInfim_L2 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D]  [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : (Subtype D1)) (h : interlattice_glb D D1 D2) : ((boundedSubtype D D1 D2 D2 a L2.top) (L2.sInf (setOf (boundedSubtype D D1 D2 D2 a L2.top)))) := by
  unfold interlattice_glb at h
  have inter_property := h.right.right a a.prop (setOf (boundedSubtype D D1 D2 D2 a L2.top))
  have greater_than_a : (∀ x ∈ setOf (boundedSubtype D D1 D2 D2 a L2.top), (a : D) ≤ ↑x) = True := by
    apply propext
    apply Iff.intro
    .
      tauto
    .
      intro _ _ h2
      exact h2.left
  rw [greater_than_a] at inter_property
  simp at inter_property
  have inf_lower_than_top := L2.le_top
  tauto


def supOfSubSetIsSupOfSubtype_L1 {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] (b : (Subtype D2)) (h : ∀ x ∈ {x | (boundedSubtype D D1 D2 D1 L1.bot b) x}, x ≤ L1.sSup {x | (boundedSubtype D D1 D2 D1 L1.bot b) x}) : ∀ y : {x // (boundedSubtype D D1 D2 D1 L1.bot b) x}, y ≤ L1.sSup {x | (boundedSubtype D D1 D2 D1 L1.bot b) x} :=
  λ y => h y y.property

def infOfSubSetIsInfOfSubtype_L2 {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : (Subtype D1))
(h : ∀ x ∈ {x | (boundedSubtype _ _ _ D2 a L2.top) x}, x ≥ L2.sInf {x | (boundedSubtype _ _ _ D2 a L2.top)  x}) :
∀ x : {x // (boundedSubtype _ _ _ D2 a L2.top) x}, x ≥ L2.sInf {x | (boundedSubtype _ _ _ D2 a L2.top) x}:=
  λ x => h x x.property

def sInfBoundedIsInBounds_L2 {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [L : BoundedPartialOrder D] [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : {x // D1 x}) (h : Set (Subtype (boundedSubtype _ _ _ D2 a L2.top))) (interglb : interlattice_glb D D1 D2) : (boundedSubtype _ _ _ D2 a L2.top) (L2.sInf (Subtype.val '' h)) := by
  apply And.intro
  .
    exact interglb.2.2 a a.prop (Subtype.val '' h) (λ x ⟨x', ⟨_, x'eqx⟩⟩ => x'eqx ▸ x'.prop.1)
  .
    apply L2.le_top

instance CompleteSemilatticeInfBoundedSubtype_L2 {D : Type u} {D1 D2 : D → Prop} [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [BoundedPartialOrder D]  [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : (Subtype D1)) (interglb : interlattice_glb D D1 D2) : CompleteSemilatticeInf ({x // (boundedSubtype D D1 D2 D2 a L2.top) x}) :=
  {
    le := λ x y => (x : D) ≤ (y : D)
    lt := λ x y => (x : D) < (y : D)
    le_refl := λ x => L2.le_refl x
    le_trans := λ x y z => L2.le_trans x y z
    lt_iff_le_not_le := λ x y => L2.lt_iff_le_not_le x y
    le_antisymm := λ x y hxy hyx => Subtype.ext (L2.le_antisymm x.val y.val hxy hyx)
    sInf := λ s => ⟨L2.sInf (Subtype.val '' s), sInfBoundedIsInBounds_L2 a s interglb⟩
    sInf_le := λ s x hx => L2.sInf_le (Subtype.val '' s) x ⟨x, hx, rfl⟩
    le_sInf := λ s x ub => L2.le_sInf (Subtype.val '' s) x (λ _ ⟨x, x_in_s, x_eq_b⟩ => x_eq_b ▸ ub x x_in_s)
  }


def sSupBoundedIsInBounds_L1 {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [L : BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (b : (Subtype D2)) (h : Set (Subtype (boundedSubtype D D1 D2 D1 ⊥ b))) (interlub : interlattice_lub D D1 D2) : (boundedSubtype D D1 D2 D1 ⊥ b) (L1.sSup (Subtype.val '' h)) := by
  apply And.intro
  .
    apply L1.bot_le
  .
    have le_b := interlub.2.2 b b.property (Subtype.val '' h)
    have xleqb : ∀ x ∈ (Subtype.val '' h), ↑x ≤ (b : D) := by
      intro x ⟨x', ⟨_, x'eqx⟩⟩
      have x'leqb := x'.prop.2
      rw[x'eqx] at x'leqb
      exact x'leqb
    exact le_b xleqb

-- SupSet Instance for (Subtype (boundedSubtype D D1 D2 D1 L1.bot b))
instance supSetForBoundedSubtype_L1 {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) : SupSet {x // (boundedSubtype D D1 D2 D1 L1.bot b) x} :=
  {
    sSup := λ s => ⟨L1.sSup (Subtype.val '' s), (sSupBoundedIsInBounds_L1 b s interlub)⟩
  }


def sSupIsLUB {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D] [Nonempty D]
  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)]
  (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2)
  (s : Set {x // (boundedSubtype D D1 D2 D1 L1.bot b) x}) : IsLUB s (((supSetForBoundedSubtype_L1 b interlub).sSup s)) := by
  unfold IsLUB
  unfold IsLeast
  apply And.intro
  .
    intro elem elem_in_s
    have temp := L1.le_sSup (Subtype.val '' s) elem.val
    apply temp
    simp
    apply And.intro
    .
      unfold boundedSubtype at elem
      exact elem.property
    .
      exact elem_in_s
  .
    intro elem elem_ub_s
    unfold upperBounds at elem_ub_s
    have _ : (boundedSubtype D D1 D2 D1 ⊥ b) ((supSetForBoundedSubtype_L1 b interlub).sSup s) := by
      unfold boundedSubtype
      simp
      -- ↑↑(sSup s) ≤ ↑b
      unfold interlattice_lub at interlub
      have le_b := interlub.2.2 b b.property (Subtype.val '' s)
      have xleqb : ∀ x ∈ {x | ∃ y ∈ s, (y : Subtype D1) = x}, ↑x ≤ (b : D) :=
        λ x ⟨hx, ⟨_, xeqhx⟩⟩ => by
          have temp := hx.property.right
          rw[xeqhx] at temp
          exact temp

      exact le_b xleqb
    have L1sSup_lub : L1.sSup (Subtype.val '' s) ≤ elem := by
      have temp := isLUB_sSup (Subtype.val '' s)
      unfold IsLUB at temp
      unfold IsLeast at temp

      have all_elem_le_elem : ∀ x ∈ (Subtype.val '' s), x ≤ elem := by
        intro x ⟨x_in_s, x_eq⟩
        rw [←x_eq.2]
        exact elem_ub_s x_eq.1
      tauto
    exact L1sSup_lub

def Proposition_8_A {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) : (CompleteLattice {x // (boundedSubtype D D1 D2 D1 L1.bot b) x}) :=
  {
    -- The top is the supremum of the whole boundedSubtype
    top := ⟨L1.sSup (setOf (boundedSubtype D D1 D2 D1 L1.bot b)), subTypeBoundedContainsItsSuprem_L1 b interlub⟩
    le_top := supOfSubSetIsSupOfSubtype_L1 b (L1.le_sSup (setOf (boundedSubtype D D1 D2 D1 L1.bot b)))
    -- Bot is the bot of the complete lattice
    bot := ⟨L1.bot, (subTypeBoundedByBotContainsBot_L1 b interlub)⟩
    bot_le := subTypeBoundedByBotHasBotasBottom_L1 b interlub

    __ := @completeLatticeOfSup _ _ (supSetForBoundedSubtype_L1 b interlub) (sSupIsLUB b interlub)
  }


def Proposition_8_B {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : (Subtype D1)) (interglb : interlattice_glb D D1 D2) : (CompleteLattice {x // (boundedSubtype D D1 D2 D2 a L2.top) x}) :=
  @completeLatticeOfCompleteSemilatticeInf {x // (boundedSubtype D D1 D2 D2 a L2.top) x} (CompleteSemilatticeInfBoundedSubtype_L2 a interglb)

def Proposition_9_A {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [L : BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : ∀ x : {x // (boundedSubtype D D1 D2 D1 L1.bot b) x}, ⊥ ≤ (A ⟨(x, b), x.prop.2⟩).val.1 ∧ (A ⟨(x, b), x.prop.2⟩).val.1 ≤ (b : D) := by
  let aₛ := L1.sSup {x | x ≤ b.val}
  have aₛ_b : ⊗ (aₛ, b) :=
    interlub.2.2 b b.property {x | x ≤ b.val} (λ x x_in => x_in)

  have leq : ∀ (x : Subtype D1), x.val ∈ {x | x ≤ b.val} → (x, b) ≲ (aₛ, b) := by
    intro x x_prop
    apply And.intro
    .
      exact L1.le_sSup {x | x ≤ b.val} x x_prop
    .
      rfl
  have A_leq : ∀ x : {x : Subtype D1 // x.val ≤ b}, A ⟨(x, b), x.prop⟩ ≤ A ⟨(aₛ, b), aₛ_b⟩ := by
    intro x
    exact (conA ⟨(x, b), x.prop⟩ ⟨(aₛ, b), aₛ_b⟩ (leq x x.prop))
  have a_A_leq := A_leq ⟨a,ab⟩
  have Aas1_le_Aa2 : (A ⟨(aₛ, b), aₛ_b⟩).val.1 ≤ (A ⟨(a, b), ab⟩).val.2.val:=
    le_trans (A ⟨(aₛ, b), aₛ_b⟩).prop a_A_leq.2
  have Aa2_le_b : (A ⟨(a, b), ab⟩).val.2.val ≤ b.val :=
    A_reliable.2
  have proof : ∀ x : {x // (boundedSubtype D D1 D2 D1 L1.bot b) x}, ⊥ ≤ (A ⟨(x, b), x.prop.2⟩).val.1 ∧ (A ⟨(x, b), x.prop.2⟩).val.1 ≤ b.val := by
    intro ⟨x,⟨_, x_prop⟩⟩
    have k1 : (A ⟨(x, b), x_prop⟩).val.1 ≤ (A ⟨(aₛ, b), aₛ_b⟩).val.1 := (A_leq ⟨x,x_prop⟩).1
    have k2 := Aas1_le_Aa2
    have k3 := Aa2_le_b
    have k12 := O.le_trans (A ⟨(x, b), x_prop⟩).val.1 (A ⟨(aₛ, b), aₛ_b⟩).val.1 (A ⟨(a, b), ab⟩).val.2.val k1 k2
    have k123 := O.le_trans (A ⟨(x, b), x_prop⟩).val.1 (A ⟨(a, b), ab⟩).val.2.val b.val  k12 k3
    exact ⟨L1.bot_le (A ⟨(x, b), x_prop⟩).val.1, k123⟩
  exact proof

def Proposition_9_B {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [L : BoundedPartialOrder D]  [CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : ∀ x : {x // (boundedSubtype D D1 D2 D2 a L2.top) x}, a ≤ (A ⟨(a, x), x.prop.1⟩).val.2.val ∧ (A ⟨(a, x), x.prop.1⟩).val.2.val ≤ (L2.top : D) := by
  let b_star := L2.sInf {x | a ≤ x.val}

  have a_bₛ : ⊗(a, b_star) :=
    interglb.2.2 a a.property {x | a ≤ x.val} (λ x x_in => x_in)
  have leq : ∀ (x : Subtype D2), x.val ∈ {x | a.val ≤ x} → (a, x) ≲ (a, b_star) := by
    intro x x_prop
    apply And.intro
    .
      rfl
    .
      exact L2.sInf_le {x | a.val ≤ x} x x_prop
  have A_leq : ∀ x : {x : Subtype D2 // a.val ≤ x}, (A ⟨(a, x), x.prop⟩) ≤ (A ⟨(a, b_star), a_bₛ⟩)  := by
    intro x
    exact (conA ⟨(a, x), x.prop⟩ ⟨(a, b_star), a_bₛ⟩ (leq x.val x.prop))
  have b_A_leq := A_leq ⟨b, ab⟩
  have a_leq_Aa1 : a ≤ (A ⟨(a, b), ab⟩).val.1:= A_reliable.1
  have proof : ∀ x : {x // (boundedSubtype D D1 D2 D2 a L2.top) x}, a ≤ (A ⟨(a, x), x.prop.1⟩).val.2.val ∧ (A ⟨(a, x), x.prop.1⟩).val.2.val ≤ (L2.top : D) := by
    intro ⟨x, ⟨x_prop, _⟩⟩
    have k1 := O.le_trans (A ⟨(a, b), ab⟩).val.1 (A ⟨(a, b_star), a_bₛ⟩).val.1 (A ⟨(a, b_star), a_bₛ⟩).val.2 b_A_leq.1 (A ⟨(a, b_star), a_bₛ⟩).prop
    have k2 := O.le_trans (A ⟨(a, b), ab⟩).val.1 (A ⟨(a, b_star), a_bₛ⟩).val.2.val (A ⟨(a, x), x_prop⟩).val.2.val k1 (A_leq ⟨x, x_prop⟩).2
    have k3 := O.le_trans a (A ⟨(a, b), ab⟩).val.1 (A ⟨(a, x), x_prop⟩).val.2 a_leq_Aa1 k2
    exact ⟨k3, L2.le_top (A ⟨(a, x), x_prop⟩).val.2⟩
  exact proof

def first  {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : Subtype (boundedSubtype D D1 D2 D1 L1.bot b) → Subtype (boundedSubtype D D1 D2 D1 L1.bot b) :=
  λ x => ⟨(A ⟨(x, b), x.prop.2⟩).val.1, Proposition_9_A a b interlub ab A conA A_reliable x⟩

def second {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D] [CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : Subtype (boundedSubtype D D1 D2 D2 a L2.top) → Subtype (boundedSubtype D D1 D2 D2 a L2.top) :=
  λ x => ⟨(A ⟨(a, x), x.prop.1⟩).val.2, Proposition_9_B a b interglb ab A conA A_reliable x⟩

def A1_monotone {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩)  : Monotone (first a b interlub ab A conA A_reliable) :=
  λ ⟨d1, od1⟩  ⟨d2, od2⟩ hle =>
    have les_inf : ⟨d1, b⟩ ≲ ⟨d2, b⟩ := by
      apply And.intro
      .
        exact hle
      .
        rfl
    (conA ⟨(d1,b), od1.2⟩ ⟨(d2,b), od2.2⟩ les_inf).1

def A2_monotone {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [L : BoundedPartialOrder D]  [CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : Monotone (second a b interglb ab A conA A_reliable) :=
  λ ⟨d1, od1⟩ ⟨d2, od2⟩ hle =>
    have les_inf : ⟨a, d2⟩ ≲ ⟨a, d1⟩ := by
      apply And.intro
      .
        rfl
      .
        exact hle
    (conA ⟨(a, d2), od2.1⟩ ⟨(a, d1), od1.1⟩ les_inf).2

def A1_OrderHom {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : OrderHom (Subtype (boundedSubtype D D1 D2 D1 ⊥ b)) (Subtype (boundedSubtype D D1 D2 D1 ⊥ b)) :=
  {
    toFun := first a b interlub ab A conA A_reliable
    monotone' := A1_monotone a b interlub ab A conA A_reliable
  }

def A2_OrderHom {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : OrderHom (Subtype (boundedSubtype D D1 D2 D2 a ⊤)) (Subtype (boundedSubtype D D1 D2 D2 a ⊤)) :=
  {
    toFun := second a b interglb ab A conA A_reliable
    monotone' := A2_monotone a b interglb ab A conA A_reliable
  }

-- notation b↓
def rOb {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1)  (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : Subtype (boundedSubtype D D1 D2 D1 L1.bot b) :=
  @OrderHom.lfp {x // (boundedSubtype D D1 D2 D1 L1.bot b) x} (Proposition_8_A b interlub) (A1_OrderHom a b interlub ab A conA A_reliable)

-- notation a↑
def rOa  {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : {x // (boundedSubtype _ _ _ D2 a L2.top) x} :=
  @OrderHom.lfp { x // (boundedSubtype _ _ _ D2 a L2.top) x} (Proposition_8_B a interglb) (A2_OrderHom a b interglb ab A conA A_reliable)

def Proposition_10 {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) :
(rOb a b interlub ab A conA A_reliable) ≤ b.val ∧
a.val ≤ (rOa a b interglb ab A conA A_reliable) ∧
(rOa a b interglb ab A conA A_reliable) ≤ b.val ∧
(rOb a b interlub ab A conA A_reliable) ≤ (rOa a b interglb ab A conA A_reliable).val.val := by

  let A₁ := A1_OrderHom a b interlub ab A conA A_reliable
  let A₂ := A2_OrderHom a b interglb ab A conA A_reliable

  let bᵥ := (rOb a b interlub ab A conA A_reliable)
  let aᵤ := (rOa a b interglb ab A conA A_reliable)

  have aᵤ_in : aᵤ ∈ {a_1 | A₂ a_1 ≤ a_1} ∧ aᵤ ∈ lowerBounds {a_1 | A₂ a_1 ≤ a_1} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype D D1 D2 D2 a L2.top) x} (Proposition_8_B a interglb) A₂)
  have b_in_pre : ⟨b, ⟨ab, L2.le_top b⟩⟩ ∈ {a_1 | A₂ a_1 ≤ a_1} := by
    let Aab2_le_b := A_reliable.2
    -- Need to prove that (A (a, b)).2 = A₂ b
    have A2b_le_b : (A ⟨(a, b), ab⟩).val.2 = A₂ ⟨b, ⟨ab, L2.le_top b⟩⟩ := by
      apply Subtype.ext
      exact rfl
    rw [A2b_le_b] at Aab2_le_b
    have ab2_eq_b : (a, b).2 = b := rfl
    rw [ab2_eq_b] at Aab2_le_b
    simp
    exact Aab2_le_b
  -- As thus aᵤ ≤ b since aᵤ is in the lower bounds of the prefixpoints of A₂
  have aᵤ_le_b : aᵤ ≤ b.val := by
    have aᵤ_lb := aᵤ_in.2
    have aᵤ_le : ∀ x, x ∈ {a_1 | A₂ a_1 ≤ a_1} → aᵤ ≤ x := by
      apply aᵤ_lb
    exact aᵤ_le ⟨b, ⟨ab, L2.le_top b⟩⟩ b_in_pre

  let aₛ := L1.sSup {x | x.val ≤ aᵤ}
  -- Proof asserts that aᵤ ≥ a, but that's already included by the definition of aᵤ
  -- So a is in the set of x such that x ≤ aᵤ
  have a_in_pre_aᵤ : a ∈ {x : {x // D1 x} | x.val ≤ aᵤ} := by
    apply aᵤ.prop.1
  -- So aₛ is greater than a
  have aₛ_le_a : a.val ≤ aₛ := by
    exact L1.le_sSup {x | x.val ≤ aᵤ} a a_in_pre_aᵤ
  -- aₛ ≤ aᵤ by interlattice_lub
  have aₛ_le_aᵤ : aₛ.val ≤ aᵤ :=
    interlub.2.2 aᵤ aᵤ.val.prop {x | x.val ≤ aᵤ} (λ x x_in => x_in)
  -- thus aₛ ≤ b
  have aₛ_le_b : aₛ ≤ b.val :=
    O.le_trans aₛ aᵤ b aₛ_le_aᵤ aᵤ_le_b
  -- so we have a ≤ aₛ ≤ aᵤ ≤ b
  -- so ⟨aₛ, b⟩ ≲ (aₛ, aᵤ) ⇒ A (aₛ, b) ≲ A (aₛ, aᵤ)
  -- r1.1 is basically the (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).prop
  have r1 : A ⟨(aₛ, b), aₛ_le_b⟩ ≲ (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val :=
    have temp : (aₛ, b) ≲ (aₛ, ↑aᵤ) := by
      apply And.intro
      .
        rfl
      .
        exact aᵤ_le_b
    conA ⟨(aₛ, b),aₛ_le_b⟩  ⟨(aₛ, aᵤ),aₛ_le_aᵤ⟩ temp
  -- and (a, aᵤ) ≲ (aₛ, aᵤ) ⇒ A (a, aᵤ) ≲ A (aₛ, aᵤ)
  have r2 : A ⟨(a, aᵤ), aᵤ.prop.1⟩ ≲ (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val :=
    have temp2 : (a, ↑aᵤ) ≲ (aₛ, ↑aᵤ) := by
      apply And.intro
      .
        apply aₛ_le_a
      .
        tauto
    conA ⟨(a, aᵤ),aᵤ.prop.1⟩  ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩ temp2

  have r3 : (A ⟨(aₛ, b), aₛ_le_b⟩).val.1 ≤ (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.2.val :=
    O.le_trans (A ⟨(aₛ, b), aₛ_le_b⟩).val.1.val (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.1.val (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.2.val r1.1 (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).prop

  have r4 : (A ⟨(aₛ, b), aₛ_le_b⟩).val.1 ≤ (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2.val :=
    O.le_trans (A ⟨(aₛ, b), aₛ_le_b⟩).val.1.val (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.2.val (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2.val r3 r2.2

  have r5 : A₂ aᵤ = aᵤ :=
    @OrderHom.map_lfp {x // (boundedSubtype _ _ _ D2 a ⊤) x} (Proposition_8_B a interglb) A₂
  have r6 : A₂ aᵤ = (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2 := by
    tauto
  -- A(a*, b)₁ ≤ a↑
  have r7 : (A ⟨(aₛ, b), aₛ_le_b⟩).val.1.val ≤ aᵤ := by
    rw [←r6, r5] at r4
    exact r4
  -- A(a*, b)₁ ∈ {x ∈ L₁ | x ≤ a↑}
  have r8 : (A ⟨(aₛ, b), aₛ_le_b⟩).val.1 ∈ {x : {x // D1 x} | x.val ≤ aᵤ} := r7
  -- A(a*, b)₁ ≤ a* since a* supremum of {x ∈ L₁ | x ≤ a↑}
  have r9 :   (A ⟨(aₛ, b), aₛ_le_b⟩).val.1 ≤ aₛ :=
    L1.le_sSup {x | x.val ≤ aᵤ} (A ⟨(aₛ, b), aₛ_le_b⟩).val.1 r8
  -- Thus a* is a prefixpoint of A(·, b)₁, thus
  -- b↓ = lfp(A(·, b)₁) = ⊓ {x ∈ [⊥, b] | x ≥ A(x, b)₁}
  -- b↓ = lfp(A(·, b)₁) ≤ a* ≤ a↑
  have r10 : ⟨aₛ, ⟨L1.bot_le aₛ , aₛ_le_b⟩⟩ ∈ {x | A₁ x ≤ x} := by
    have notational_eq : ∀ x, A₁ x = (A ⟨(x, b), x.prop.2⟩).val.1 := by
      intro x
      apply Subtype.ext
      exact rfl
    have proof : A₁ ⟨aₛ, ⟨L1.bot_le aₛ , aₛ_le_b⟩⟩ ≤ aₛ := by
      rw [notational_eq]
      exact r9
    exact proof
  have b_d_in : bᵥ ∈ {x | A₁ x ≤ x} ∧ bᵥ ∈ lowerBounds {x | A₁ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype D D1 D2 D1 ⊥ b) x} (Proposition_8_A b interlub) A₁)
  have b_d_le : ∀ x, x ∈ {x | A₁ x ≤ x} → bᵥ ≤ x := by
    apply b_d_in.2
  have b_d_le_aₛ : bᵥ ≤ aₛ := by
    exact b_d_le ⟨aₛ, ⟨L1.bot_le aₛ , aₛ_le_b⟩⟩ r10
  have p1 := O.le_trans bᵥ aₛ b b_d_le_aₛ aₛ_le_b
  have p2 := aᵤ.prop.1
  have p3 := aᵤ_le_b
  have p4 := O.le_trans bᵥ aₛ aᵤ b_d_le_aₛ aₛ_le_aᵤ
  -- b↓ ≤ b, a ≤ a↑, a↑ ≤ b, b↓ ≤ a↑
  exact ⟨p1, p2, p3, p4⟩

-- An A-reliable approximation (a, b) is A-prudent if a ≤ b↓.
def prudent {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]  [CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : Prop :=
  reliable A ⟨(a,b), ab⟩ ∧
  a.val ≤ (rOb a b interlub ab A conA A_reliable).val

def Proposition_11_A {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) (A_prudent : prudent a b interlub ab A conA A_reliable) :
-- (a, b) ≲ (b↑, a↓)
(a, b) ≲ ((rOb a b interlub ab A conA A_reliable).val,(rOa a b interglb ab A conA A_reliable).val) ∧
-- reliable A (b↑, a↓)
reliable A ⟨((rOb a b interlub ab A conA A_reliable).val, (rOa a b interglb ab A conA A_reliable).val), (Proposition_10 a b interlub interglb ab A conA A_reliable).2.2.2⟩  := by

  let A₁ := A1_OrderHom a b interlub ab A conA A_reliable
  let A₂ := A2_OrderHom a b interglb ab A conA A_reliable

  let aᵤ := (rOa a b interglb ab A conA A_reliable)
  let bᵥ := (rOb a b interlub ab A conA A_reliable)

  let P10 := Proposition_10 a b interlub interglb ab A conA A_reliable

  -- (a, b) ≲ (b↑, a↓)
  have ab_le_ba : (a, b) ≲ (bᵥ.val, aᵤ.val) := by
    have a_le_b_d := A_prudent.2
    have aᵤ_le_b := P10.2.2.1
    exact ⟨a_le_b_d, aᵤ_le_b⟩
  -- (b↑, a↓) ≲ A (b↑, a↓)
  have r1 : (bᵥ.val, b) ≲ (bᵥ, aᵤ) := by
    apply And.intro
    .
      rfl
    .
      exact P10.2.2.1
  -- A (b↑, a↓) ≲ A (b↑, a↓)
  have r2 : A ⟨(bᵥ.val, b), P10.1⟩  ≲ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val :=
    conA ⟨(bᵥ.val, b), P10.1⟩ ⟨(bᵥ, aᵤ),P10.2.2.2⟩ r1

  have r3 : (A ⟨(bᵥ.val, b), P10.1⟩).val.1 = bᵥ := by
    have b_d_fix: A₁ bᵥ = bᵥ := @OrderHom.map_lfp {x // (boundedSubtype _ _ _ D1 ⊥ b) x} (Proposition_8_A b interlub) A₁
    have notation_eq : A₁ bᵥ = (A ⟨(bᵥ.val, b), P10.1⟩).val.1 := by
      tauto
    rw [←notation_eq]
    rw [b_d_fix]
  have r4 : bᵥ ≤ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val.1 := by
    have proof := r2.1
    rw [r3] at proof
    exact proof
  have r5 : (a, aᵤ) ≲ (bᵥ, aᵤ) := by
    apply And.intro
    .
      exact A_prudent.2
    .
      rfl
  have r6 : A ⟨(a, aᵤ), P10.2.1⟩ ≲ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val :=
    conA ⟨(a, aᵤ), P10.2.1⟩ ⟨(bᵥ, aᵤ.val), P10.2.2.2⟩ r5
  -- aᵤ fixpoint A(a, x).2
  have r7 : A₂ aᵤ = aᵤ :=
    @OrderHom.map_lfp {x // (boundedSubtype _ _ _ D2 a ⊤) x} (Proposition_8_B a interglb) A₂
  have r8 : A₂ aᵤ = (A ⟨(a, aᵤ), P10.2.1⟩).val.2 := by
    tauto
  have r9 : (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val.2 ≤ aᵤ := by
    have proof := r6.2
    rw [←r8, r7] at proof
    exact proof
  have reliab : (bᵥ.val, aᵤ.val) ≲ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩) := by
    exact ⟨r4, r9⟩
  exact ⟨ab_le_ba, reliab⟩


-- In Proposition 11 need to take the lfp of A(·, a↑)₁
-- For that we need to prove that A(·, a↑)₁ : L → L is a monotone operator
-- Where X is a Complete Lattice
  -- For X = L1, then we need to prove that A(·, a↑)₁ : L1 → L1 is a monotone operator
    -- But A(·, a↑)₁ is not defined in the whole of L1
  -- So, instead we take X = [⊥, a↑]₁, we need to prove that [⊥, a↑]₁ is a complete lattice
  -- And that ⊥ ≤ A(·, a↑)₁ ≤ a↑, i.e. that A(·, a↑)₁ ∈ [⊥, a↑]₁

def revised {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [L : BoundedPartialOrder D]  [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) (A_prudent : prudent a b interlub ab A conA A_reliable) : {x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)} → {x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)} :=

  let aᵤ := rOa a b interglb ab A conA A_reliable
  let bᵥ := (rOb a b interlub ab A conA A_reliable)

  let bᵥaᵤ := (Proposition_10 a b interlub interglb ab A conA A_reliable).2.2.2

  have bᵥaᵤ_reliable := (Proposition_11_A a b interlub interglb ab A conA A_reliable A_prudent).2

  λ x => ⟨(A ⟨(x, aᵤ), x.prop.2⟩).val.1, @Proposition_9_A _ _ _ _ L L1 L2 bᵥ aᵤ interlub bᵥaᵤ A conA bᵥaᵤ_reliable x⟩

instance revisedSubtypeCL {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D] [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) : CompleteLattice {x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)} :=
  let aᵤ := rOa a b interglb ab A conA A_reliable
  Proposition_8_A aᵤ.val interlub

def revised_Monotone {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [L : BoundedPartialOrder D] [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) (A_prudent : prudent a b interlub ab A conA A_reliable) :
@Monotone
{x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)}
{x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)}
(revisedSubtypeCL a b interlub interglb ab A conA A_reliable).toPreorder
(revisedSubtypeCL a b interlub interglb ab A conA A_reliable).toPreorder
(revised a b interlub interglb ab A conA A_reliable A_prudent) := by
  let aᵤ := (rOa a b interglb ab A conA A_reliable)

  intro x y hle
  have h1 : (x.val, aᵤ.val) ≲ (y.val, aᵤ.val) := by
    apply And.intro
    .
      exact hle
    .
      rfl
  have h2 : (A ⟨(x, aᵤ), x.prop.2⟩) ≲ (A ⟨(y, aᵤ.val), y.prop.2⟩).val :=
    conA ⟨(x, aᵤ), x.prop.2⟩ ⟨(y, aᵤ.val), y.prop.2⟩ h1
  exact h2.1

def revised_OrderHom {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D] [L1 : CompleteLatticeFromOrder (Subtype D1)] [CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) (A_prudent : prudent a b interlub ab A conA A_reliable) : OrderHom {x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)} {x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)}:=
  {
    toFun := revised a b interlub interglb ab A conA A_reliable A_prudent
    monotone' := revised_Monotone a b interlub interglb ab A conA A_reliable A_prudent
  }

def Proposition_11_B {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [BoundedPartialOrder D] [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (a : Subtype D1) (b : (Subtype D2)) (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (ab : ⊗(a,b)) (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A) (A_reliable : reliable A ⟨(a,b), ab⟩) (A_prudent : prudent a b interlub ab A conA A_reliable) : prudent (rOb a b interlub ab A conA A_reliable).val (rOa a b interglb ab A conA A_reliable).val interlub (Proposition_10 a b interlub interglb ab A conA A_reliable).2.2.2 A conA (Proposition_11_A a b interlub interglb ab A conA A_reliable A_prudent).2 := by

  let CLaᵤ := revisedSubtypeCL a b interlub interglb ab A conA A_reliable
  let CLb := Proposition_8_A b interlub

  let A₁ := A1_OrderHom a b interlub ab A conA A_reliable
  let A₂ := A2_OrderHom a b interglb ab A conA A_reliable
  let Aₛ := revised_OrderHom a b interlub interglb ab A conA A_reliable A_prudent

  let aᵤ := (rOa a b interglb ab A conA A_reliable)
  let bᵥ := (rOb a b interlub ab A conA A_reliable)
  -- let aₛ := L1.sSup {x | x.val ≤ aᵤ}
  -- lfp(A(·, a↑)₁)
  let aᵤᵥ := @OrderHom.lfp {x : {x // D1 x} // L1.bot ≤ x.val ∧ x.val ≤ (rOa a b interglb ab A conA A_reliable)} CLaᵤ Aₛ

  have P10 := Proposition_10 a b interlub interglb ab A conA A_reliable
  have P11a := (Proposition_11_A a b interlub interglb ab A conA A_reliable A_prudent)

  have A_reliable_rev := P11a.2
  -- have a_b_lei_bd_au := P11a.1

  have r1 : ∀ x ∈ {x : {x // D1 x} | L1.bot ≤ x ∧ x.val ≤ aᵤ}, (x, b) ≲ (x, aᵤ) := by
    intro x _
    apply And.intro
    .
      rfl
    .
      exact P10.2.2.1

  have r2 : ∀ (x : Subtype D1), x ≤ (aᵤ : D) → x ≤ b.val :=
    λ x x_prop => O.le_trans x.val aᵤ b x_prop P10.2.2.1

  -- A(x,b)₁ ≤ A(x,aᵤ)₁
  have r3 : ∀ x : {x : {x // D1 x} // ⊥ ≤ x ∧ x ≤ (aᵤ : D)}, (A ⟨(x, b), r2 x x.prop.2⟩).val.1 ≤ (A ⟨(x, aᵤ), x.prop.2⟩).val.1 :=
    λ x => (conA ⟨(x, b), r2 x x.prop.2⟩ ⟨(x, aᵤ), x.prop.2⟩ (r1 x x.prop)).1

  -- A(·, b)₁ ≤ x
  have r4 : ∀ x : {x : {x : {x // D1 x} // ⊥ ≤ x ∧ x ≤ (aᵤ : D)} // (Aₛ x) ≤ x}, (A ⟨(x, b), r2 x x.val.prop.2⟩).val.1 ≤ x := by
    intro x
    have notation_eq : ∀ x : {x : {x : {x // D1 x} // ⊥ ≤ x ∧ x ≤ (aᵤ : D)} // (Aₛ x) ≤ x}, Aₛ x = (A ⟨(x, aᵤ), x.val.prop.2⟩).val.1 := by
      intro x
      apply Subtype.ext
      exact rfl
    let r3' := r3 x
    rw [←notation_eq] at r3'
    exact O.le_trans (A ⟨(x, b), r2 x x.val.prop.2⟩).val.1 (Aₛ x) x r3' x.prop


  -- A(aₛ, aᵤ)₁ ≤ aᵤ
  have aᵤ_in : aᵤ ∈ {a_1 | A₂ a_1 ≤ a_1} ∧ aᵤ ∈ lowerBounds {a_1 | A₂ a_1 ≤ a_1} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype D D1 D2 D2 a L2.top) x} (Proposition_8_B a interglb) A₂)

  have b_in_pre : ⟨b, ⟨ab, L2.le_top b⟩⟩ ∈ {a_1 | A₂ a_1 ≤ a_1} := by
    let Aab2_le_b := A_reliable.2
    -- Need to prove that (A (a, b)).2 = A₂ b
    have A2b_le_b : (A ⟨(a, b), ab⟩).val.2 = A₂ ⟨b, ⟨ab, L2.le_top b⟩⟩ := by
      apply Subtype.ext
      exact rfl
    rw [A2b_le_b] at Aab2_le_b
    have ab2_eq_b : (a, b).2 = b := rfl
    rw [ab2_eq_b] at Aab2_le_b
    simp
    exact Aab2_le_b

  have aᵤ_le_b : aᵤ ≤ b.val := by
    have aᵤ_lb := aᵤ_in.2
    have aᵤ_le : ∀ x, x ∈ {a_1 | A₂ a_1 ≤ a_1} → aᵤ ≤ x := by
      apply aᵤ_lb
    exact aᵤ_le ⟨b, ⟨ab, L2.le_top b⟩⟩ b_in_pre

  -- aₛ ≤ aᵤ
  -- have aₛ_le_aᵤ : aₛ.val ≤ aᵤ :=
  --   interlub.2.2 aᵤ aᵤ.val.prop {x | x.val ≤ aᵤ} (λ x x_in => x_in)
  -- thus aₛ ≤ b
  -- have aₛ_le_b : aₛ ≤ b.val :=
  --   O.le_trans aₛ aᵤ b aₛ_le_aᵤ aᵤ_le_b
  -- have a_in_pre_aᵤ : a ∈ {x : {x // D1 x} | x.val ≤ aᵤ} := by
  --   apply aᵤ.prop.1
  -- So a ≤ aₛ
  -- have aₛ_le_a : a.val ≤ aₛ := by
  --   exact L1.le_sSup {x | x.val ≤ aᵤ} a a_in_pre_aᵤ
  -- A(a, aᵤ) ≲ A(aₛ, aᵤ)
  -- have r5 : A ⟨(a, aᵤ), aᵤ.prop.1⟩ ≲ (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val :=
  --   have temp2 : (a, ↑aᵤ) ≤ (aₛ, ↑aᵤ) := by
  --     apply And.intro
  --     .
  --       apply aₛ_le_a
  --     .
  --       tauto
  --   conA ⟨(a, aᵤ),aᵤ.prop.1⟩  ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩ temp2
  -- have r6 : A₂ aᵤ = aᵤ :=
  --   @OrderHom.map_lfp {x // (boundedSubtype _ _ _ D2 a ⊤) x} (Proposition_8_B a interglb) A₂
  -- have r7 : A₂ aᵤ = (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2 := by
  --   tauto
  -- r5 => A(a, aᵤ)₁ ≤ A(aₛ, aᵤ)₁ ∧ A(aₛ, aᵤ)₂ ≤ A(a, aᵤ)₂ = aᵤ
  -- have Aaₛaᵤ1_le_aᵤ : (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.1.val ≤ aᵤ := by
  --   -- A(a, aᵤ)₁ ≤ A(aₛ, aᵤ)₁
  --   have t1 := r5.1
  --   -- A(aₛ, aᵤ)₂ ≤ A(a, aᵤ)₂
  --   have t2 := r5.2
  --   -- rw[←r7, r6] at t2
  --   have proof := O.le_trans (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.1.val (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.2.val (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2 (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).prop t2
  --   rw[←r7, r6] at proof
  --   exact proof
  -- have Aaₛaᵤ1_in : (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.1 ∈ {x : {x // D1 x} | x.val ≤ aᵤ} := by
  --   exact Aaₛaᵤ1_le_aᵤ
  -- We found a prefixpoint of A(·, a↑)₁
  -- have Aaₛaᵤ1_le_aₛ : (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.1.val ≤ aₛ := by
  --   exact L1.le_sSup {x | x.val ≤ aᵤ} (A ⟨(aₛ, aᵤ), aₛ_le_aᵤ⟩).val.1 Aaₛaᵤ1_in

  -- Since the prefixpoints of A(·, a↑)₁ are not empty
  -- And every prefixpoint of A(·, a↑)₁ is a prefixpoint of A(·, b)₁
  -- The set of prefixpoints of A(·, b)₁ is a superset of the set of prefixpoints of A(·, a↑)₁
  -- r4
  -- As such the glb of the set of prefixpoints of A(·, b)₁ is less than or equal to the glb of the set of prefixpoints of A(·, a↑)₁
  -- But the glbs of the set of prefixpoints of A(·, b)₁ and A(·, a↑)₁ are b↓ and aₛ respectively

  -- let bᵥPreSet := {x : {x // (boundedSubtype _ _ _ D1 ⊥ b) x} | (A₁ x) ≤ x}
  -- let aᵤᵥPreSet := {x : {x // (boundedSubtype _ _ _ D1 ⊥ aᵤ.val) x} | (Aₛ x) ≤ x}

  -- Since the prefixpoints of A(·, a↑)₁ are not empty
  -- have aᵤᵥSet_Inh : Nonempty aᵤᵥPreSet  :=
  --   ⟨⟨aₛ, ⟨L1.bot_le aₛ, aₛ_le_aᵤ⟩⟩, Aaₛaᵤ1_le_aₛ⟩

  have bᵥ_in : bᵥ ∈ {x | A₁ x ≤ x} ∧ bᵥ ∈ lowerBounds {x | A₁ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype _ _ _ D1 ⊥ b) x} CLb A₁)

  have aᵤᵥ_in : aᵤᵥ ∈ {x | Aₛ x ≤ x} ∧ aᵤᵥ ∈ lowerBounds {x | Aₛ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype D D1 D2 D1 ⊥ aᵤ.val) x} CLaᵤ Aₛ)

  -- ∀ x ∈ {x | Aₛ x ≤ x}, A₁ x ≤ x, i.e. prefixpoints of A(·, a↑)₁ are prefixpoints of A(·, b)₁
  have p1 : ∀ x ∈ {x | Aₛ x ≤ x}, A₁ ⟨x, ⟨L1.bot_le x, O.le_trans x aᵤ b x.prop.2 aᵤ_le_b⟩⟩ ≤ ⟨x, ⟨L1.bot_le x, O.le_trans x aᵤ b x.prop.2 aᵤ_le_b⟩⟩ :=
    λ x x_in => r4 ⟨x, x_in⟩
  -- thus A₁ aᵤᵥ ≤ aᵤᵥ, i.e. aᵤᵥ is a prefixpoint of A(·, b)₁
  -- (since trivially A(a↑↓, a↑) = a↑↓ ≤ a↑↓, thus it is a prefixpoint of A(·, a↑)₁)
  have p2 : A₁ ⟨aᵤᵥ, ⟨L1.bot_le aᵤᵥ, O.le_trans aᵤᵥ aᵤ b aᵤᵥ.prop.2 aᵤ_le_b⟩⟩ ≤ aᵤᵥ.val := by
    exact p1 aᵤᵥ aᵤᵥ_in.1
  -- thus aᵤᵥ ∈ {x | A₁ x ≤ x}
  have aᵤᵥ_in_pre : ⟨aᵤᵥ, ⟨L1.bot_le aᵤᵥ, O.le_trans aᵤᵥ aᵤ b aᵤᵥ.prop.2 aᵤ_le_b⟩⟩ ∈ {x | A₁ x ≤ x.val} := by
    exact p2
  -- ∀ x ∈ {x | A₁ x ≤ x}, bᵥ ≤ x
  have p3 : ∀ x ∈ {x | A₁ x ≤ x}, bᵥ ≤ x := by
    apply bᵥ_in.2
  -- thus bᵥ ≤ aᵤᵥ
  have proof : bᵥ ≤ aᵤᵥ.val := by
    apply p3 ⟨aᵤᵥ, ⟨L1.bot_le aᵤᵥ, O.le_trans aᵤᵥ aᵤ b aᵤᵥ.prop.2 aᵤ_le_b⟩⟩ aᵤᵥ_in_pre

  exact ⟨A_reliable_rev, proof⟩

------------------------------------------------------------------------------
------------------------------- Proposition 12 -------------------------------
------------------------------------------------------------------------------

instance InfoPoset {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] : PartialOrder {x : Subtype D1 × Subtype D2 | ⊗x} :=
{
  -- le := λ d d' => d.val.1 ≤ d'.val.1 ∧ d'.val.2 ≤ d.val.2
  -- lt := λ d d' => (d.val.1 < d'.val.1 ∧ d'.val.2 ≤ d.val.2) ∨ (d.val.1 ≤ d'.val.1 ∧ d'.val.2 < d.val.2)
  le_refl := λ x => ⟨le_refl x.val.1, le_refl x.val.2⟩
  le_trans := λ _ _ _ h1 h2 => ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩
  le_antisymm := λ _ _ h1 h2 => Subtype.ext (Prod.ext (le_antisymm h1.1 h2.1) (le_antisymm h2.2 h1.2)),
  lt_iff_le_not_le := λ a b => by
    apply Iff.intro
    .
      intro h
      apply Or.elim h
      .
        intro h'
        apply And.intro
        .
          exact ⟨(le_not_le_of_lt h'.1).1, h'.2⟩
        .
          have t1 : ¬ b.val.1 ≤ a.val.1 := (le_not_le_of_lt h'.1).2
          have t2 : ¬ b.val.1 ≤ a.val.1 ∨ ¬ a.val.2 ≤ b.val.2 := Or.inl t1
          have t3 : ¬ (b.val.1 ≤ a.val.1 ∧ a.val.2 ≤ b.val.2) := by tauto
          tauto
      .
        intro h'
        apply And.intro
        .
          exact ⟨h'.1, (le_not_le_of_lt h'.2).1⟩
        .
          have t1 : ¬ a.val.2 ≤ b.val.2 := (le_not_le_of_lt h'.2).2
          have t2 : ¬ b.val.1 ≤ a.val.1 ∨ ¬ a.val.2 ≤ b.val.2 := Or.inr t1
          have t3 : ¬ (b.val.1 ≤ a.val.1 ∧ a.val.2 ≤ b.val.2) := by tauto
          tauto
    .
      intro h
      have t1 : a.val.1 ≤ b.val.1 ∧ b.val.2 ≤ a.val.2 := h.1
      apply Or.elim (Classical.em (a.val.1 < b.val.1))
      .
        intro h1
        apply Or.inl (And.intro h1 t1.2)
      .
        intro _
        have t2 : ¬ b.val.1 ≤ a.val.1 ∨ ¬ a.val.2 ≤ b.val.2 := by tauto
        apply t2.elim
        .
          intro h3
          exact Or.inl ⟨lt_of_le_not_le t1.1 h3, t1.2⟩
        .
          intro h3
          exact Or.inr ⟨t1.1, lt_of_le_not_le t1.2 h3⟩
}

class OmegaPosetGivenPoset (α : Type u) [PartialOrder α] where
  ωSup : OmegaCompletePartialOrder.Chain α → α
  le_ωSup : ∀ (c : OmegaCompletePartialOrder.Chain α) (i : ℕ), c i ≤ ωSup c
  ωSup_le : ∀ (c : OmegaCompletePartialOrder.Chain α) (x : α), (∀ i, c i ≤ x) → ωSup c ≤ x

instance OmegaPosetGivenPoset.toOmegaPoset {α : Type u} [PartialOrder α] [OCP : OmegaPosetGivenPoset α] : OmegaCompletePartialOrder α where
  ωSup := OCP.ωSup
  le_ωSup := OCP.le_ωSup
  ωSup_le := OCP.ωSup_le


-- Assuming a monotone chain of pairs of elements of D1 and D2
-- We can prove the first assertion of Prop 12
def Proposition_12_A {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [BoundedPartialOrder D] [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) (chain : @OmegaCompletePartialOrder.Chain {x : Subtype D1 × Subtype D2 | ⊗x} (@InfoPoset _ _ _ O).toPreorder) :
L1.sSup {(chain i).val.1 | i : ℕ} ≤ (L2.sInf {(chain i).val.2 | i : ℕ}).val
:= by

  have NatClassical : ∀ a : ℕ, ∀ b : ℕ, a ≤ b ∨ b < a := by
    intro a b
    apply Or.elim (Classical.em (a ≤ b))
    .
      intro h
      apply Or.inl h
    .
      intro h
      apply Or.inr (Nat.lt_of_not_le h)

  have a_le_b : ∀ u : ℕ, ∀ κ : ℕ, (chain κ).val.1 ≤ (chain u).val.2.val := by
    intro u κ
    apply (NatClassical u κ).elim
    .
      intro h
      have t1 : (chain κ).val.1 ≤ (chain κ).val.2.val :=
        (chain κ).prop
      --{α : Type u_2} {β : Type u_3} [inst✝ : Preorder α] [inst✝¹ : Preorder β] (f : α →o β)
      have t2 : (chain u) ≤ (chain κ) :=
        (@OrderHom.monotone _ _ _ (_) chain) h
      have t3 : (chain κ).val.2.val ≤ (chain u).val.2 :=
        t2.2
      exact O.le_trans (chain κ).val.1 (chain κ).val.2.val (chain u).val.2 t1 t3
    .
      intro h
      have t1 : (chain u).val.1 ≤ (chain u).val.2.val :=
        (chain u).prop
      have t2 : (chain κ) ≤ (chain u).val :=
         (@OrderHom.monotone _ _ _ (_) chain) (le_of_lt h)
      have t3 : (chain κ).val.1 ≤ (chain u).val.1 :=
        t2.1
      exact O.le_trans (chain κ).val.1 (chain u).val.1 (chain u).val.2.val t3 t1

  have b_ub_a : ∀ u : ℕ, (chain u).val.2.val ∈ upperBounds (Subtype.val '' {(chain i).val.1 | i : ℕ}) := by
    intro u a ⟨a', ⟨i, ci_eq_a'⟩, a_eq_a'⟩
    exact a_eq_a' ▸ ci_eq_a' ▸ a_le_b u i

  have b_ub_a' : ∀ u : ℕ, ∀ x ∈ {(chain i).val.1 | i : ℕ}, x ≤ (chain u).val.2.val := by
    intro u x x_in
    have b_ub : ∀ x ∈ (Subtype.val '' {(chain i).val.1 | i : ℕ}), x ≤ (chain u).val.2.val :=  b_ub_a u
    exact b_ub x (Set.mem_image_of_mem Subtype.val x_in)

  let aᵢₙ := L1.sSup {(chain i).val.1 | i : ℕ}

  have aᵢₙ_le_b : ∀ u : ℕ, aᵢₙ ≤ (chain u).val.2.val := by
    intro u
    exact interlub.2.2 (chain u).val.2 (chain u).val.2.prop {(chain i).val.1 | i : ℕ} (b_ub_a' u)


  have aᵢₙ_lb_b : ∀ b ∈ {(chain i).val.2 | i : ℕ}, aᵢₙ ≤ b.val := by
    intro b ⟨i, ci_eq_b⟩
    exact ci_eq_b ▸ aᵢₙ_le_b i

  have aᵢₙ_le_inf_b : aᵢₙ.val ≤ L2.sInf {(chain i).val.2 | i : ℕ} := by
    exact interglb.2.2 aᵢₙ.val aᵢₙ.prop {(chain i).val.2 | i : ℕ} (aᵢₙ_lb_b)

  exact aᵢₙ_le_inf_b

-- Using the first assertion we can prove that this chain (with the supremum defined as in Proposition_12_A) can create an actual Omega Complete Partial Order, i.e. a chain with a supremum
def Proposition_12_B {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [BoundedPartialOrder D] [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2) :
OmegaCompletePartialOrder {x : Subtype D1 × Subtype D2 | ⊗x} :=
{
  ωSup := λ c => ⟨(L1.sSup {(c i).val.1 | i : ℕ}, L2.sInf {(c i).val.2 | i : ℕ}), Proposition_12_A interlub interglb c⟩
  le_ωSup := λ c i => by
    apply And.intro
    .
      have a_in : (c i).val.1 ∈ {(c i).val.1 | i : ℕ} := by
        tauto
      exact L1.le_sSup {(c i).val.1 | i : ℕ} (c i).val.1 a_in
    .
      have b_in : (c i).val.2 ∈ {(c i).val.2 | i : ℕ} := by
        tauto
      exact L2.sInf_le {(c i).val.2 | i : ℕ} (c i).val.2 b_in

  ωSup_le := λ c x h => by
    apply And.intro
    .
      have h1 : ∀ b ∈ {x | ∃ i, (c i).val.1 = x}, b ≤ x.val.1 := by
        exact λ b ⟨i, ci_eq_b⟩ => ci_eq_b ▸ (λ j => (h j).1) i

      exact L1.sSup_le {(c i).val.1 | i : ℕ} x.val.1 h1
    .
      have h2 : ∀ b ∈ {x | ∃ i, (c i).val.2 = x}, x.val.2 ≤ b := by
        exact λ b ⟨i, ci_eq_b⟩ => ci_eq_b ▸ (λ j => (h j).2) i
      exact L2.le_sInf {(c i).val.2 | i : ℕ} x.val.2 h2
}


-- (A_prudent : prudent a b interlub ab A conA A_reliable)
-- (A_reliable : reliable A ⟨(a,b), ab⟩)
def Proposition_12 {D : Type u} {D1 D2 : D → Prop} [O : PartialOrder D] [BoundedPartialOrder D] [L1 : CompleteLatticeFromOrder (Subtype D1)] [L2 : CompleteLatticeFromOrder (Subtype D2)] (interlub : interlattice_lub D D1 D2) (interglb : interlattice_glb D D1 D2)
(chain : @OmegaCompletePartialOrder.Chain {x : Subtype D1 × Subtype D2 | ⊗x} (@InfoPoset _ _ _ O).toPreorder)
(A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) (conA : consistent_approximating_operator A)
(A_reliable : ∀ i, (reliable A ⟨((chain i).val.1, (chain i).val.2), (chain i).prop⟩))
(prudent_chain : ∀ i, prudent (chain i).val.1 (chain i).val.2 interlub (chain i).prop A conA (A_reliable i)) : Prop := by
  let ωCompletePoset := Proposition_12_B interlub interglb

  --let kl := --ωCompletePoset.ωSup chain -- ERROR HERE
  sorry

-- ⟨((chain i).val.1, (chain i).val.2), (chain i).prop⟩
