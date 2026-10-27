module

public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

structure CompData : Type 1 where
  G : Type
  [grp : Group G]
  fund : Set (Subgroup G)

attribute [instance] CompData.grp

@[expose] def M11ClassicalClass : Set (Subgroup ↥CFSG.Blueprint.NativeSporadic.M11) :=
  {J | ∃ z, IsClassicalMember3 J z}

@[expose, reducible] noncomputable def CompData.model
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : CompData :=
  ⟨(modelUniv t n 3 1 Nat.prime_three).K,
    fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D⟩

@[expose, reducible] def CompData.sl23 : CompData := ⟨SL(2, ZMod 3), {⊤}⟩

@[expose, reducible] noncomputable def CompData.m11 : CompData :=
  ⟨↥CFSG.Blueprint.NativeSporadic.M11, M11ClassicalClass⟩

@[expose] def CompData.Valid (c : CompData) : Prop :=
  (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n) ∨
    c = CompData.sl23 ∨ c = CompData.m11

structure LieSystemData3 (ι : Type) (X : Type) [Group X] (Φ : Set (Subgroup X)) where
  kind : ι → CompData
  valid : ∀ i, (kind i).Valid
  hom : ∀ i, (kind i).G →* X
  ker_le_center : ∀ i, (hom i).ker ≤ Subgroup.center _
  commute : ∀ i j, i ≠ j → ∀ x y, hom i x * hom j y = hom j y * hom i x
  generate : ⨆ i, (hom i).range = ⊤
  fundamental : ∀ L ∈ Φ, ∃ i, ∃ R ∈ (kind i).fund, L = R.map (hom i)
  meets : ∀ i, ∃ R ∈ (kind i).fund, R.map (hom i) ∈ Φ
  card_eq : ∀ L ∈ Φ, Nat.card L = 24

@[expose] def LieSystem3 (X : Type) [Group X] (Φ : Set (Subgroup X)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι), Nonempty (LieSystemData3 ι X Φ)

@[expose] def LieSystemMod3 {Y : Type} [Group Y] (Λ : Set (Subgroup Y)) : Prop :=
  LieSystem3 (Y ⧸ classicalInvolutionOddCore Y) (oddQuotientFamily Λ)

namespace LieSystemData3

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

def ofEmpty [Subsingleton X] (hΦ : Φ = ∅) : LieSystemData3 PEmpty X Φ where
  kind := fun i => i.elim
  valid := fun i => i.elim
  hom := fun i => i.elim
  ker_le_center := fun i => i.elim
  commute := fun i => i.elim
  generate := by
    rw [eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  fundamental := by simp [hΦ]
  meets := fun i => i.elim
  card_eq := by simp [hΦ]

noncomputable def congr {X' : Type} [Group X'] (e : X ≃* X') (D : LieSystemData3 ι X Φ) :
    LieSystemData3 ι X' (Subgroup.map e.toMonoidHom '' Φ) where
  kind := D.kind
  valid := D.valid
  hom i := e.toMonoidHom.comp (D.hom i)
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  commute i j h x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  generate := by
    have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  fundamental := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  meets i := by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩
  card_eq := by
    rintro _ ⟨L, hL, rfl⟩
    rw [← D.card_eq L hL]
    exact Nat.card_congr (L.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm

noncomputable def sumHom {Y : Type} [Group Y] {Y₁ Y₂ : Subgroup Y} {ι₁ ι₂ : Type}
    {Φ₁ : Set (Subgroup Y₁)} {Φ₂ : Set (Subgroup Y₂)} (D₁ : LieSystemData3 ι₁ Y₁ Φ₁)
    (D₂ : LieSystemData3 ι₂ Y₂ Φ₂) :
    ∀ i : ι₁ ⊕ ι₂, (Sum.elim D₁.kind D₂.kind i).G →* Y
  | Sum.inl j => Y₁.subtype.comp (D₁.hom j)
  | Sum.inr j => Y₂.subtype.comp (D₂.hom j)

noncomputable def sum {Y : Type} [Group Y] (Y₁ Y₂ : Subgroup Y) (hc : Commutes Y₁ Y₂)
    (hgen : Y₁ ⊔ Y₂ = ⊤) {ι₁ ι₂ : Type} {Φ₁ : Set (Subgroup Y₁)} {Φ₂ : Set (Subgroup Y₂)}
    {Φ : Set (Subgroup Y)} (D₁ : LieSystemData3 ι₁ Y₁ Φ₁) (D₂ : LieSystemData3 ι₂ Y₂ Φ₂)
    (hΦ : ∀ L ∈ Φ, (∃ L' ∈ Φ₁, L = L'.map Y₁.subtype) ∨ (∃ L' ∈ Φ₂, L = L'.map Y₂.subtype))
    (hΦ₁ : ∀ L' ∈ Φ₁, L'.map Y₁.subtype ∈ Φ) (hΦ₂ : ∀ L' ∈ Φ₂, L'.map Y₂.subtype ∈ Φ) :
    LieSystemData3 (ι₁ ⊕ ι₂) Y Φ where
  kind := Sum.elim D₁.kind D₂.kind
  valid := fun i => match i with
    | Sum.inl j => D₁.valid j
    | Sum.inr j => D₂.valid j
  hom := sumHom D₁ D₂
  ker_le_center := by
    rintro (j | j) x hx
    · have h : D₁.hom j x = 1 := Subtype.ext hx
      exact D₁.ker_le_center j h
    · have h : D₂.hom j x = 1 := Subtype.ext hx
      exact D₂.ker_le_center j h
  commute := by
    rintro (i | i) (j | j) hij x y
    · have hne : i ≠ j := fun h => hij (congrArg Sum.inl h)
      exact congrArg Subtype.val (D₁.commute i j hne x y)
    · exact hc _ (D₁.hom i x).2 _ (D₂.hom j y).2
    · exact (hc _ (D₁.hom j y).2 _ (D₂.hom i x).2).symm
    · have hne : i ≠ j := fun h => hij (congrArg Sum.inr h)
      exact congrArg Subtype.val (D₂.commute i j hne x y)
  generate := by
    rw [eq_top_iff, ← hgen]
    have h1 : ∀ y : Y₁, (y : Y) ∈ (⨆ i, (sumHom D₁ D₂ i).range : Subgroup Y) := by
      intro y
      have hy : y ∈ (⨆ i, (D₁.hom i).range : Subgroup Y₁) := by rw [D₁.generate]; trivial
      induction hy using Subgroup.iSup_induction' with
      | hp k z hz =>
        obtain ⟨a, rfl⟩ := hz
        exact Subgroup.mem_iSup_of_mem (Sum.inl k) ⟨a, rfl⟩
      | h1 => exact Subgroup.one_mem _
      | hmul u v _ _ hu hv => exact Subgroup.mul_mem _ hu hv
    have h2 : ∀ y : Y₂, (y : Y) ∈ (⨆ i, (sumHom D₁ D₂ i).range : Subgroup Y) := by
      intro y
      have hy : y ∈ (⨆ i, (D₂.hom i).range : Subgroup Y₂) := by rw [D₂.generate]; trivial
      induction hy using Subgroup.iSup_induction' with
      | hp k z hz =>
        obtain ⟨a, rfl⟩ := hz
        exact Subgroup.mem_iSup_of_mem (Sum.inr k) ⟨a, rfl⟩
      | h1 => exact Subgroup.one_mem _
      | hmul u v _ _ hu hv => exact Subgroup.mul_mem _ hu hv
    exact sup_le (fun x hx => h1 ⟨x, hx⟩) (fun x hx => h2 ⟨x, hx⟩)
  fundamental := by
    intro L hL
    rcases hΦ L hL with ⟨L', hL', rfl⟩ | ⟨L', hL', rfl⟩
    · obtain ⟨i, R, hR, rfl⟩ := D₁.fundamental L' hL'
      exact ⟨Sum.inl i, R, hR, Subgroup.map_map _ _ _⟩
    · obtain ⟨i, R, hR, rfl⟩ := D₂.fundamental L' hL'
      exact ⟨Sum.inr i, R, hR, Subgroup.map_map _ _ _⟩
  meets := by
    rintro (i | i)
    · obtain ⟨R, hR, hmem⟩ := D₁.meets i
      exact ⟨R, hR, by
        have := hΦ₁ _ hmem
        rwa [Subgroup.map_map] at this⟩
    · obtain ⟨R, hR, hmem⟩ := D₂.meets i
      exact ⟨R, hR, by
        have := hΦ₂ _ hmem
        rwa [Subgroup.map_map] at this⟩
  card_eq := by
    intro L hL
    rcases hΦ L hL with ⟨L', hL', rfl⟩ | ⟨L', hL', rfl⟩
    · rw [← D₁.card_eq L' hL']
      exact Nat.card_congr (L'.equivMapOfInjective Y₁.subtype Y₁.subtype_injective).toEquiv.symm
    · rw [← D₂.card_eq L' hL']
      exact Nat.card_congr (L'.equivMapOfInjective Y₂.subtype Y₂.subtype_injective).toEquiv.symm

end LieSystemData3

theorem LieSystem3.of_empty {X : Type} [Group X] [Subsingleton X] {Φ : Set (Subgroup X)}
    (hΦ : Φ = ∅) : LieSystem3 X Φ :=
  ⟨PEmpty, inferInstance, ⟨LieSystemData3.ofEmpty hΦ⟩⟩

theorem LieSystem3.congr {X X' : Type} [Group X] [Group X'] {Φ : Set (Subgroup X)}
    (e : X ≃* X') (h : LieSystem3 X Φ) : LieSystem3 X' (Subgroup.map e.toMonoidHom '' Φ) := by
  obtain ⟨ι, hι, ⟨D⟩⟩ := h
  exact ⟨ι, hι, ⟨D.congr e⟩⟩

end CFSG.ClassicalInvolution.Q3
