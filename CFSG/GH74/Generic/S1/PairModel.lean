module

public import CFSG.GH74.Generic.S1.TPairFacts
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic

public section

open Subgroup CFSG CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

section Map

variable {X Y : Type} [Group X] [Group Y]

theorem linearBlockStandardPair_map_central {F : Type} [Field F] {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) (φ : X →* Y)
    (hφ : ∀ w ∈ W, φ w = 1 → ∀ w' ∈ W, w * w' = w' * w) :
    LinearBlockStandardPair F (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  have hperf : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    have hθW : θ g ∈ W := hrange ▸ ⟨g, rfl⟩
    have hcen : θ.rangeRestrict g ∈ center ↥θ.range := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have := hφ (θ g) hθW hg (w : X) (hrange ▸ w.2)
      exact this.symm
    exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center θ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker) hcen
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem unitaryBlockStandardPair_map_central {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair F p f W U V) (φ : X →* Y)
    (hφ : ∀ w ∈ W, φ w = 1 → ∀ w' ∈ W, w * w' = w' * w) :
    UnitaryBlockStandardPair F p f (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  have hperf : Group.IsPerfect (Su F p f 3) :=
    (CFSG.GH74.L5U5.isQuasisimple_su hF (by norm_num) (fun h' => hq (by
      simpa using (Prod.mk.inj h').2))).1
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    have hθW : θ g ∈ W := hrange ▸ ⟨g, rfl⟩
    have hcen : θ.rangeRestrict g ∈ center ↥θ.range := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have := hφ (θ g) hθW hg (w : X) (hrange ▸ w.2)
      exact this.symm
    exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center θ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker) hcen
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

end Map

structure SL3Pair {H : Type} [Group H] (ε : ℤ) (p f : ℕ) (W V : Subgroup H) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  one_le : 1 ≤ f
  five_le : 5 ≤ p ^ f
  eps : ε = 1 ∨ ε = -1
  le : V ≤ W
  quasi : IsQuasisimple ↥W
  center_odd : ∀ z ∈ W, (∀ w ∈ W, z * w = w * z) → Odd (orderOf z)
  model : (ε = 1 ∧ StatedClassicalModel (↥W ⧸ center ↥W) .PSL 3 p f) ∨
    (ε = -1 ∧ StatedClassicalModel (↥W ⧸ center ↥W) .PSU 3 p f)
  sl2 : CFSG.GH74.GLS.HasSL2Model ↥V (fun q => q = p ^ f)

section Lin

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

omit [Finite F] in
theorem LinearBlockStandardPair.symm' {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) :
    LinearBlockStandardPair F W V U := by
  obtain ⟨θ, c, hr, hk, h'⟩ := h
  exact ⟨θ, c, hr, hk, h'.symm⟩

theorem lin_pair_sl3Pair {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f) {W U V : Subgroup X}
    (hP : LinearBlockStandardPair F W U V) : SL3Pair 1 p f W V := by
  obtain ⟨hWq, hWc⟩ := lin_pair_W_facts hP
  obtain ⟨θ, hrange, hker, h1, h2⟩ := pair_normalize hP
  have hQ : IsQuasisimple SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hsurj : Function.Surjective θ.rangeRestrict := θ.rangeRestrict_surjective
  have hker' : θ.rangeRestrict.ker ≤ center SL(3, F) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hZ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hQ hsurj hker'
  let e₁ := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective θ.rangeRestrict hsurj hker' hZ
  have hle : V ≤ W := by
    rw [← h2, ← hrange]
    exact Subgroup.map_le_range θ _
  obtain ⟨hinj, hrV⟩ := (pair_block_inj hker h1 h2).2.2
  subst hrange
  refine ⟨hp, hp2, hf, h5, Or.inl rfl, hle, hWq, hWc, Or.inl ⟨rfl, ?_⟩, ?_⟩
  · refine ⟨⟨hp, hf, by norm_num, by simp, by simp⟩, F, inferInstance, inferInstance, hF, ?_⟩
    exact ⟨e₁.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩
  · refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
    exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrV)).symm.trans
      (specialLinearGroupEquivStatedSL 2 F)⟩

end Lin

section Uni

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {X : Type} [Group X]

theorem UnitaryBlockStandardPair.symm' {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair F p f W U V) : UnitaryBlockStandardPair F p f W V U := by
  obtain ⟨θ, c, hr, hk, h'⟩ := h
  exact ⟨θ, c, hr, hk, h'.symm⟩

theorem uni_pair_sl3Pair (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h5 : 5 ≤ p ^ f) {W U V : Subgroup X} (hP : UnitaryBlockStandardPair F p f W U V) :
    SL3Pair (-1) p f W V := by
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨hWq, hWc⟩ := uni_pair_W_facts hF hodd hP
  obtain ⟨θ, hrange, hker, h1, h2⟩ := pair_normalize hP
  have hdq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h' => by
    have : p ^ f = 2 := (Prod.mk.inj h').2
    omega
  have hQ : IsQuasisimple (Su F p f 3) := CFSG.GH74.L5U5.isQuasisimple_su hF (by norm_num) hdq
  have hsurj : Function.Surjective θ.rangeRestrict := θ.rangeRestrict_surjective
  have hker' : θ.rangeRestrict.ker ≤ center (Su F p f 3) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker
  have hZ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hQ hsurj hker'
  let e₁ := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective θ.rangeRestrict hsurj hker' hZ
  have hle : V ≤ W := by
    rw [← h2, ← hrange]
    exact Subgroup.map_le_range θ _
  obtain ⟨eV⟩ := (CFSG.ClassicalInvolution.Phan.nonempty_mulEquiv_of_standardPair hF hP).2
  obtain ⟨eS⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two (K := F) (p := p)
    (f := f) hF
  subst hrange
  refine ⟨Fact.out, hp2, hf, h5, Or.inr rfl, hle, hWq, hWc, Or.inr ⟨rfl, ?_⟩, ?_⟩
  · refine ⟨⟨Fact.out, hf, by norm_num, hdq⟩, F, inferInstance, inferInstance, hF, ?_⟩
    exact ⟨e₁.symm.trans (CFSG.GH74.L5U5.centerQuotientEquivStatedProjSu hF (by norm_num) hdq)⟩
  · refine ⟨↥(CFSG.LieType.Steinberg.fixedSubfield F p f), inferInstance, inferInstance,
      CFSG.LieType.Steinberg.card_fixedSubfield hF, ?_⟩
    exact ⟨(eV.symm.trans eS.symm).trans (specialLinearGroupEquivStatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield F p f))⟩

end Uni

end CFSG.GH74.Generic.S1
