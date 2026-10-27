module

public import CFSG.ClassicalInvolution.Q3.Q3MTShapeB
public import CFSG.ClassicalInvolution.Q3.Q3URTransfer

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3MT
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open scoped MatrixGroups

section Triple

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem shapeTriple_of_three {A B C : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ Φ) (hC : C ∈ Φ)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (cAB : Commutes A B) (cAC : Commutes A C)
    (cBC : Commutes B C) : MuTab.ShapeTriple Φ := by
  refine ⟨![A, B, C], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hC
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hAB
    · exact absurd hij hAC
    · exact absurd hij hAB.symm
    · rfl
    · exact absurd hij hBC
    · exact absurd hij hAC.symm
    · exact absurd hij hBC.symm
    · rfl
  · intro i j hij a ha b hb
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact cAB a ha b hb
    · exact cAC a ha b hb
    · exact cAB.symm a ha b hb
    · exact absurd rfl hij
    · exact cBC a ha b hb
    · exact cAC.symm a ha b hb
    · exact cBC.symm a ha b hb
    · exact absurd rfl hij

end Triple


section Plus

theorem shapeTriple_of_plus4 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}
    (M : Ih8Model 3 1 Ω .POmegaPlus 4 e) (hne : Ω.Nonempty) : MuTab.ShapeTriple Ω := by
  have hG2 : LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have hD4 : LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have he := ih8Model_exp_eq_one M hD4
  subst he
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨R, hR, -⟩ := (M.mem_iff K₀).mp hK₀
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, c23, c24,
    c34, -⟩ := clique_plus3 (M.cls_sub hR)
  have m₂ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₂
  have m₃ := M.fund_subset_cls ⟨K₀, hK₀⟩ hG2 hD4 h₃
  have hRΩ := M.map_mem hR
  exact shapeTriple_of_three hRΩ (M.map_mem m₂) (M.map_mem m₃)
    (fun h => n12 (map_inj3 M hG2 hD4 hR m₂ h)) (fun h => n13 (map_inj3 M hG2 hD4 hR m₃ h))
    (fun h => n23 (map_inj3 M hG2 hD4 m₂ m₃ h)) (ih8_commutes_map M.ψ c12)
    (ih8_commutes_map M.ψ c13) (ih8_commutes_map M.ψ c23)

end Plus

section Facade

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose] def lieSystemDataU_of_q3 (D : LieSystemData3 ι X Φ) : LieSystemDataU 3 1 ι X Φ where
  kind := D.kind
  valid i := by
    rcases D.valid i with ⟨t, n, ht, hadm, hc⟩ | hc | hc
    · exact Or.inl ⟨t, n, 1, ht, hadm, Or.inl rfl, hc⟩
    · exact Or.inr ⟨by norm_num, Or.inl hc⟩
    · exact Or.inr ⟨by norm_num, Or.inr hc⟩
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate
  fundamental := D.fundamental
  meets := D.meets
  card_eq _ := D.card_eq

end Facade

section Centre

theorem eq_one_of_pow_five_gf3 {ω : GaloisField 3 1} (h : ω ^ 5 = 1) : ω = 1 := by
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)]
    norm_num
  have h3 : ω ^ 3 = ω := by
    have := FiniteField.pow_card ω
    rwa [hcard] at this
  have h5 : ω ^ 5 = ω := by
    calc ω ^ 5 = ω ^ 3 * ω ^ 2 := by ring
      _ = ω * ω ^ 2 := by rw [h3]
      _ = ω ^ 3 := by ring
      _ = ω := h3
  rwa [h5] at h

theorem eq_one_of_mem_center_sl5 {f : SL(5, GaloisField 3 1)}
    (hf : f ∈ Subgroup.center SL(5, GaloisField 3 1)) : f = 1 := by
  obtain ⟨ω, hω5, hωc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hf
  have hω : ω = 1 := eq_one_of_pow_five_gf3 (by simpa using hω5)
  apply Subtype.ext
  rw [← hωc, hω, map_one]
  rfl

theorem eq_one_of_mem_center_psl5 {f : (CompData.model .PSL 5).G}
    (hf : f ∈ Subgroup.center (CompData.model .PSL 5).G) : f = 1 :=
  eq_one_of_mem_center_sl5 (f := f) hf

theorem eq_one_of_pow_five_gf9 {c : GaloisField 3 2} (h : c ^ 5 = 1) : c = 1 := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at h
  have h8 : c ^ 8 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hcard] at this
  have h3 : c ^ 3 = 1 := by
    have e : c ^ 8 = c ^ 5 * c ^ 3 := by ring
    rw [e, h] at h8
    simpa using h8
  have h2 : c ^ 2 = 1 := by
    have e : c ^ 5 = c ^ 3 * c ^ 2 := by ring
    rw [e, h3] at h
    simpa using h
  have e : c ^ 3 = c ^ 2 * c := by ring
  rw [e, h2] at h3
  simpa using h3

theorem eq_one_of_mem_center_psu5 (hadm : StatedLieAdmissible .PSU 5 3 1)
    {f : (CompData.model .PSU 5).G} (hf : f ∈ Subgroup.center (CompData.model .PSU 5).G) :
    f = 1 := by
  obtain ⟨φ, -⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv (p := 3) (f := 1)
    (by norm_num) hadm
  have hz : φ f ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 5) :=
    CFSG.ClassicalInvolution.Asc77.BSC.BSD.map_mem_center φ hf
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_su3 card_gf9 (by norm_num) (by norm_num : 3 ≤ 5) hz
  have hdet := det_suMat (φ f)
  rw [hc] at hdet
  have hc1 : c = 1 := eq_one_of_pow_five_gf9 (by simpa [Matrix.scalar_apply, Matrix.det_diagonal]
    using hdet)
  apply φ.injective
  apply suMat_injective
  rw [hc, hc1, map_one, map_one, suMat_one]

end Centre

section Transport

theorem eq_one_of_mem_center_of_eq_psl5 {c : CompData} (hc : c = CompData.model .PSL 5)
    {f : c.G} (hf : f ∈ Subgroup.center c.G) : f = 1 := by
  subst hc
  exact eq_one_of_mem_center_psl5 hf

theorem eq_one_of_mem_center_of_eq_psu5 (hadm : StatedLieAdmissible .PSU 5 3 1) {c : CompData}
    (hc : c = CompData.model .PSU 5) {f : c.G} (hf : f ∈ Subgroup.center c.G) : f = 1 := by
  subst hc
  exact eq_one_of_mem_center_psu5 hadm hf

theorem eq_one_of_mem_center_of_eq_m11 {c : CompData} (hc : c = CompData.m11) {f : c.G}
    (hf : f ∈ Subgroup.center c.G) : f = 1 := by
  subst hc
  have h : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ := Q3W.center_m11_eq_bot
  rw [show Subgroup.center CompData.m11.G = ⊥ from h, Subgroup.mem_bot] at hf
  exact hf

end Transport

end CFSG.ClassicalInvolution.Q3.Q3AM
