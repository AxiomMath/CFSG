module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89

open CFSG Equiv
open CFSG.Assembly.RankThreeEven (projSp)

noncomputable def perm6EquivOfSp42 {C : Type*} [Group C]
    (e : C ≃* projSp 2 (GaloisField 2 1)) : C ≃* Perm (Fin 6) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num), pow_one]
  ((e.trans (CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 2 _)).trans
    (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2)).trans
    (MulEquiv.ofBijective CFSG.ComponentClassification.PresentationLocal.omegaPerm
      ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
        CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩)

theorem map_perfectResidual_eq_alternatingGroup {C : Type*} [Group C] [Finite C]
    (e : C ≃* Perm (Fin 6)) (hP : Nonempty (perfectResidual C ≃* alternatingGroup (Fin 6))) :
    (perfectResidual C).map e.toMonoidHom = alternatingGroup (Fin 6) := by
  obtain ⟨ι⟩ := hP
  have hcomm : (commutator C).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
      ← commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  have hle : (perfectResidual C).map e.toMonoidHom ≤ alternatingGroup (Fin 6) := by
    rw [← hcomm]
    refine Subgroup.map_mono ?_
    have h := iInf_le (fun i => derivedSeries C i) 1
    rwa [derivedSeries_one] at h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective e.injective, Nat.card_congr ι.toEquiv]

abbrev t01 : Perm (Fin 6) := swap 0 1

abbrev c012 : Perm (Fin 6) := swap 0 1 * swap 1 2

abbrev c12345 : Perm (Fin 6) := swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5

abbrev c234 : Perm (Fin 6) := swap 2 3 * swap 3 4

theorem eq_one_of_commute_c012_c12345 :
    ∀ g : Perm (Fin 6), g * c012 = c012 * g → g * c12345 = c12345 * g → g = 1 := by
  decide +kernel

theorem exists_outer_involution_of_perm6 {C : Type*} [Group C] (e : C ≃* Perm (Fin 6))
    (P : Subgroup C) (hP : P.map e.toMonoidHom = alternatingGroup (Fin 6)) :
    ∃ s : C, s ^ 2 = 1 ∧ (∃ w ∈ P, w ^ 3 = 1 ∧ w ≠ 1 ∧ s * w = w * s) ∧
      ∀ g ∈ P, ∃ x ∈ P, s * x * s⁻¹ ≠ g * x * g⁻¹ := by
  have hmem : ∀ x : C, x ∈ P ↔ e x ∈ alternatingGroup (Fin 6) := by
    intro x
    rw [← hP]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rw [show y = x from e.injective hyx] at hy
      exact hy
  have ht2 : t01 ^ 2 = 1 := by decide
  have hw3 : c234 ^ 3 = 1 := by decide
  have hw1 : c234 ≠ 1 := by decide
  have htw : t01 * c234 = c234 * t01 := by decide
  have hwA : c234 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hc1A : c012 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hc2A : c12345 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have htA : t01 ∉ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  refine ⟨e.symm t01, ?_, ⟨e.symm c234, ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one, ht2]
  · rw [hmem, MulEquiv.apply_symm_apply]
    exact hwA
  · apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one, hw3]
  · intro h
    apply hw1
    have h' := congrArg e h
    rwa [MulEquiv.apply_symm_apply, map_one] at h'
  · apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact htw
  · intro g hg
    by_contra hall
    push Not at hall
    have hgA := (hmem g).mp hg
    have hc1 := hall (e.symm c012) (by rw [hmem, MulEquiv.apply_symm_apply]; exact hc1A)
    have hc2 := hall (e.symm c12345) (by rw [hmem, MulEquiv.apply_symm_apply]; exact hc2A)
    have hc1' := congrArg e hc1
    have hc2' := congrArg e hc2
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at hc1' hc2'
    have h1 : ((e g)⁻¹ * t01) * c012 = c012 * ((e g)⁻¹ * t01) := by
      calc ((e g)⁻¹ * t01) * c012 = (e g)⁻¹ * (t01 * c012 * t01⁻¹) * t01 := by group
        _ = (e g)⁻¹ * (e g * c012 * (e g)⁻¹) * t01 := by rw [hc1']
        _ = c012 * ((e g)⁻¹ * t01) := by group
    have h2 : ((e g)⁻¹ * t01) * c12345 = c12345 * ((e g)⁻¹ * t01) := by
      calc ((e g)⁻¹ * t01) * c12345 = (e g)⁻¹ * (t01 * c12345 * t01⁻¹) * t01 := by group
        _ = (e g)⁻¹ * (e g * c12345 * (e g)⁻¹) * t01 := by rw [hc2']
        _ = c12345 * ((e g)⁻¹ * t01) := by group
    have h3 := eq_one_of_commute_c012_c12345 _ h1 h2
    have h4 : e g = t01 := by
      rw [inv_mul_eq_one] at h3
      exact h3
    rw [h4] at hgA
    exact htA hgA

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89
