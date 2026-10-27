module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Model
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealComp
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealSingle
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUniBlock
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.AutBound
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealEigen

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Dickson.Sec6.I1431
open scoped commutatorElement

section Blocks

variable {K : Type} [Field K] {h : UnitaryFieldData 2 1 K}

noncomputable abbrev excU62_X0 (A : primeFormUnitary h (idGram K 6)) :
    Subgroup (primeFormP h (idGram K 6)) :=
  (fixSubgroup (t6psub_actSU h 6 A)).map
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6))

noncomputable abbrev excU62_N (A : primeFormUnitary h (idGram K 6))
    (i : t6psub_Idx h 6 A) : Subgroup (primeFormP h (idGram K 6)) :=
  (t6psub_block A i).map (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6))

theorem excU62_finite (h : UnitaryFieldData 2 1 K) : Finite (primeFormP h (idGram K 6)) := by
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) Units.val_injective
  infer_instance

theorem excU62_block_isComponent (A : primeFormUnitary h (idGram K 6))
    (H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A)) (i : t6psub_Idx h 6 A) :
    CFSG.Open.IsComponentOf (excU62_N A i)
      (fixSubgroup (primeFormConjHom h (idGram K 6) A)) := by
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) Units.val_injective
  have hq := isQuasisimple_open (u6r_block_quasisimple A H i)
  have hn : ((excU62_N A i).subgroupOf (excU62_X0 A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (u6r_block_le A i)]
    exact fun x c hx hc => u6r_block_normal A i c hc x hx
  exact ⟨(u6r_block_le A i).trans (u6r_map_fix_le A),
    IsSubnormal.step (u6r_block_le A i) hn
      (IsSubnormal.step (u6r_map_fix_le A) (u6r_map_fix_normal A) (IsSubnormal.refl _)), hq⟩

theorem excU62_perfect_le (A : primeFormUnitary h (idGram K 6))
    (H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A))
    {Y : Subgroup (primeFormP h (idGram K 6))} (hY : (⨆ i : t6psub_Idx h 6 A, excU62_N A i) ≤ Y)
    (P : Subgroup (primeFormP h (idGram K 6)))
    (hPC : P ≤ fixSubgroup (primeFormConjHom h (idGram K 6) A)) (hP : ⁅P, P⁆ = P) : P ≤ Y := by
  have hPX : P ≤ excU62_X0 A :=
    le_map_fixSubgroup_of_perfect _ u6r_ker_le_center (t6psub_actSU h 6 A)
      (primeFormConjHom h (idGram K 6) A) (fun x => t6psub_hact A x)
      (QuotientGroup.mk'_surjective _) hPC hP
  refine excU62_perfect_le_of_derived hPX hP ?_
  obtain ⟨k, hk⟩ := u6r_block_derived A H
  exact ⟨k, fun x hx => hY (hk x hx)⟩

theorem excU62_compShape_of_blocks (A : primeFormUnitary h (idGram K 6)) {c : Kˣ}
    (hA3 : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hone : ∀ i j : t6psub_Idx h 6 A, i = j)
    (hT : ∀ i : t6psub_Idx h 6 A,
      ExcU62Type (↥(excU62_N A i) ⧸ Subgroup.center ↥(excU62_N A i))) :
    CompShape ExcU62Type (primeFormConjHom h (idGram K 6) A) := by
  haveI := excU62_finite h
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A) :=
    t6psuh_primaryData_toLin' h A.2 Nat.prime_three (by norm_num) hA3
  by_cases hne : Nonempty (t6psub_Idx h 6 A)
  · obtain ⟨i₀⟩ := hne
    refine excU62_compShape_of_core _ (excU62_N A i₀)
      (Or.inr ⟨excU62_block_isComponent A H i₀, hT i₀⟩) ?_
    refine excU62_perfect_le A H ?_
    exact iSup_le fun i => by rw [hone i i₀]
  · refine excU62_compShape_of_core _ ⊥ (Or.inl rfl) ?_
    refine excU62_perfect_le A H ?_
    exact iSup_le fun i => (hne ⟨i⟩).elim

theorem excU62_block_type (A : primeFormUnitary h (idGram K 6))
    (H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A)) (i : t6psub_Idx h 6 A)
    (hself : dualPoly h.bar (i.1 : K[X]) = i.1) (hdeg : (i.1 : K[X]).natDegree = 1)
    (hm : primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (i.1 : K[X]) = 4 ∨
      primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (i.1 : K[X]) = 5) :
    ExcU62Type (↥(excU62_N A i) ⧸ Subgroup.center ↥(excU62_N A i)) := by
  haveI := h.finite
  haveI : Finite (AdjoinRoot (i.1 : K[X])) := Module.finite_of_finite K
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e1⟩⟩ :=
    Sec6.Up34Chev2.nonempty_specialBlock_mulEquiv_sesqSU_c2 hself
      (selfDualPrimaryBlock H i.1 hself)
  obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
  obtain ⟨e2⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU
    hE b (G := 1) (fun i j => by rw [hb i j, Matrix.one_apply])
  have e0 : ↥(t6psub_block A i) ≃*
      ↥(specialBlock (idForm h 6) (t6psub_toLin A) (i.1 : K[X])) :=
    (Subgroup.equivMapOfInjective (t6psub_block A i) (t6psuh_toLinSU h 6)
      t6psuh_toLinSU_injective).trans (MulEquiv.subgroupCongr (t6psub_map_block A H i))
  have hmdef : Module.finrank (AdjoinRoot (i.1 : K[X]))
      (primaryComponent ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (i.1 : K[X])) =
      primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (i.1 : K[X]) := rfl
  have hm3 : 3 ≤ Module.finrank (AdjoinRoot (i.1 : K[X]))
      (primaryComponent ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (i.1 : K[X])) := by omega
  have hq : ¬(Module.finrank (AdjoinRoot (i.1 : K[X]))
      (primaryComponent ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (i.1 : K[X])) = 3 ∧
      2 ^ (1 * (i.1 : K[X]).natDegree) = 2) := by
    rintro ⟨h3, -⟩
    omega
  have hLM := Sec6.Up34Chev2.lieModel_centerQuotient_of_equiv_gramSU hE hm3 hq
    ((e0.trans e1).trans e2)
  rw [hdeg, one_mul] at hLM
  obtain ⟨-, F, _, _, hF, ⟨eQ⟩⟩ := hLM.statedClassicalModel (by decide)
  have hq1 : CFSG.Open.IsQuasisimple ↥(t6psub_block A i) :=
    isQuasisimple_open (t6psub_isQuasisimple_block A H i)
  obtain ⟨eZ⟩ := LieComp.nonempty_centralQuotient_mulEquiv hq1.1
    ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 6)) 6)).subgroupMap
      (t6psub_block A i))
    (MonoidHom.subgroupMap_surjective _ _)
    (ker_subgroupMap_le_center _ u6r_ker_le_center _)
  exact excU62Type_of_psu hF (by omega) (eZ.symm.trans eQ)

theorem excU62_units_pow_three (h : UnitaryFieldData 2 1 K) (a : Kˣ) : a ^ 3 = 1 := by
  haveI := h.finite
  have hc : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  rw [← hc]
  exact pow_card_eq_one'

theorem excU62_conjHom_scalar (A : primeFormUnitary h (idGram K 6)) {d : Kˣ}
    (hA : (A : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) d) :
    primeFormConjHom h (idGram K 6) A = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin 6) K) * (g : GL (Fin 6) K) * (A : GL (Fin 6) K)⁻¹ = g
  rw [hA, Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

section Eigen

variable (A : primeFormUnitary h (idGram K 6))

theorem excU62_good_data (hA3 : (A : GL (Fin 6) K) ^ 3 = 1) (i : t6psub_Idx h 6 A) :
    ∃ d : K, d ^ 3 = 1 ∧ (i.1 : K[X]) = X - C d :=
  u6r_primaryFactor_eq A hA3 i.1.2

theorem excU62_good_mult (hA3 : (A : GL (Fin 6) K) ^ 3 = 1) (i : t6psub_Idx h 6 A) :
    dualPoly h.bar (i.1 : K[X]) = i.1 ∧ (i.1 : K[X]).natDegree = 1 ∧
      4 ≤ primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (i.1 : K[X]) := by
  obtain ⟨d, hd, hid⟩ := excU62_good_data A hA3 i
  have hself : dualPoly h.bar (i.1 : K[X]) = i.1 := by
    rw [hid]
    exact u6r_dualPoly h odd_one hd
  have hdeg : (i.1 : K[X]).natDegree = 1 := by rw [hid, natDegree_X_sub_C]
  have h2 := i.2.1
  have h3 := i.2.2 hself
  refine ⟨hself, hdeg, ?_⟩
  have h4 : primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) (i.1 : K[X]) ≠ 2 := fun hm => h3 (by simp [hm, hdeg])
  have h5 : primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) (i.1 : K[X]) ≠ 3 := fun hm => h3 (by simp [hm, hdeg])
  omega

theorem excU62_two_good (hA3 : (A : GL (Fin 6) K) ^ 3 = 1) (i j : t6psub_Idx h 6 A) : i = j := by
  classical
  by_contra hij
  have hsq := u6r_squarefree A hA3
  have hsum := finrank_eq_sum_degree_mul_multiplicity hsq
  rw [Module.finrank_fin_fun] at hsum
  have hij' : i.1 ≠ j.1 := fun hh => hij (Subtype.ext hh)
  have hle : ∀ a : primaryFactors ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)), primaryMultiplicity
        ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (a : K[X]) ≤ (a : K[X]).natDegree *
        primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
          Module.End K (Fin 6 → K)) (a : K[X]) := fun a =>
    Nat.le_mul_of_pos_left _ (Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2))
  have hpair := Finset.sum_le_sum_of_subset (f := fun a : primaryFactors
      ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) => (a : K[X]).natDegree *
      primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
        Module.End K (Fin 6 → K)) (a : K[X])) (Finset.subset_univ {i.1, j.1})
  rw [Finset.sum_pair hij', ← hsum] at hpair
  have hi := (excU62_good_mult A hA3 i).2.2
  have hj := (excU62_good_mult A hA3 j).2.2
  have h1 := hle i.1
  have h2 := hle j.1
  omega

theorem excU62_good_mult_lt (hA3 : (A : GL (Fin 6) K) ^ 3 = 1)
    (hA1 : primeFormConjHom h (idGram K 6) A ≠ 1) (i : t6psub_Idx h 6 A) :
    primaryMultiplicity ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) :
      Module.End K (Fin 6 → K)) (i.1 : K[X]) < 6 := by
  obtain ⟨d, hd, hid⟩ := excU62_good_data A hA3 i
  by_contra hge
  push Not at hge
  set x : Module.End K (Fin 6 → K) :=
    ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) : Module.End K (Fin 6 → K))
    with hx
  have hmult : primaryMultiplicity x (i.1 : K[X]) =
      Module.finrank K (primaryComponent x (X - C d)) := by
    rw [hid]
    haveI : Fact (Irreducible (X - C d : K[X])) := ⟨irreducible_X_sub_C d⟩
    have h1 := finrank_primaryComponent x (X - C d)
    rw [natDegree_X_sub_C, one_mul] at h1
    exact h1.symm
  have hle : Module.finrank K (primaryComponent x (X - C d)) ≤ 6 := by
    have := Submodule.finrank_le (primaryComponent x (X - C d))
    rwa [Module.finrank_fin_fun] at this
  have hge' : 6 ≤ primaryMultiplicity x (i.1 : K[X]) := hge
  have heq : Module.finrank K (primaryComponent x (X - C d)) = Module.finrank K (Fin 6 → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have htop := Submodule.eq_top_of_finrank_eq heq
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hd
  have hscal : ∀ v : Fin 6 → K, x v = d • v := fun v =>
    (u6r_mem_primaryComponent_iff A d v).1 (htop ▸ Submodule.mem_top)
  apply hA1
  refine excU62_conjHom_scalar A (d := Units.mk0 d hd0) ?_
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  apply LinearMap.ext
  intro v
  rw [t6psub_glA_scalar_apply]
  exact hscal v

theorem excU62_compShape_one (hA3 : (A : GL (Fin 6) K) ^ 3 = 1)
    (hA1 : primeFormConjHom h (idGram K 6) A ≠ 1) :
    CompShape ExcU62Type (primeFormConjHom h (idGram K 6) A) := by
  have hA3' : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) 1 := by
    rw [hA3, map_one]
  refine excU62_compShape_of_blocks A hA3' (excU62_two_good A hA3) fun i => ?_
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A) :=
    t6psuh_primaryData_toLin' h A.2 Nat.prime_three (by norm_num) hA3'
  obtain ⟨hself, hdeg, h4⟩ := excU62_good_mult A hA3 i
  have h6 := excU62_good_mult_lt A hA3 hA1 i
  exact excU62_block_type A H i hself hdeg (by omega)

end Eigen

theorem excU62_compShape_zeta (A : primeFormUnitary h (idGram K 6)) {c : Kˣ}
    (hA3 : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) (hc : c ≠ 1) :
    CompShape ExcU62Type (primeFormConjHom h (idGram K 6) A) := by
  have hcube : ∀ a : Kˣ, a ^ 3 ≠ c := fun a ha => hc (ha.symm.trans (excU62_units_pow_three h a))
  obtain ⟨i₀, hi₀, hT⟩ := u6r_single odd_one A hA3 hcube
  refine excU62_compShape_of_blocks A hA3 (fun i j => (hi₀ i).trans (hi₀ j).symm) fun i => ?_
  obtain rfl := hi₀ i
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hT
  exact excU62Type_of_psl2 (by simpa using hF) e

theorem excU62_realize (h : UnitaryFieldData 2 1 K) (β : MulAut (primeFormP h (idGram K 6)))
    (hβ : β ^ 3 = 1) :
    ∃ A : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) A = β ∧
      ∃ c : Kˣ, (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  have hC : IsPrimeFormGram (1 : GL (Fin 6) K) := isPrimeFormGram_idGram
  have hn3 : 3 ≤ 6 := by norm_num
  have hq' : ¬(6 = 3 ∧ 2 ^ 1 = 2) := by omega
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  have hσ : primeFormFieldFactor h hC hn3 hq' β = 1 := by
    have hc : Nat.card (K ≃+* K) = 2 := by
      rw [CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.card_ringEquiv_unitary h]
    haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    have h3 : (primeFormFieldFactor h hC hn3 hq' β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
    have h2 : (primeFormFieldFactor h hC hn3 hq' β) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := K ≃+* K) (x := primeFormFieldFactor h hC hn3 hq' β)
      rwa [hc] at this
    set σ := primeFormFieldFactor h hC hn3 hq' β with hσdef
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have hβD : β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
  rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
  obtain ⟨A, hA⟩ := hβD
  have h1 : primeFormPsi h hC ⟨A ^ 3, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_pow, hA, hβ, map_one, one_mul]
  obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
  exact ⟨A, hA, c, by rwa [SubgroupClass.coe_pow] at hc⟩

theorem excU62_compShape_primeForm (h : UnitaryFieldData 2 1 K)
    (β : MulAut (primeFormP h (idGram K 6))) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    CompShape ExcU62Type β := by
  obtain ⟨A, rfl, c, hA3⟩ := excU62_realize h β hβ
  by_cases hc : c = 1
  · subst hc
    exact excU62_compShape_one A (by rwa [map_one] at hA3) hβ1
  · exact excU62_compShape_zeta A hA3 hc

end Blocks

end CFSG.HardMathSupport.Dickson.Bal207

end
