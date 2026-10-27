module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1ThreeQS
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Id
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Ind
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Iso

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem ringEquiv_eq_one_of_card_eq_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (σ : K ≃+* K) : σ = 1 := by
  have h : ∀ x, σ x = x := fun x => by
    rcases eq_zero_or_eq_one_or_eq_neg_one_of_card_eq_three hK x with rfl | rfl | rfl
    · exact map_zero σ
    · exact map_one σ
    · rw [map_neg, map_one]
  exact RingEquiv.ext fun x => (h x).trans rfl

theorem quasisimpleRestrictInput_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    QuasisimpleRestrictInput K := fun _ hU hU4 hne =>
  isQuasisimple_elementaryGroup_three hK (nondegenerate_polarBilin_restrict hU) hU4 hne

theorem u1_spinSeven_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (α : MulAut (spinGroup (quadOdd 3 K))) (hα : α * α = 1) :
    (∃ x : spinGroup (quadOdd 3 K), x * x = 1 ∧ x ∉ center (spinGroup (quadOdd 3 K)) ∧
        α = MulAut.conj x) ∨
      ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
        spinZ K ∈ J ∧ ¬ IsSLTwoOver 3 (↥J ⧸ pPrimeCore 2 ↥J) := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin Nat.prime_three (by decide) hK'
  obtain ⟨σ, F, hF, μ, -, hQF, hπ⟩ := exists_semilinear_spinAction h2 α
  obtain ⟨-, c, hc, hFF⟩ := sq_eq_smul_of_spinAction h2 hF hQF hα hπ
  obtain rfl := ringEquiv_eq_one_of_card_eq_three hK σ
  exact u1_linear Nat.prime_three (by decide) hK' (quasisimpleRestrictInput_three hK)
    (fun a v => hF a v) (fun v => hQF v) hc hFF hπ

theorem harris82Lemma411U1Three_holds : Harris82Lemma411U1Three := by
  intro X _ _ p f _ h3 hX z hz hz1 α hα
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_spinSeven_three h3 hX
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hez : e z = spinZ K := eq_spinZ_of_mem_center Nat.prime_three (by decide) hK'
    ((mem_center_mulEquiv_iff e z).mpr hz) (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
  set α' : MulAut (spinGroup (quadOdd 3 K)) := MulAut.congr e α with hα'
  have hα'2 : α' * α' = 1 := by
    rw [hα', ← map_mul, hα, map_one]
  have hα'e : ∀ y, α' (e y) = e (α y) := fun y => by
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rcases u1_spinSeven_three hK α' hα'2 with ⟨x, hxx, hxZ, hαx⟩ | ⟨J, hJ, hzJ, hSL⟩
  · refine Or.inl ⟨e.symm x, by rw [← map_mul, hxx, map_one], fun h => hxZ ?_, ?_⟩
    · have := (mem_center_mulEquiv_iff e (e.symm x)).mpr h
      rwa [MulEquiv.apply_symm_apply] at this
    · ext y
      have h1 := hα'e y
      rw [hαx, MulAut.conj_apply] at h1
      rw [MulAut.conj_apply]
      apply e.injective
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · refine Or.inr ⟨J.map e.symm.toMonoidHom, ?_, ?_, fun h => hSL ?_⟩
    · have hmap : (fixedSubgroup α').map e.symm.toMonoidHom = fixedSubgroup α := by
        ext y
        rw [mem_map_equiv, MulEquiv.symm_symm, mem_fixedSubgroup, mem_fixedSubgroup, hα'e]
        exact e.injective.eq_iff
      have h := L35.isTwoComponentIn_map_of_injective e.symm.toMonoidHom e.symm.injective hJ
      rwa [hmap] at h
    · rw [mem_map_equiv, MulEquiv.symm_symm, hez]
      exact hzJ
    · rw [h3] at h
      exact isSLTwoOver_quotient_of_mulEquiv
        (J.equivMapOfInjective e.symm.toMonoidHom e.symm.injective) h

end CFSG.ComponentClassification.HarrisLit.T1
