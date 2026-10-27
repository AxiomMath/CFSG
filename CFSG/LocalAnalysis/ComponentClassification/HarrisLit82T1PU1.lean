module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Fld
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Ind
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Iso

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin

theorem u1_spinSeven {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (α : MulAut (spinGroup (quadOdd 3 K)))
    (hα : α * α = 1) :
    (∃ x : spinGroup (quadOdd 3 K), x * x = 1 ∧ x ∉ center (spinGroup (quadOdd 3 K)) ∧
        α = MulAut.conj x) ∨
      ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
        spinZ K ∈ J ∧ ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin hp hp2 hK
  obtain ⟨σ, F, hF, μ, -, hQF, hπ⟩ := exists_semilinear_spinAction h2 α
  obtain ⟨hσ2, c, hc, hFF⟩ := sq_eq_smul_of_spinAction h2 hF hQF hα hπ
  by_cases hσ1 : σ = 1
  · subst hσ1
    exact u1_linear hp hp2 hK (quasisimpleRestrictInput_of_five_le
      (hK ▸ (hp.odd_of_ne_two hp2).pow) (hK ▸ h5)) (fun a v => hF a v) (fun v => hQF v) hc hFF hπ
  · exact Or.inr (u1_field hp hp2 hK h5 hσ2 hσ1 hF hQF hc hFF hπ)

theorem harris82Lemma411U1_holds : Harris82Lemma411U1 := by
  intro X _ _ p f hp hp2 h5 hX z hz hz1 α hα
  obtain ⟨K, _, _, hK, -, -, -, ⟨e⟩⟩ := nonempty_mulEquiv_spinOdd h5 hX
  have hez : e z = spinZ K := eq_spinZ_of_mem_center hp hp2 hK
    ((mem_center_mulEquiv_iff e z).mpr hz) (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
  set α' : MulAut (spinGroup (quadOdd 3 K)) := MulAut.congr e α with hα'
  have hα'2 : α' * α' = 1 := by
    rw [hα', ← map_mul, hα, map_one]
  have hα'e : ∀ y, α' (e y) = e (α y) := fun y => by
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rcases u1_spinSeven hp hp2 hK h5 α' hα'2 with ⟨x, hxx, hxZ, hαx⟩ | ⟨J, hJ, hzJ, hSL⟩
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
    · exact isSLTwoOver_quotient_of_mulEquiv
        (J.equivMapOfInjective e.symm.toMonoidHom e.symm.injective) h

end CFSG.ComponentClassification.HarrisLit.T1
