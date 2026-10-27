module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.GUCore
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CenterCore
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PairedBlock

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.UnitaryLevi CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary Matrix Polynomial

theorem eq_bot_of_stable_isotropic_cube_scalar {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = (2 ^ 1) ^ 2) (hn : 4 ≤ n) (A : GL (Fin n) K)
    (hA : ∀ x y : Fin n → K,
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n x y)
    (hA3 : A ^ 3 ∈ StatedScalars (Fin n) K) {W : Submodule K (Fin n → K)}
    (hW : IsTotallyIsotropicSU (2 ^ 1) W)
    (hC : ∀ g : StatedSU n (2 ^ 1) K, Commute (g : GL (Fin n) K) A → ∀ w ∈ W,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) : W = ⊥ := by
  classical
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl
  obtain ⟨c, hc⟩ := hA3
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hM : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
      Matrix.scalar (Fin n) (c : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    simpa [GeneralLinearGroup.coe_scalar] using this.symm
  have hcn : (c : K) ^ (2 ^ 1 + 1) = 1 := by
    set e : Fin n → K := Pi.single ⟨0, by omega⟩ 1 with he
    have hee : stdHermForm h n e e = 1 := by
      simp [he, stdHermForm_apply, Pi.single_apply]
    have h3 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e)) = (c : K) • e := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', hM]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hiter : stdHermForm h n (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e)))
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e))) =
        stdHermForm h n e e := by
      rw [hA, hA, hA]
    have hsm : stdHermForm h n ((c : K) • e) ((c : K) • e) =
        h.bar c * c * stdHermForm h n e e := by
      simp [map_smulₛₗ]
      ring
    rw [h3, hsm, hee, mul_one, h.bar_apply] at hiter
    rw [← hiter]
    ring
  have hsq0 := squarefree_minpoly_of_pow_scalar Nat.prime_three (by norm_num) _ hc0 hM
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) := GeneralLinearGroup.toLin A with hxdef
  have hx : (x : Module.End K (Fin n → K)) =
      mulVecLin ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    GeneralLinearGroup.coe_toLin _
  have hsq : Squarefree (minpoly K (x : Module.End K (Fin n → K))) := by rw [hx]; exact hsq0
  have hxU : x ∈ sesqUnitaryGroup (stdHermForm h n) := by
    rw [mem_sesqUnitaryGroup]
    intro v w
    have h1 : ∀ v, ((x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K)) v = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v :=
      fun v => by rw [hxdef, GeneralLinearGroup.coe_toLin]; rfl
    rw [h1, h1]
    exact hA v w
  have H : UnitaryPrimaryData h.bar (stdHermForm h n) x :=
    ⟨fun c => h.bar_bar c, stdHermForm_isSymm h n, stdHermForm_separatingLeft h n, hxU, hsq⟩
  have hmin : minpoly K (x : Module.End K (Fin n → K)) ∣ X ^ 3 - C (c : K) := by
    apply minpoly.dvd
    rw [hx, map_sub, map_pow, aeval_X, aeval_C, mulVecLin_pow', hM]
    refine LinearMap.ext fun v => ?_
    ext i
    simp [Matrix.scalar_apply, Module.algebraMap_end_apply]
  have hself : ∀ a ∈ primaryFactors (x : Module.End K (Fin n → K)), dualPoly h.bar a = a := by
    intro a ha
    obtain ⟨hai, ham, hadvd⟩ := mem_primaryFactors.mp ha
    exact dualPoly_eq_self Nat.prime_three (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1) hK h.bar
      (fun c => h.bar_apply c) hcn hai ham (hadvd.trans hmin)
  have hdeg : ∑ a ∈ primaryFactors (x : Module.End K (Fin n → K)), a.natDegree ≤ 3 := by
    rw [← natDegree_prod_of_monic _ _ (fun a ha => monic_of_mem_primaryFactors ha),
      prod_primaryFactors hsq]
    calc (minpoly K (x : Module.End K (Fin n → K))).natDegree ≤ (X ^ 3 - C (c : K)).natDegree :=
          natDegree_le_of_dvd hmin (X_pow_sub_C_ne_zero (by norm_num) _)
      _ = 3 := natDegree_X_pow_sub_C
  have hn' : 4 ≤ Module.finrank K (Fin n → K) := by simpa using hn
  obtain ⟨ν, hν, hν2⟩ : ∃ ν : K, h.bar ν * ν = 1 ∧ ν ≠ ν⁻¹ := by
    have : Fintype K := Fintype.ofFinite K
    have hcardU : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
      norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hcardU
    have hωu3 : ωu ^ 3 = 1 := by rw [← hωu]; exact pow_orderOf_eq_one ωu
    have hωu1 : ωu ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hωu
      omega
    have hω3 : (ωu : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hωu3, Units.val_one]
    have hω1 : (ωu : K) ≠ 1 := fun h1 => hωu1 (Units.ext h1)
    refine ⟨ωu, ?_, ?_⟩
    · rw [h.bar_apply]
      have : (ωu : K) ^ 2 ^ 1 * (ωu : K) = (ωu : K) ^ 3 := by ring
      rw [this, hω3]
    · intro hneq
      apply hω1
      have h0 : (ωu : K) ≠ 0 := ωu.ne_zero
      have : (ωu : K) * (ωu : K) = 1 := by
        calc (ωu : K) * (ωu : K) = (ωu : K) * (ωu : K)⁻¹ := by rw [← hneq]
          _ = 1 := mul_inv_cancel₀ h0
      have h3 : (ωu : K) ^ 3 = (ωu : K) * ((ωu : K) * (ωu : K)) := by ring
      rw [hω3, this, mul_one] at h3
      exact h3.symm
  have hWt := (ToralCensus.isTotallyIsotropicSU_iff h W).mp hW
  have hC' : ∀ g : LinearMap.GeneralLinearGroup K (Fin n → K),
      g ∈ sesqSpecialUnitaryGroup (stdHermForm h n) →
      Commute (g : Module.End K (Fin n → K)) (x : Module.End K (Fin n → K)) →
      ∀ w ∈ W, (g : Module.End K (Fin n → K)) w ∈ W := by
    intro g hg hgx w hw
    have hg' := toStatedSU_mem hK le_rfl hg
    set g' := (GeneralLinearGroup.toLin (n := Fin n) (R := K)).symm g with hg'def
    have hgA : g = GeneralLinearGroup.toLin g' := (MulEquiv.apply_symm_apply _ _).symm
    have hcomm : Commute (g' : GL (Fin n) K) A := by
      have h1 : GeneralLinearGroup.toLin (g' * A) = GeneralLinearGroup.toLin (A * g') := by
        rw [map_mul, map_mul, ← hgA, ← hxdef]
        exact Units.ext hgx.eq
      exact GeneralLinearGroup.toLin.injective h1
    rw [hgA]
    exact hC ⟨g', hg'⟩ hcomm w hw
  exact eq_bot_of_stable_isotropic h H hself hdeg hn' hν hν2 hWt hC'

end CFSG.HardMathSupport.Curtis.UnitaryLevi
