module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerOrd
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2U

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148Inner

open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)

theorem sigma_pow_three_eq_one {K : Type} [Field K] [Finite K] {f : ℕ} {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) : σ ^ 3 = 1 := by
  refine RingEquiv.ext fun c => ?_
  have := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ c
  simpa [pow_succ] using this

theorem dvd_centralizer_of_mem_centralizer_short {f : ℕ} (K : Type) [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (ht : t ∈ Subgroup.centralizer
      ((CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    (2 ^ f) ^ 3 ∣ Nat.card (Subgroup.centralizer
      ({t} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have hle : CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ≤
      Subgroup.centralizer ({t} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff] at ht
    exact Subgroup.mem_centralizer_singleton_iff.2 (ht s hs)
  have hS := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.card_d4ShortSL2
    (sigma_pow_three_eq_one hK hσ)
  rw [hK] at hS
  have hdvd : (2 ^ f) ^ 3 ∣
      Nat.card (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) := by
    rw [hS]
    exact dvd_mul_right _ _
  exact hdvd.trans (Subgroup.card_dvd_of_le hle)

theorem dvd_centralizer_of_mem_short {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    (2 ^ f) ^ 3 ∣ Nat.card (Subgroup.centralizer
      ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (f * 3) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  by_cases hev : f % 2 = 0
  · obtain ⟨c, R, hcR, hRC, -, -, F, hFf, hFfin, hFcard, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model Nat.prime_two hf (by norm_num)
        (two_pow_mod_three_of_even hev) hK hσ hzS hz3 hz1
    have hR : (2 ^ f) ^ 3 ∣ Nat.card R := by
      rw [Nat.card_congr e.toEquiv, natCard_SL3 F, hFcard]
      exact (dvd_mul_right _ _).mul_right _
    rw [← natCard_centralizer_conj c z]
    exact hR.trans (Subgroup.card_dvd_of_le hRC)
  · obtain ⟨c, R, hcR, hRC, -, U, hU, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model_unitary_two Nat.prime_two hf
        (by norm_num) (two_pow_mod_three_of_odd (by omega)) hK hσ hzS hz3 hz1
    haveI : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    have hUcard := CFSG.RankThree.PartTwo.Sec4.E27.card_subgroup_unitarySet (ℓ := 2) (f := f) hf U hU
    have hR : (2 ^ f) ^ 3 ∣ Nat.card R := by
      rw [Nat.card_congr e.toEquiv, hUcard]
      exact (dvd_mul_right _ _).mul_right _
    rw [← natCard_centralizer_conj c z]
    exact hR.trans (Subgroup.card_dvd_of_le hRC)

theorem dvd_centralizer_all {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    (2 ^ f) ^ 3 ∣ Nat.card (Subgroup.centralizer
      ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have h3 : ¬ 3 ∣ 2 ^ f := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds K (2 ^ f) σ hK hσ h3 z hz3 hz1
  rw [← natCard_centralizer_conj g z]
  rcases hg with hS | hC
  · have hz3' : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have hz1' : g * z * g⁻¹ ≠ 1 := fun h => hz1 (by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    exact dvd_centralizer_of_mem_short hf K hK hσ hS hz3' hz1'
  · exact dvd_centralizer_of_mem_centralizer_short K hK hσ hC

theorem two_pow_three_le_twoPart_centralizer {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    (2 ^ f) ^ 3 ≤ CFSG.LocalAnalysis.GLTheoremA.S10.twoPart
      (Nat.card (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) :=
  two_pow_three_le_twoPart (Nat.card_pos.ne') (dvd_centralizer_all hf K hK hσ hz3 hz1)

end CFSG.LocalAnalysis.GLTheoremA.K148Inner

end
