module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSource
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Ree

theorem suzukiZ0_elementary {m : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    IsElementaryAbelian 2 (suzukiZ0 m K) ∧ Nat.card (suzukiZ0 m K) = 2 ^ (2 * m + 1) := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hmul : ∀ v w : K, suzukiSElt m K 0 v * suzukiSElt m K 0 w = suzukiSElt m K 0 (v + w) :=
    fun v w => by rw [suzukiSElt_mul hK]; simp
  refine ⟨{ toIsMulCommutative := isMulCommutative_iff.mpr ?_, exponent_dvd_p := ?_ }, ?_⟩
  · intro x y
    obtain ⟨v, hv⟩ := (mem_suzukiZ0_iff hK).mp x.2
    obtain ⟨w, hw⟩ := (mem_suzukiZ0_iff hK).mp y.2
    apply Subtype.ext
    change (x : suzukiGroup m K) * y = y * x
    rw [← hv, ← hw, hmul, hmul, add_comm]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨v, hv⟩ := (mem_suzukiZ0_iff hK).mp x.2
    apply Subtype.ext
    change (x : suzukiGroup m K) ^ 2 = 1
    rw [← hv, pow_two, hmul, CharTwo.add_self_eq_zero, suzukiSElt_zero_zero hK]
  · rw [← SetLike.coe_sort_coe, coe_suzukiZ0 hK, Nat.card_range_of_injective
      (fun v w h => (suzukiSElt_inj.mp h).2), hK]

theorem small_standard_source_Suzuki_model_exclusion_stated {m : ℕ} (hm : 1 ≤ m) {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ (2 * m + 1)) {X : Type} [Group X]
    (hX : Nonempty (X ≃* suzukiGroup m K)) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 := by
  obtain ⟨e⟩ := hX
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXcard : Nat.card X = (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) *
      ((2 ^ (2 * m + 1)) ^ 2 + 1) := (Nat.card_congr e.toEquiv).trans (suzuki_order hK)
  have hdvd : 2 ^ (4 * m + 2) ∣ Nat.card X := by
    rw [hXcard, show 4 * m + 2 = (2 * m + 1) * 2 by ring, pow_mul]
    exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  refine ⟨fun p f hp2 hY => ?_, ⟨fun e7 => ?_⟩, fun hZ => ?_⟩
  ·
    obtain ⟨⟨hp, -, -⟩, K₀, _, _, hK₀, ⟨ψ⟩⟩ := hY
    have hq : Odd (Nat.card K₀) := by
      rw [hK₀]
      exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨hZel, hZcard⟩ := suzukiZ0_elementary hK
    have : IsElementaryAbelian 2 ((suzukiZ0 m K).map e.symm.toMonoidHom) :=
      IsElementaryAbelian.map _
    have h4 := card_le_four_of_odd_psl_two hq ψ ((suzukiZ0 m K).map e.symm.toMonoidHom)
    rw [Subgroup.card_map_of_injective e.symm.injective, hZcard] at h4
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  ·
    have hX7 : Nat.card X = 2520 := (Nat.card_congr e7.toEquiv).trans card_alternating_seven
    rw [hX7, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num] at hdvd
    have := two_pow_dvd_of_dvd_mul_odd (by decide) hdvd
    omega
  ·
    obtain ⟨-, K₃, _, _, hK₃, ⟨χ⟩⟩ := hZ
    have hX3 : Nat.card X = 20160 :=
      (Nat.card_congr χ.toEquiv).trans (card_psl_three_four K₃ (by rw [hK₃]; norm_num))
    have hdvd' := hdvd
    rw [hX3, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at hdvd'
    have := two_pow_dvd_of_dvd_mul_odd (by decide) hdvd'
    have hm1 : m = 1 := by omega
    subst hm1
    rw [hX3] at hXcard
    norm_num at hXcard

theorem small_standard_source_Suzuki_model_exclusion {m : ℕ} (hm : 1 ≤ m) {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ (2 * m + 1)) {X : Type} [Group X]
    (hX : Nonempty (X ≃* suzukiGroup m K)) :
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 →
        ¬ Assembly.ComponentType.ClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      ¬ Assembly.ComponentType.ClassicalModel X .PSL 3 2 2 := by
  obtain ⟨h1, h2, h3⟩ := small_standard_source_Suzuki_model_exclusion_stated hm hK hX
  exact ⟨fun p f _ hp2 hY => h1 p f hp2
      (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 p f hY), h2,
    fun hZ => h3 (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 3 2 2 hZ)⟩

end CFSG.ComponentClassification.UnbalancingLocal
