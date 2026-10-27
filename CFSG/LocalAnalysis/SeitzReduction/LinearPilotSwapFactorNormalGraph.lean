module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphFour

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)

section Arith

theorem prod_Icc_odd_split (q r : ℕ) :
    ∏ j ∈ Finset.Icc 1 (2 * r + 1), (q ^ j - 1) =
      (∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1)) *
        ∏ i ∈ Finset.range (r + 1), (q ^ (2 * i + 1) - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : ∏ j ∈ Finset.Icc 1 (2 * (r + 1) + 1), (q ^ j - 1) =
        (∏ j ∈ Finset.Icc 1 (2 * r + 1), (q ^ j - 1)) * (q ^ (2 * (r + 1)) - 1) *
          (q ^ (2 * (r + 1) + 1) - 1) := by
      rw [show 2 * (r + 1) + 1 = (2 * r + 1 + 1) + 1 by ring,
        Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega),
        show 2 * r + 1 + 1 = 2 * (r + 1) by ring]
    rw [h1, ih, Finset.prod_Icc_succ_top (by omega), Finset.prod_range_succ (n := r + 1)]
    ring

theorem ppd_not_dvd_two_mul {p k f : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hf : 1 ≤ f)
    (hfk : f < k) (N : ℕ) : ¬ p ∣ 2 * f * (2 ^ f) ^ N := by
  have hk0 : 0 < k := by omega
  have hpk := index_lt_of_isPrimitivePrimeDivisor hp hk0
  have hp2 : ¬ p ∣ 2 := fun h =>
    hp.ne_two hk0 ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).1 h)
  intro h
  rcases (Nat.Prime.dvd_mul hp.prime).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp.prime).1 h with h | h
    · exact hp2 h
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · rw [← pow_mul] at h
    exact hp2 (hp.prime.dvd_of_dvd_pow h)

theorem ppd_not_dvd_prod_odd {p k f r : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk0 : 0 < k)
    (hk : ∀ i, ¬ k ∣ f * (2 * i + 1)) :
    ¬ p ∣ ∏ i ∈ Finset.range (r + 1), ((2 ^ f) ^ (2 * i + 1) - 1) := by
  rw [Prime.dvd_finsetProd_iff hp.prime.prime]
  rintro ⟨i, -, hi⟩
  rw [← pow_mul] at hi
  exact hk i ((hp.dvd_sub_one_iff hk0 _).1 hi)

end Arith

section GraphOdd

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem card_fixedSubgroup_graph_odd {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : n = 2 * r + 1) (hr : 1 ≤ r) (A : GL (Fin n) K)
    (hθ : (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1) :
    Nat.card (fixedSubgroup (conjAut n K A * dualAut n K)) =
      (2 ^ f) ^ (r ^ 2) * ∏ i ∈ Finset.Icc 1 r, ((2 ^ f) ^ (2 * i) - 1) := by
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨C, hC, hcard, -⟩ := card_fixedSubgroup_graph_eq hf hK (by omega) A hθ
  rcases hC with hC1 | ⟨r', hr', -⟩
  · rw [hcard, hC1, card_matrixIsometryGroup_one_of_odd hn, SymplecticFlag.card_statedSp, hK]
  · omega

theorem card_mulAut_dvd_odd {f r : ℕ} (hK : Nat.card K = 2 ^ f) (hn : n = 2 * r + 1)
    (hr : 1 ≤ r) :
    Nat.card (MulAut (projectiveSL n K)) ∣ 2 * f * (2 ^ f) ^ (n * (n - 1) / 2) *
      ((∏ i ∈ Finset.Icc 1 r, ((2 ^ f) ^ (2 * i) - 1)) *
        ∏ i ∈ Finset.range (r + 1), ((2 ^ f) ^ (2 * i + 1) - 1)) := by
  have h := card_mulAut_projectiveSL_dvd (K := K) (n := n) (by omega) hK
  rw [card_GL_eq, hK, hn, prod_Icc_odd_split] at h
  rw [hn]
  simpa only [mul_assoc] using h

theorem graphOddPairExclusion (hn : 4 ≤ n) {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    GraphOddPairExclusion n f K := by
  intro hno A θ₂ hθ₁ h₂ hC2
  obtain ⟨r, hr⟩ := hno
  have hr1 : 1 ≤ r := by omega
  set q := 2 ^ f with hq
  set S := ∏ i ∈ Finset.Icc 1 r, (q ^ (2 * i) - 1) with hS
  set O := ∏ i ∈ Finset.range (r + 1), (q ^ (2 * i + 1) - 1) with hO
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hS0 : S ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => by
    have : 2 ≤ q ^ (2 * i) :=
      le_trans hq2 (Nat.le_self_pow (by have := (Finset.mem_Icc.1 hi).1; omega) q)
    omega
  have h1 := card_fixedSubgroup_graph_odd (by omega) hK hr hr1 A hθ₁
  have hA := card_mulAut_dvd_odd (K := K) hK hr hr1
  have hC : Nat.card (fixedSubgroup θ₂) ∣ 2 * f * q ^ (n * (n - 1) / 2) * O := by
    have h3 := hC2.trans hA
    rw [h1] at h3
    have h4 : q ^ (r ^ 2) * S * Nat.card (fixedSubgroup θ₂) =
        S * (q ^ (r ^ 2) * Nat.card (fixedSubgroup θ₂)) := by ring
    have h5 : 2 * f * q ^ (n * (n - 1) / 2) * (S * O) =
        S * (2 * f * q ^ (n * (n - 1) / 2) * O) := by ring
    rw [h4, h5] at h3
    exact (Dvd.intro_left _ rfl).trans ((mul_dvd_mul_iff_left hS0).1 h3)
  rcases h₂ with ⟨B, rfl, hθ₂⟩ | hF
  ·
    have hr2 : 2 ≤ r := by omega
    have hk8 : 2 * 2 * 2 ≤ 2 * f * r := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hf) hr2
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * f * r) (by omega) (by omega)
    have hpS : p ∣ S := by
      have h7 : p ∣ q ^ (2 * r) - 1 := by
        rw [hq, ← pow_mul, show f * (2 * r) = 2 * f * r by ring]
        exact hp.dvd
      exact h7.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨hr1, le_rfl⟩))
    have h2 := card_fixedSubgroup_graph_odd (by omega) hK hr hr1 B hθ₂
    have hpC : p ∣ Nat.card (fixedSubgroup (conjAut n K B * dualAut n K)) := by
      rw [h2]
      exact Dvd.dvd.mul_left hpS _
    have hp2 := hpC.trans hC
    have hfk : f < 2 * f * r := by
      have := Nat.mul_le_mul_left (2 * f) hr1
      omega
    rcases (Nat.Prime.dvd_mul hp.prime).1 hp2 with h | h
    · exact ppd_not_dvd_two_mul hp (by omega) hfk _ h
    · refine ppd_not_dvd_prod_odd hp (by omega) (fun i hi => ?_) h
      obtain ⟨c, hc⟩ := hi
      have : 2 * (r * c) = 2 * i + 1 := by
        have h8 : f * (2 * (r * c)) = f * (2 * i + 1) := by rw [hc]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) h8
      omega
  ·
    obtain ⟨a, ha⟩ := hF.1
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * f) (by omega) (by omega)
    have hp4 : p ∣ (2 ^ a) ^ 4 - 1 := by
      rw [← pow_mul, show a * 4 = 2 * f by omega]
      exact hp.dvd
    have hpq : ∀ s, s ∣ 2 ^ a - 1 ∨ s ∣ 2 ^ a + 1 → ¬ p ∣ s := by
      intro s hs hps
      have h9 : 2 ^ a - 1 ∣ 2 ^ f - 1 ∧ 2 ^ a + 1 ∣ 2 ^ f - 1 := by
        have h10 : 2 ^ f - 1 = (2 ^ a - 1) * (2 ^ a + 1) := by
          rw [sub_one_mul_add_one, ← pow_mul, show a * 2 = f by omega]
        exact ⟨Dvd.intro _ h10.symm, Dvd.intro_left _ h10.symm⟩
      have h11 : p ∣ 2 ^ f - 1 := by
        rcases hs with hs | hs
        · exact (hps.trans hs).trans h9.1
        · exact (hps.trans hs).trans h9.2
      have := (hp.dvd_sub_one_iff (by omega) f).1 h11
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    have hpX : p ∣ Nat.card (perfectCore (fixedSubgroup θ₂)) := by
      rw [ha] at hF
      have h4mem : 4 ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨by norm_num, hn⟩
      rcases fieldTypeCore_normal_form (by omega) hF with ⟨s, hs, hX⟩ | ⟨s, hs, hX⟩
      · have h12 : p ∣ Nat.card (perfectCore (fixedSubgroup θ₂)) * s := by
          rw [hX]
          exact Dvd.dvd.mul_left
            (hp4.trans (Finset.dvd_prod_of_mem (fun j => (2 ^ a) ^ j - 1) h4mem)) _
        rcases (Nat.Prime.dvd_mul hp.prime).1 h12 with h | h
        · exact h
        · exact absurd h (hpq s (Or.inl hs))
      · have h12 : p ∣ Nat.card (perfectCore (fixedSubgroup θ₂)) * s := by
          rw [hX]
          refine Dvd.dvd.mul_left ?_ _
          have he4 : Even 4 := ⟨2, rfl⟩
          refine (show p ∣ unitaryFactor (2 ^ a) 4 by
            simpa only [unitaryFactor, he4, ↓reduceIte] using hp4).trans
              (Finset.dvd_prod_of_mem (fun j => unitaryFactor (2 ^ a) j) h4mem)
        rcases (Nat.Prime.dvd_mul hp.prime).1 h12 with h | h
        · exact h
        · exact absurd h (hpq s (Or.inr hs))
    have hp2 := (hpX.trans (Subgroup.card_dvd_of_le (CFSG.Quasithin.perfectCore_le _))).trans hC
    rcases (Nat.Prime.dvd_mul hp.prime).1 hp2 with h | h
    · exact ppd_not_dvd_two_mul hp (by omega) (by omega) _ h
    · refine ppd_not_dvd_prod_odd hp (by omega) (fun i hi => ?_) h
      obtain ⟨c, hc⟩ := hi
      have : 2 * c = 2 * i + 1 := by
        have h8 : f * (2 * c) = f * (2 * i + 1) := by rw [hc]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) h8
      omega

end GraphOdd

section GraphFour

open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical (radicalGroup)

variable {K : Type} [Field K] [Finite K]

theorem two_pow_dvd_card_perfectCore_graph_four (hK : Nat.card K = 2 ^ 2) (C : GL (Fin 4) K)
    (hC1 : (C : Matrix (Fin 4) (Fin 4) K) = 1) :
    2 ^ 8 ∣ Nat.card (perfectCore (fixedSubgroup (conjAut 4 K C * dualAut 4 K))) := by
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv
    (by norm_num : 1 ≤ 2) hK (by norm_num) C (Or.inl hC1)
  have hMO : radicalGroup (K := K) (Fin.last 3) ⊔ isometryThreeImage K ≤
      matrixIsometryGroup (C : Matrix (Fin 4) (Fin 4) K) := by
    rw [hC1]
    exact radicalGroup_sup_le
  exact (two_pow_dvd_card_radicalGroup_sup hK).trans
    (card_dvd_card_perfectCore_of_mulEquiv E hMO (commutator_radicalGroup_sup hK))

theorem graphFourPairExclusion {n f : ℕ} (hK : Nat.card K = 2 ^ f) :
    GraphFourPairExclusion n f K := by
  intro hn4 hf2 A θ₂ hθ₁ hF hC2 hC3
  subst hn4 hf2
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨C, hC, hcard, hcore⟩ := card_fixedSubgroup_graph_eq (by norm_num : 1 ≤ 2) hK
    (by norm_num) A hθ₁
  have hX : (Nat.card (perfectCore (fixedSubgroup θ₂)) = 20160) ∨
      (∃ s, s ∣ 3 ∧ Nat.card (perfectCore (fixedSubgroup θ₂)) * s = 25920) := by
    rcases fieldTypeCore_normal_form (a := 1) (by norm_num) hF with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
    · left
      have hs1 : s = 1 := Nat.dvd_one.1 (by simpa using hs)
      rw [hs1, mul_one] at h
      rw [h]
      decide
    · right
      refine ⟨s, by simpa using hs, ?_⟩
      rw [h]
      decide
  have hXC : Nat.card (perfectCore (fixedSubgroup θ₂)) ∣ Nat.card (fixedSubgroup θ₂) :=
    Subgroup.card_dvd_of_le (CFSG.Quasithin.perfectCore_le _)
  rcases hC with hC1 | ⟨r, hr, hJ⟩
  ·
    have h28 := two_pow_dvd_card_perfectCore_graph_four hK C hC1
    rw [← hcore] at h28
    have h26 : 2 ^ 6 ∣ Nat.card (perfectCore (fixedSubgroup θ₂)) := by
      rcases hX with h | ⟨s, hs, h⟩
      · rw [h]; decide
      · have hs3 : s = 1 ∨ s = 3 := by
          have := Nat.le_of_dvd (by norm_num) hs
          interval_cases s <;> simp_all
        rcases hs3 with rfl | rfl
        · rw [mul_one] at h; rw [h]; decide
        · have h' : Nat.card (perfectCore (fixedSubgroup θ₂)) = 8640 := by omega
          rw [h']; decide
    have h214 := (mul_dvd_mul h28 h26).trans hC3
    have hP : Nat.card (projectiveSL 4 K) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) :=
      Subgroup.card_quotient_dvd_card _
    rw [card_SL_eq (by norm_num), hK] at hP
    have h := h214.trans hP
    revert h
    decide
  ·
    have hr2 : r = 2 := by omega
    subst hr2
    rw [hcard, hJ, card_matrixIsometryGroup_blockSwapJ hr, SymplecticFlag.card_statedSp, hK]
      at hC2
    have hA := card_mulAut_projectiveSL_dvd (K := K) (n := 4) (by norm_num) hK
    rw [card_GL_eq, hK] at hA
    have h := (mul_dvd_mul_left _ hXC).trans (hC2.trans hA)
    rcases hX with hX | ⟨s, hs, hX⟩
    · rw [hX] at h
      revert h
      decide
    · have hs3 : s = 1 ∨ s = 3 := by
        have := Nat.le_of_dvd (by norm_num) hs
        interval_cases s <;> simp_all
      rcases hs3 with rfl | rfl
      · rw [mul_one] at hX
        rw [hX] at h
        revert h
        decide
      · have h' : Nat.card (perfectCore (fixedSubgroup θ₂)) = 8640 := by omega
        rw [h'] at h
        revert h
        decide

end GraphFour

theorem linearInvolutionPairExclusion_holds {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    LinearInvolutionPairExclusion n K :=
  linearInvolutionPairExclusion_of_residuals hn hf hK (fieldTypePairExclusion hn hK)
    (graphOddPairExclusion hn hf hK) (graphFourPairExclusion hK)

theorem linearSwapFactorNormalInput_holds : LinearSwapFactorNormalInput :=
  linearSwapFactorNormalInput_of_pairExclusion fun _ _ _ _ _ _ hm hK hf =>
    linearInvolutionPairExclusion_holds (by omega) hf hK

end CFSG.SeitzReduction.LinearPilot
