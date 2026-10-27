module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3SL4
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

namespace ThreeNineHyp

theorem D_le_K_of_inner_of_coprime (h : ThreeNineHyp K E D X₁ p d)
    (hZ : Nat.Coprime (Nat.card (Subgroup.center ↥K)) d)
    (hinn : ∀ x ∈ D, ∃ k ∈ K, ∀ c ∈ K, x * c * x⁻¹ = k * c * k⁻¹) : D ≤ K := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  intro x hxD
  obtain ⟨k₀, hk₀K, hk₀⟩ := hinn x hxD
  set C : Subgroup X := Subgroup.centralizer (K : Set X)
  obtain ⟨a, ha⟩ := h.isPGroup_D ⟨x, hxD⟩
  have hxa : x ^ d ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hy₀C : k₀⁻¹ * x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 := hk₀ c hc
    calc c * (k₀⁻¹ * x) = k₀⁻¹ * (k₀ * c * k₀⁻¹) * x := by group
      _ = k₀⁻¹ * (x * c * x⁻¹) * x := by rw [h1]
      _ = k₀⁻¹ * x * c := by group
  have hcomm₀ : Commute k₀ (k₀⁻¹ * x) := Subgroup.mem_centralizer_iff.mp hy₀C k₀ hk₀K
  have hpow₀ : k₀ ^ d ^ a * (k₀⁻¹ * x) ^ d ^ a = 1 := by
    rw [← hcomm₀.mul_pow, mul_inv_cancel_left, hxa]
  have hk₀C : k₀ ^ d ^ a ∈ C := by
    have : k₀ ^ d ^ a = ((k₀⁻¹ * x) ^ d ^ a)⁻¹ := eq_inv_of_mul_eq_one_left hpow₀
    rw [this]
    exact C.inv_mem (C.pow_mem hy₀C _)
  have hzZ : (⟨k₀ ^ d ^ a, K.pow_mem hk₀K _⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hk₀C c c.2)
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥K)) (d ^ a) := Nat.Coprime.pow_right a hZ
  obtain ⟨w, hw⟩ := (Nat.Coprime.pow_left_bijective hcop).2 ⟨_, hzZ⟩
  have hwpow : ((w : ↥K) : X) ^ d ^ a = k₀ ^ d ^ a := by
    have h1 := congrArg (fun u : Subgroup.center ↥K => ((u : ↥K) : X)) hw
    simpa only [SubgroupClass.coe_pow] using h1
  have hwc : ∀ c ∈ K, ((w : ↥K) : X) * c = c * ((w : ↥K) : X) := by
    intro c hc
    have h1 := Subgroup.mem_center_iff.mp w.2 ⟨c, hc⟩
    exact (congrArg Subtype.val h1).symm
  set k : X := k₀ * ((w : ↥K) : X)⁻¹ with hkdef
  have hkK : k ∈ K := K.mul_mem hk₀K (K.inv_mem (w : ↥K).2)
  have hk : ∀ c ∈ K, x * c * x⁻¹ = k * c * k⁻¹ := by
    intro c hc
    have hwc' : ((w : ↥K) : X)⁻¹ * c = c * ((w : ↥K) : X)⁻¹ := by
      have h1 := hwc c hc
      calc ((w : ↥K) : X)⁻¹ * c
          = ((w : ↥K) : X)⁻¹ * (c * ((w : ↥K) : X)) * ((w : ↥K) : X)⁻¹ := by group
        _ = ((w : ↥K) : X)⁻¹ * (((w : ↥K) : X) * c) * ((w : ↥K) : X)⁻¹ := by rw [h1]
        _ = c * ((w : ↥K) : X)⁻¹ := by group
    rw [hk₀ c hc]
    calc k₀ * c * k₀⁻¹ = k₀ * (c * ((w : ↥K) : X)⁻¹) * ((w : ↥K) : X) * k₀⁻¹ := by group
      _ = k₀ * (((w : ↥K) : X)⁻¹ * c) * ((w : ↥K) : X) * k₀⁻¹ := by rw [hwc']
      _ = k * c * k⁻¹ := by rw [hkdef]; group
  have hkpow : k ^ d ^ a = 1 := by
    have hcw : Commute k₀ ((w : ↥K) : X) := (hwc k₀ hk₀K).symm
    rw [hkdef, hcw.inv_right.mul_pow, inv_pow, hwpow, mul_inv_cancel]
  have hyC : k⁻¹ * x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 := hk c hc
    calc c * (k⁻¹ * x) = k⁻¹ * (k * c * k⁻¹) * x := by group
      _ = k⁻¹ * (x * c * x⁻¹) * x := by rw [h1]
      _ = k⁻¹ * x * c := by group
  have hcomm : Commute k (k⁻¹ * x) := Subgroup.mem_centralizer_iff.mp hyC k hkK
  have hy1 : (k⁻¹ * x) ^ d ^ a = 1 := by
    have hpow : k ^ d ^ a * (k⁻¹ * x) ^ d ^ a = 1 := by
      rw [← hcomm.mul_pow, mul_inv_cancel_left, hxa]
    rwa [hkpow, one_mul] at hpow
  have hsylC : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ C) C :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : C.Normal)])
  have hcardC : ¬ d ∣ Nat.card C := by
    intro hdvd
    have hc := hsylC.card_eq
    rw [h.D_faithful, Subgroup.card_bot] at hc
    have hpos : 0 < (Nat.card C).factorization d :=
      (Nat.Prime.factorization_pos_of_dvd h.d_prime Nat.card_pos.ne' hdvd)
    have : 1 < d ^ (Nat.card C).factorization d :=
      Nat.one_lt_pow hpos.ne' h.d_prime.one_lt
    omega
  have hord : orderOf (⟨k⁻¹ * x, hyC⟩ : C) ∣ d ^ a :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy1))
  obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow h.d_prime).1 hord
  have hy : k⁻¹ * x = 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [pow_zero, orderOf_eq_one_iff] at hio
      exact congrArg Subtype.val hio
    · exfalso
      apply hcardC
      have hdo : d ∣ orderOf (⟨k⁻¹ * x, hyC⟩ : C) := by
        rw [hio]
        exact dvd_pow_self d hipos.ne'
      exact hdo.trans (orderOf_dvd_natCard _)
  have hxk : x = k := by
    calc x = k * (k⁻¹ * x) := by group
      _ = k := by rw [hy, mul_one]
  rw [hxk]
  exact hkK

end ThreeNineHyp

theorem false_of_threeNineHyp_A6Hat (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : IsTripleCover ↥K (alternatingGroup (Fin 6))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  have hperf : Group.IsPerfect ↥K := h.quasisimple.1
  have hcardK : Nat.card ↥K = 1080 :=
    CFSG.RankThree.PartTwo.Sec14.HJRes2.card_of_isTripleCover_six hK
  obtain ⟨hZ3, ⟨eZ⟩⟩ := hK
  have hodd : CFSG.ComponentClassification.HarrisLit.T1.P58b3.OddAutInner ↥K := by
    refine CFSG.ComponentClassification.HarrisLit.T1.P58b3.oddAutInner_of_card_outer_dvd hperf
      (m := 2) ?_
    rw [CFSG.Sporadic.SteinbergBI.card_outer_eq_of_mulEquiv eZ]
    exact CFSG.AGLEmbedding.card_outer_alternatingGroup_six_dvd_four
  have hinn : ∀ x ∈ D, ∃ k ∈ K, ∀ c ∈ K, x * c * x⁻¹ = k * c * k⁻¹ := by
    intro x hxD
    obtain ⟨a, ha⟩ := h.isPGroup_D ⟨x, hxD⟩
    have hxa : x ^ d ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    set α : MulAut ↥K := MulAut.conjNormal x
    have hα : α ^ d ^ a ∈ (MulAut.conj : ↥K →* MulAut ↥K).range :=
      ⟨1, by rw [map_one, ← map_pow, hxa, map_one]⟩
    obtain ⟨k, hk⟩ := hodd α (d ^ a) ((h.d_prime.odd_of_ne_two h.d_ne_two).pow) hα
    refine ⟨k, k.2, fun c hc => ?_⟩
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨c, hc⟩ : ↥K) : X)) hk
    simp only [MulAut.conj_apply, α, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    exact h1.symm
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥K)) d := by
    rw [hZ3]
    exact (Nat.coprime_primes Nat.prime_three h.d_prime).mpr (Ne.symm h.d_ne)
  have hDK : D ≤ K := h.D_le_K_of_inner_of_coprime hcop hinn
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  rw [inf_eq_left.mpr hDK] at hDsylK
  have hDcard := hDsylK.card_eq
  rw [hcardK] at hDcard
  have hdK : d ∣ 1080 := by
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hDcard
    exact h.D_ne_bot (Subgroup.card_eq_one.mp hDcard)
  have hd5 : d = 5 := by
    have hfac : (1080 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp h1
  subst hd5
  have hDd : Nat.card D = 5 := by
    rw [hDcard]
    have h1 : (5 : ℕ) ^ (1080 : ℕ).factorization 5 = 5 ^ 1 :=
      (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 5) (a := 1)
        (k := 216) (by norm_num) (by norm_num)).symm
    rw [h1, pow_one]
  set Y : Subgroup ↥K := X₁.subgroupOf K
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ Y := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨Q, hEQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elem).exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup X) ⊓ K) K := by
    have hQ : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup X) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, Q.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact Q.not_dvd_index
    exact hQ.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  let T : Sylow 3 ↥K := Sylow.ofCard (((Q : Subgroup X) ⊓ K).subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hQsyl.card_eq)
  have hTcard : Nat.card (T : Subgroup ↥K) = 27 := by
    have h3 : (3 : ℕ) ^ (1080 : ℕ).factorization 3 = 3 ^ 3 :=
      (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 3)
        (k := 40) (by norm_num) (by norm_num)).symm
    rw [Sylow.card_eq_multiplicity, hcardK, h3]
    norm_num
  have hTY : (T : Subgroup ↥K) ≤ Y := fun x hx => h.inf_K_le Q.isPGroup' hEQ hx
  have hDY : D.subgroupOf K ≤ Y := fun x hx => h.D_le hx
  have hDKc : Nat.card (D.subgroupOf K) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDd]
  let SD : Sylow 5 ↥K := Sylow.ofCard (D.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDcard, hcardK])
  have hN : Subgroup.normalizer ((SD : Subgroup ↥K) : Set ↥K) ≤ Y := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
    rw [← Subgroup.subgroupOf_normalizer_eq hDK] at hn'
    exact h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot ⟨hn', le_sup_left (a := K) n.2⟩
  have hmod := index_modEq_one_of_normalizer_le SD hN
  have h27 : 27 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hTY
    rwa [hTcard] at this
  have h5Y : 5 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hDY
    rwa [hDKc] at this
  have h135 : 135 ∣ Nat.card Y :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 5) h27 h5Y
  have hidx := index_dvd_div_of_dvd_card h135
  rw [hcardK] at hidx
  have key : ∀ m ∈ Nat.divisors 8, m ≡ 1 [MOD 5] → m = 1 := by decide
  exact hYtop (Subgroup.index_eq_one.mp
    (key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) hmod))

theorem threeNineThreeA6Hat_holds : ThreeNineThreeA6Hat :=
  fun _ _ _ _ _ _ _ _ h hK => false_of_threeNineHyp_A6Hat h hK

end CFSG.LocalAnalysis.AGL81I.Section3
