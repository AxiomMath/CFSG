module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74A3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73C

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.LieType.HighestRoot
open scoped MatrixGroups

section OddIndex

variable {C : Type*} [Group C] {N : Subgroup C} [N.Normal]

theorem mem_of_conj_eq_inv_of_odd_index (hN : ¬ 2 ∣ N.index) {g x : C}
    (h : g * x * g⁻¹ = x⁻¹) : x ∈ N := by
  obtain ⟨a, ha⟩ : ∃ a : C ⧸ N, a = QuotientGroup.mk' N g := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : C ⧸ N, b = QuotientGroup.mk' N x := ⟨_, rfl⟩
  have hab : a * b * a⁻¹ = b⁻¹ := by
    rw [ha, hb, ← map_inv, ← map_mul, ← map_mul, h, map_inv]
  have e1 : a * b = b⁻¹ * a := by
    rw [← hab]
    group
  have e2 : a * b⁻¹ = b * a := by
    have h1 : b = a * b⁻¹ * a⁻¹ := by
      calc b = (a * b * a⁻¹)⁻¹ := by rw [hab, inv_inv]
        _ = a * b⁻¹ * a⁻¹ := by group
    calc a * b⁻¹ = a * b⁻¹ * a⁻¹ * a := by group
      _ = b * a := by rw [← h1]
  have h2 : a ^ 2 * b = b * a ^ 2 := by
    calc a ^ 2 * b = a * (a * b) := by rw [pow_two, mul_assoc]
      _ = a * b⁻¹ * a := by rw [e1, mul_assoc]
      _ = b * a ^ 2 := by rw [e2, mul_assoc, ← pow_two]
  have hodd : Odd (orderOf a) := by
    have hd : orderOf a ∣ N.index := orderOf_dvd_natCard a
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => hN (h2.trans hd))
  obtain ⟨k, hk⟩ := hodd
  have hak : a = (a ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf a + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hcomm : a * b = b * a := by
    rw [hak]
    exact (Commute.pow_left h2 (k + 1)).eq
  have hbb : b = b⁻¹ := by
    calc b = a * b * a⁻¹ := by rw [hcomm, mul_inv_cancel_right]
      _ = b⁻¹ := hab
  have hb2 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [pow_two]
    calc b * b = b * b⁻¹ := by rw [← hbb]
      _ = 1 := mul_inv_cancel b)
  have hbd : orderOf b ∣ N.index := orderOf_dvd_natCard b
  have hb1 : orderOf b = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hb2 with h' | h'
    · exact h'
    · exact absurd (h' ▸ hbd) hN
  rw [orderOf_eq_one_iff, hb] at hb1
  exact (QuotientGroup.eq_one_iff x).mp hb1

theorem mem_of_mul_self_of_odd_index (hN : ¬ 2 ∣ N.index) {x : C} (hx : x * x = 1) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← map_mul, hx, map_one])
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · rw [orderOf_eq_one_iff] at h
    exact (QuotientGroup.eq_one_iff x).mp h
  · exact absurd (h ▸ h2) hN

end OddIndex

section SL2

variable {K : Type} [Field K] [Finite K]

theorem card_eq_three_or_five_le (hodd : Odd (Nat.card K)) : Nat.card K = 3 ∨ 5 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨k, hk⟩ := hodd
  omega

omit [Finite K] in
theorem upperSL2_one_not_mem_center : upperSL2 (1 : K) ∉ center SL(2, K) := by
  intro h
  have h1 := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 1 1)
    (mem_center_iff.mp h (lowerSL2 1))
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_upperSL2, coe_lowerSL2] at h1

omit [Finite K] in
theorem upperSL2_neg_one : upperSL2 (-1 : K) = (upperSL2 1)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← upperSL2_add, neg_add_cancel, upperSL2_zero])

theorem eq_top_of_upperSL2_one_mem {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {N : Subgroup SL(2, K)} [N.Normal] (h : upperSL2 (1 : K) ∈ N) :
    N = ⊤ := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  rcases card_eq_three_or_five_le hodd with h3 | h5
  · have hchar : (3 : K) = 0 := by
      classical
      have : Fintype K := Fintype.ofFinite K
      have h0 := FiniteField.cast_card_eq_zero K
      rw [← Nat.card_eq_fintype_card, h3] at h0
      exact_mod_cast h0
    refine normal_eq_top_of_mem_sl23 (slEquivSL23 h3) inferInstance h ?_ ?_
    · have e : upperSL2 (1 : K) ^ 3 = upperSL2 (1 + 1 + 1) := by
        rw [upperSL2_add, upperSL2_add, pow_succ, pow_two]
      rw [e, show (1 : K) + 1 + 1 = 3 by norm_num, hchar, upperSL2_zero]
    · intro h1
      have h01 := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h1
      simp [coe_upperSL2] at h01
  · have h5' : 5 ≤ p ^ f := hK ▸ h5
    have hSL : IsSLTwoOver (p ^ f) SL(2, K) := by
      let _ := Fintype.ofFinite K
      exact ⟨K, inferInstance, inferInstance, by rw [Fintype.card_eq_nat_card, hK],
        ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hq, -, -⟩ := sl2_facts_spin hp hp2 h5' hSL
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq N with hc | ht
    · exact absurd (hc h) upperSL2_one_not_mem_center
    · exact ht

end SL2

section Torus

variable (K : Type) [Field K]

noncomputable abbrev torusZeroTwo : spinGroup (quadOdd 3 K) :=
  (oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true (-1)

variable {K}

theorem torusZeroTwo_conj_shortSeven :
    torusZeroTwo K * shortSeven K (upperSL2 1) * (torusZeroTwo K)⁻¹ =
      (shortSeven K (upperSL2 1))⁻¹ := by
  have he : longCoroot (0 : Fin 3) 2 true true 2 true = 1 := by decide
  rw [show (shortSeven K (upperSL2 1))⁻¹ = shortSeven K (upperSL2 (-1)) by
      rw [upperSL2_neg_one, map_inv],
    OddFrame.shortSL2_upperSL2, OddFrame.shortSL2_upperSL2, OddFrame.longTorus_conj_shortRoot,
    he, zpow_one, Units.val_neg, Units.val_one, mul_one]

theorem torusZeroTwo_conj_longSL2_true :
    torusZeroTwo K * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 1) *
        (torusZeroTwo K)⁻¹ =
      ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 1))⁻¹ := by
  have he : longCoroot (0 : Fin 3) 2 true true 0 true + longCoroot (0 : Fin 3) 2 true true 1 true =
      1 := by decide
  rw [show ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 1))⁻¹ =
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 (-1)) by
      rw [upperSL2_neg_one, map_inv],
    HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2, HypFrame.longTorus_conj_longRoot, he,
    zpow_one, Units.val_neg, Units.val_one, mul_one]

theorem torusZeroTwo_conj_longSL2_false :
    torusZeroTwo K * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (upperSL2 1) *
        (torusZeroTwo K)⁻¹ =
      ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (upperSL2 1))⁻¹ := by
  have he : longCoroot (0 : Fin 3) 2 true true 0 true +
      longCoroot (0 : Fin 3) 2 true true 1 false = 1 := by decide
  rw [show ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (upperSL2 1))⁻¹ =
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (upperSL2 (-1)) by
      rw [upperSL2_neg_one, map_inv],
    HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2, HypFrame.longTorus_conj_longRoot, he,
    zpow_one, Units.val_neg, Units.val_one, mul_one]

end Torus

section Normal

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f)
include hp hp2 hK

theorem eq_top_of_normal_of_odd_index
    {N : Subgroup ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))} [N.Normal]
    (hN : ¬ 2 ∣ N.index) : N = ⊤ := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  have hg₀ := longTorus_zero_two_mem_centralizer K (-1)
  have key : ∀ ρ : SL(2, K) →* spinGroup (quadOdd 3 K),
      ∀ hρ : ρ.range ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))),
      torusZeroTwo K * ρ (upperSL2 1) * (torusZeroTwo K)⁻¹ = (ρ (upperSL2 1))⁻¹ →
      ∀ M, (⟨ρ M, hρ ⟨M, rfl⟩⟩ : ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))) ∈
        N := by
    intro ρ hρ hinv
    set ρ' := ρ.codRestrict _ (fun M => hρ ⟨M, rfl⟩) with hρ'
    have hu : ρ' (upperSL2 1) ∈ N := by
      refine mem_of_conj_eq_inv_of_odd_index hN (g := ⟨torusZeroTwo K, hg₀⟩) ?_
      apply Subtype.ext
      exact hinv
    have htop : N.comap ρ' = ⊤ := eq_top_of_upperSL2_one_mem hp hp2 hK hu
    intro M
    have hM : M ∈ N.comap ρ' := htop ▸ mem_top M
    exact hM
  have hEN : (spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) ≤
      N := by
    rw [subgroupOf_sup (sup_le l1 l2) l3, subgroupOf_sup l1 l2]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      obtain ⟨M, hM⟩ := mem_subgroupOf.mp hx
      rw [show x = ⟨shortSeven K M, l1 ⟨M, rfl⟩⟩ from Subtype.ext hM.symm]
      exact key _ l1 torusZeroTwo_conj_shortSeven M
    · intro x hx
      obtain ⟨M, hM⟩ := mem_subgroupOf.mp hx
      rw [show x = ⟨_, l2 ⟨M, rfl⟩⟩ from Subtype.ext hM.symm]
      exact key _ l2 torusZeroTwo_conj_longSL2_true M
    · intro x hx
      obtain ⟨M, hM⟩ := mem_subgroupOf.mp hx
      rw [show x = ⟨_, l3 ⟨M, rfl⟩⟩ from Subtype.ext hM.symm]
      exact key _ l3 torusZeroTwo_conj_longSL2_false M
  obtain ⟨ν, hν0, hνs⟩ := exists_nonsquare_spin hp hp2 hK
  have hτC := spinTau_mem_centralizer ν hν0
  set τ : ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) := ⟨spinTau ν hν0, hτC⟩
    with hτ
  have hτE : τ ∉ (spinE K).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :=
    fun h => spinNormC_spinTau_ne_one ν hν0 hνs hτC (spinE_le_ker_spinNormC_odd hp hp2 hK h)
  have hτN : τ ∈ N := mem_of_mul_self_of_odd_index hN (Subtype.ext (spinTau_mul_self ν hν0))
  have hidx := index_spinE_eq_two_odd hp hp2 hK
  rw [eq_top_iff]
  intro c _
  by_cases hc : c ∈ (spinE K).subgroupOf
    (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))
  · exact hEN hc
  · have hcτ := hEN ((mul_mem_iff_of_index_two hidx).mpr (iff_of_false hc hτE))
    have h' := mul_mem hcτ (inv_mem hτN)
    rwa [mul_inv_cancel_right] at h'

theorem eq_spinJ_of_normal_of_mulEquiv {P J : Subgroup (spinGroup (quadOdd 3 K))}
    (hPC : P ≤ centralizer {tSeven K}) (hPn : (P.subgroupOf (centralizer {tSeven K})).Normal)
    (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) (e : ↥P ≃* ↥J) :
    P = spinJ₁ K ∨ P = spinJ₂ K ∨ P = spinJ₃ K := by
  have hodd : Odd (Nat.card K) := odd_card_spin hp hp2 hK
  obtain ⟨⟨eJ⟩, hOJ⟩ : Nonempty (↥J ≃* SL(2, K)) ∧ pPrimeCore 2 ↥J = ⊥ := by
    obtain ⟨o1, o2, o3⟩ := pPrimeCore_spinJ_odd (K := K) hp hp2 hK
    rcases hJ with rfl | rfl | rfl
    · exact ⟨⟨(MonoidHom.ofInjective injective_shortSeven).symm⟩, o1⟩
    · exact ⟨⟨(MonoidHom.ofInjective (longSL2_injective _ fin3_zero_ne_one true true)).symm⟩, o2⟩
    · exact ⟨⟨(MonoidHom.ofInjective (longSL2_injective _ fin3_zero_ne_one true false)).symm⟩,
        o3⟩
  have hOP : pPrimeCore 2 ↥P = ⊥ := by
    have h := pPrimeCore_map_iso 2 e
    rw [hOJ] at h
    exact (map_eq_bot_iff_of_injective _ e.injective).mp h
  rcases card_eq_three_or_five_le hodd with h3 | h5
  · refine eq_spinJ_of_isSolvableTwoComponentIn_three h3
      ⟨hPC, hPn.isSubnormal, ?_, Or.inr ⟨?_⟩⟩
    · rw [hOP, pPrimeCore_centralizer_tSeven_odd hp hp2 hK, Subgroup.map_bot, Subgroup.map_bot]
    · exact ((QuotientGroup.quotientMulEquivOfEq hOP).trans QuotientGroup.quotientBot).trans
        ((e.trans eJ).trans (slEquivSL23 h3))
  · have h5' : 5 ≤ p ^ f := hK ▸ h5
    obtain ⟨-, -, -, hO, hq⟩ := spinJ_props hp hp2 hK h5' hJ
    have hJq : IsTwoQuasisimple ↥J := ⟨hq.1, LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩
    exact eq_spinJ_of_isTwoComponentIn hp hp2 hK h5' ⟨hPC, hPn.isSubnormal,
      isTwoQuasisimple_of_mulEquiv e.symm hJq⟩

end Normal

end CFSG.ComponentClassification.HarrisLit.T1.S74
