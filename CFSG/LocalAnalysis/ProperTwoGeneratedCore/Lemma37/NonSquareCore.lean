module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCentral

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC

theorem exists_orderOf_pow_eq_four {X : Type*} [Group X] {x : X} {k : ℕ}
    (hk : orderOf x = 2 ^ k) (hx : x ^ 2 ≠ 1) : ∃ n : ℕ, orderOf (x ^ n) = 4 := by
  rcases k with _ | _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact absurd (by rw [hk, one_pow]) hx
  · exact absurd (by simpa [hk] using pow_orderOf_eq_one x) hx
  · refine ⟨2 ^ k, ?_⟩
    have hdvd : 2 ^ k ∣ orderOf x := hk ▸ pow_dvd_pow 2 (by omega)
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk, pow_add, pow_add, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (by positivity)]
    norm_num

variable {K : Type*} [Group K] [Finite K]

theorem mem_center_of_borelFacts (hperf : commutator K = ⊤) {u : K} (hu : orderOf u = 2)
    (hZ : ∀ s : K, s ∈ Subgroup.center K ↔ s = 1 ∨ s = u) (Q : Sylow 2 K)
    (hBF : BenderBorelFacts (K ⧸ Subgroup.center K) (BenderCover.centralImage (Q : Subgroup K)))
    {w : K} (hwQ : w ∈ (Q : Subgroup K)) (hwc : ∀ q ∈ (Q : Subgroup K), Commute q w) :
    w ∈ Subgroup.center K := by
  by_contra hw
  have hZ2 : IsPGroup 2 (Subgroup.center K) := fun s => ⟨1, Subtype.ext (by
    rcases (hZ s).mp s.2 with h | h
    · rw [Subgroup.coe_pow, h, one_pow, Subgroup.coe_one]
    · rw [Subgroup.coe_pow, h, pow_one, ← hu, pow_orderOf_eq_one, Subgroup.coe_one])⟩
  have hbot := BenderCover.center_eq_bot_of_borelFacts hperf hZ2 (fun s hs _ => (hZ s).mp hs) Q
    hBF hwQ hwc hw
  have huZ := (hZ u).mpr (Or.inr rfl)
  rw [hbot, Subgroup.mem_bot] at huZ
  rw [huZ, orderOf_one] at hu
  exact absurd hu (by norm_num)

theorem exists_sq_conj_eq_mul_of_borelFacts (hperf : commutator K = ⊤) {u : K}
    (hu : orderOf u = 2) (hZ : ∀ s : K, s ∈ Subgroup.center K ↔ s = 1 ∨ s = u) (Q : Sylow 2 K)
    (hBF : BenderBorelFacts (K ⧸ Subgroup.center K) (BenderCover.centralImage (Q : Subgroup K)))
    (hsq : ∀ y ∈ (Q : Subgroup K), y ^ 2 ≠ u) (hQ : ¬ (Q : Subgroup K) ≤ Subgroup.center K) :
    ∃ y ∈ (Q : Subgroup K), orderOf (y ^ 2) = 2 ∧
      ∃ q ∈ (Q : Subgroup K), q⁻¹ * y ^ 2 * q = y ^ 2 * u := by
  have hcen : ∀ w ∈ (Q : Subgroup K), (∀ q ∈ (Q : Subgroup K), Commute q w) →
      w ∈ Subgroup.center K := fun w hw hwc => mem_center_of_borelFacts hperf hu hZ Q hBF hw hwc
  obtain ⟨x, hxQ, hx⟩ : ∃ x ∈ (Q : Subgroup K), x ^ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    have hcomm := Commute.of_orderOf_dvd_two (G := (Q : Subgroup K)) fun g =>
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hall g g.2))
    exact hQ fun w hw => hcen w hw fun q hq => congrArg Subtype.val (hcomm ⟨q, hq⟩ ⟨w, hw⟩)
  obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hxQ⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one
    (show x ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk))
  obtain ⟨n, hn⟩ := exists_orderOf_pow_eq_four hj hx
  have hyQ : x ^ n ∈ (Q : Subgroup K) := Subgroup.pow_mem _ hxQ n
  have ht2 : orderOf ((x ^ n) ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hn]; norm_num), hn]
  have htZ : (x ^ n) ^ 2 ∉ Subgroup.center K := by
    intro h
    rcases (hZ _).mp h with h1 | h1
    · rw [h1, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    · exact hsq _ hyQ h1
  obtain ⟨q, hqQ, hqt⟩ : ∃ q ∈ (Q : Subgroup K), ¬ Commute q ((x ^ n) ^ 2) := by
    by_contra hall
    push Not at hall
    exact htZ (hcen _ (Subgroup.pow_mem _ hyQ 2) hall)
  have hc := ((hBF.sq_central _ (Subgroup.mem_map_of_mem _ hyQ)).2 _
    (Subgroup.mem_map_of_mem _ hqQ)).eq
  have hmem : q⁻¹ * (x ^ n) ^ 2 * q * ((x ^ n) ^ 2)⁻¹ ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
      pow_two]
    simp only [QuotientGroup.mk'_apply] at hc
    rw [mul_assoc _ _ (q : K ⧸ Subgroup.center K), ← hc]
    group
  rcases (hZ _).mp hmem with h | h
  · refine absurd ?_ hqt
    have h' := mul_inv_eq_one.mp h
    change q * (x ^ n) ^ 2 = (x ^ n) ^ 2 * q
    calc q * (x ^ n) ^ 2 = q * (q⁻¹ * (x ^ n) ^ 2 * q) := by rw [h']
      _ = (x ^ n) ^ 2 * q := by group
  · refine ⟨x ^ n, hyQ, ht2, q, hqQ, ?_⟩
    rw [mul_inv_eq_iff_eq_mul.mp h]
    exact (Subgroup.mem_center_iff.mp ((hZ u).mpr (Or.inr rfl)) _).symm

end CFSG.ProperTwoGeneratedCore.Lemma37
