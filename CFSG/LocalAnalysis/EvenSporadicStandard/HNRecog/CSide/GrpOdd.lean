module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoFacts

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog

theorem cSide_mem_commutator_of_odd {w : A5WrTwo} (hw : Odd (orderOf w)) :
    w ∈ commutator A5WrTwo := by
  rw [A5WrTwo.commutator_eq_ker]
  refine MonoidHom.mem_ker.mpr ?_
  set r := RegularWreathProduct.rightHom w with hr
  have hdvd : orderOf r ∣ orderOf w := by
    rw [hr]
    exact orderOf_map_dvd
      (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)) w
  have hdvd2 : orderOf r ∣ 2 := by
    have h := orderOf_dvd_natCard r
    rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
  have h1 : orderOf r = 1 := by
    have h : orderOf r ∣ Nat.gcd (orderOf w) 2 := Nat.dvd_gcd hdvd hdvd2
    rw [hw.coprime_two_right.gcd_eq_one] at h
    exact Nat.dvd_one.mp h
  exact orderOf_eq_one_iff.mp h1

theorem cSide_orderOf_mk_of_odd {C : Type*} [Group C] {Q : Subgroup C} [Q.Normal]
    (hQ : IsPGroup 2 Q) {σ : C} (hσ : Odd (orderOf σ)) : orderOf (σ : C ⧸ Q) = orderOf σ := by
  refine Nat.dvd_antisymm ?_ ?_
  · simpa using orderOf_map_dvd (QuotientGroup.mk' Q) σ
  · set m := orderOf (σ : C ⧸ Q) with hm
    have hmem : σ ^ m ∈ Q := by
      rw [← QuotientGroup.eq_one_iff (σ ^ m), QuotientGroup.mk_pow, hm]
      exact pow_orderOf_eq_one _
    obtain ⟨k, hk⟩ := hQ ⟨σ ^ m, hmem⟩
    have hk' : (σ ^ m) ^ 2 ^ k = 1 := by
      simpa using congrArg (fun x : Q => (x : C)) hk
    have hdvd : orderOf σ ∣ m * 2 ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
      exact hk'
    exact (hσ.coprime_two_right.pow_right k).dvd_of_dvd_mul_right hdvd

private lemma cSide_eq_mul_prime_pow_of_dvd {n m k : ℕ} (hn : 0 < n) (h : n ∣ m)
    (hm : m ∣ n * 2 ^ k) : ∃ j ≤ k, m = n * 2 ^ j := by
  obtain ⟨d, rfl⟩ := h
  have hd : d ∣ 2 ^ k := (Nat.mul_dvd_mul_iff_left hn).mp hm
  obtain ⟨j, hjle, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨j, hjle, by rw [hdj]⟩

theorem cSide_exists_lift_of_odd {C : Type*} [Group C] [Finite C] {Q : Subgroup C} [Q.Normal]
    (hQ : IsPGroup 2 Q) {r : C ⧸ Q} (hr : Odd (orderOf r)) :
    ∃ σ : C, orderOf σ = orderOf r ∧ (σ : C ⧸ Q) = r := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (N := Q) r
  have hc' : (c : C ⧸ Q) = r := hc
  generalize hn : orderOf r = n at hr ⊢
  have hnpos : 0 < n := by
    rw [← hn]
    exact (isOfFinOrder_of_finite r).orderOf_pos
  have hndvd : n ∣ orderOf c := by
    rw [← hn, ← hc']
    exact orderOf_map_dvd (QuotientGroup.mk' Q) c
  have hmem : c ^ n ∈ Q := by
    rw [← QuotientGroup.eq_one_iff (c ^ n), QuotientGroup.mk_pow, ← hn, hc']
    exact pow_orderOf_eq_one r
  obtain ⟨k, hk⟩ := hQ ⟨c ^ n, hmem⟩
  have hk' : (c ^ n) ^ 2 ^ k = 1 := by
    simpa using congrArg (fun x : Q => (x : C)) hk
  have hdvd : orderOf c ∣ n * 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
    exact hk'
  obtain ⟨j, -, hj⟩ := cSide_eq_mul_prime_pow_of_dvd hnpos hndvd hdvd
  rcases lt_or_eq_of_le (show 1 ≤ n from hnpos) with hn_gt | hn_eq
  · have hcop : (2 ^ j).Coprime n := (hr.coprime_two_right.pow_right j).symm
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn_gt
    have himg : ((c ^ (2 ^ j * u) : C) : C ⧸ Q) = r := by
      rw [QuotientGroup.mk_pow, hc', ← pow_mod_orderOf r (2 ^ j * u)]
      rw [show 2 ^ j * u % orderOf r = 1 by rw [hn]; exact hu, pow_one]
    refine ⟨c ^ (2 ^ j * u), ?_, himg⟩
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul]
      rw [show 2 ^ j * u * n = (n * 2 ^ j) * u by
        rw [Nat.mul_comm (2 ^ j * u) n, Nat.mul_assoc]]
      rw [pow_mul, show c ^ (n * 2 ^ j) = 1 by rw [← hj]; exact pow_orderOf_eq_one c,
        one_pow]
    · rw [← hn, ← himg]
      exact orderOf_map_dvd (QuotientGroup.mk' Q) (c ^ (2 ^ j * u))
  · have hr1 : r = 1 := orderOf_eq_one_iff.mp (hn.trans hn_eq.symm)
    exact ⟨1, by rw [orderOf_one]; exact hn_eq, by rw [hr1]; rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
