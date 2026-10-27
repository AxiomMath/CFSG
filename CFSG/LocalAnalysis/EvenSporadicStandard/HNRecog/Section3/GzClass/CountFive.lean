module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private theorem commutator_eq_sq_of_conj {G : Type*} [Group G] {c q : G} (hc : c ^ 2 = 1)
    (h : c * q * c = q⁻¹) : ⁅q, c⁆ = q ^ 2 := by
  have hc' : c⁻¹ = c := by
    rw [pow_two] at hc
    exact inv_eq_of_mul_eq_one_left hc
  have h1 : c * q⁻¹ * c = q := by
    have := congrArg Inv.inv h
    simp only [mul_inv_rev, inv_inv, hc'] at this
    rw [mul_assoc]
    exact this
  rw [commutatorElement_def, hc']
  calc q * c * q⁻¹ * c = q * (c * q⁻¹ * c) := by group
    _ = q * q := by rw [h1]
    _ = q ^ 2 := by rw [pow_two]

private theorem pow_two_mem_centerOf_of_isPlusExtraspecial {K : Type*} [Group K]
    {Q : Subgroup K} (hQ : IsPlusExtraspecial 4 Q) {q : K} (hq : q ∈ Q) :
    q ^ 2 ∈ centerOf Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let qQ : ↥Q := ⟨q, hq⟩
  haveI : CFSG.IsElementaryAbelian 2 (↥Q ⧸ Subgroup.center ↥Q) :=
    hQ.1.quotient_elementary_abelian
  have hExp : Monoid.exponent (↥Q ⧸ Subgroup.center ↥Q) ∣ 2 :=
    CFSG.IsElementaryAbelian.exponent_dvd_p 2 (↥Q ⧸ Subgroup.center ↥Q)
  have hpow : ((qQ : ↥Q ⧸ Subgroup.center ↥Q)) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp (qQ : ↥Q ⧸ Subgroup.center ↥Q)
  have hq2center : qQ ^ 2 ∈ Subgroup.center ↥Q := by
    exact (QuotientGroup.eq_one_iff (qQ ^ 2)).mp (by
      rw [QuotientGroup.mk_pow]
      exact hpow)
  rw [centerOf, Subgroup.mem_inf]
  refine ⟨pow_mem hq 2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyQ : (⟨y, hy⟩ : ↥Q) * qQ ^ 2 = qQ ^ 2 * ⟨y, hy⟩ :=
    (Subgroup.mem_center_iff.mp hq2center) ⟨y, hy⟩
  have hcoe := congrArg (fun z : ↥Q => (z : K)) hyQ
  simpa [qQ, Subgroup.coe_pow] using hcoe

private theorem fiber_card_le {K : Type*} [Group K] [Finite K] (Q : Subgroup K) [Q.Normal]
    (hQ : IsPlusExtraspecial 4 Q) {c : K} (hc2 : c ^ 2 = 1) :
    Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)} ≤
      Nat.card {q : K // q ∈ Q ∧ ⁅q, c⁆ ∈ centerOf Q} := by
  let f : {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)} →
      {q : K // q ∈ Q ∧ ⁅q, c⁆ ∈ centerOf Q} := fun s => by
    have hqmem : c⁻¹ * s.1 ∈ Q := by
      have h : (s.1)⁻¹ * c ∈ Q := QuotientGroup.eq.mp s.2.2
      simpa [mul_inv_rev] using Q.inv_mem h
    refine ⟨c⁻¹ * s.1, ⟨hqmem, ?_⟩⟩
    have hs2 : s.1 ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := s.2.1
      rw [← hk, pow_two]
      calc k * c * k⁻¹ * (k * c * k⁻¹) = k * (c * c) * k⁻¹ := by group
        _ = 1 := by rw [pow_two] at hc2; rw [hc2]; group
    have hsq : (c * (c⁻¹ * s.1)) * (c * (c⁻¹ * s.1)) = 1 := by
      rw [mul_inv_cancel_left, ← pow_two, hs2]
    have hcqc : c * (c⁻¹ * s.1) * c = (c⁻¹ * s.1)⁻¹ := by
      have h : c * (c⁻¹ * s.1) * c * (c⁻¹ * s.1) = 1 := by
        rw [mul_assoc, hsq]
      exact eq_inv_of_mul_eq_one_left h
    rw [commutator_eq_sq_of_conj hc2 hcqc]
    exact pow_two_mem_centerOf_of_isPlusExtraspecial hQ hqmem
  refine Nat.card_le_card_of_injective f ?_
  intro a b hab
  have h : c⁻¹ * a.1 = c⁻¹ * b.1 := congrArg Subtype.val hab
  exact Subtype.ext (mul_left_cancel h)

theorem exists_orderOf_five_commute {K : Type*} [Group K] [Finite K] (Q : Subgroup K) [Q.Normal]
    (hQ : IsPlusExtraspecial 4 Q) {x : K} (hx2 : x ^ 2 = 1)
    (hC : Nat.card ↥(Subgroup.centralizer ({(x : K ⧸ Q)} : Set (K ⧸ Q))) = 240)
    (hW : Nat.card {q : K // q ∈ Q ∧ ⁅q, x⁆ ∈ centerOf Q} = 2 ^ 5) :
    ∃ ρ : K, orderOf ρ = 5 ∧ ρ * x = x * ρ := by
  have hQcard : Nat.card ↥Q = 2 ^ 9 := by
    have h := hQ.2.1
    rw [show 1 + 2 * 4 = 9 by norm_num] at h
    exact h
  have hFmul :
      Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧ (s : K ⧸ Q) = (x : K ⧸ Q)} *
        Nat.card ↥(Subgroup.centralizer ({x} : Set K)) = 2 ^ 9 * 240 := by
    have h := card_fiber_mul_card_centralizer Q x
    rw [hC, hQcard] at h
    exact h
  have hFle : Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧ (s : K ⧸ Q) =
      (x : K ⧸ Q)} ≤ 2 ^ 5 := by
    have h := fiber_card_le Q hQ hx2
    rw [hW] at h
    exact h
  have hEle : Nat.card ↥(Subgroup.centralizer ({x} : Set K) ⊓ Q) ≤ 2 ^ 5 := by
    let g : ↥(Subgroup.centralizer ({x} : Set K) ⊓ Q) →
        {q : K // q ∈ Q ∧ ⁅q, x⁆ ∈ centerOf Q} := fun q =>
      ⟨(q : K), ⟨(Subgroup.mem_inf.mp q.2).2, by
        have hxq : (q : K) * x = x * (q : K) :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp q.2).1
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hxq]
        exact Subgroup.one_mem _⟩⟩
    have hle : Nat.card ↥(Subgroup.centralizer ({x} : Set K) ⊓ Q) ≤
        Nat.card {q : K // q ∈ Q ∧ ⁅q, x⁆ ∈ centerOf Q} := by
      refine Nat.card_le_card_of_injective g ?_
      intro a b hab
      have h : (a : K) = (b : K) :=
        congrArg (fun z : {q : K // q ∈ Q ∧ ⁅q, x⁆ ∈ centerOf Q} => (z : K)) hab
      exact Subtype.ext h
    rw [hW] at hle
    exact hle
  have hEdiv : Nat.card ↥(Subgroup.centralizer ({x} : Set K) ⊓ Q) ∣ 2 ^ 9 := by
    have h := Subgroup.card_dvd_of_le
      (inf_le_right : Subgroup.centralizer ({x} : Set K) ⊓ Q ≤ Q)
    rwa [hQcard] at h
  obtain ⟨j, hj9, hEj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hEdiv
  have hj5 : j ≤ 5 := by
    have h2 : 2 ^ j ≤ 2 ^ 5 := by rw [← hEj]; exact hEle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hFdiv : 2 ^ 4 ∣ Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
      (s : K ⧸ Q) = (x : K ⧸ Q)} := by
    have h := card_dvd_card_fiber_mul Q x
    rw [hQcard, hEj] at h
    have h9 : 2 ^ 9 = 2 ^ j * 2 ^ (9 - j) := by
      rw [← pow_add]; congr 1; omega
    rw [h9] at h
    rw [mul_comm (Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
      (s : K ⧸ Q) = (x : K ⧸ Q)}) (2 ^ j)] at h
    have hcancel : 2 ^ (9 - j) ∣ Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
        (s : K ⧸ Q) = (x : K ⧸ Q)} :=
      Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 2 ^ j) h
    exact (Nat.pow_dvd_pow 2 (by omega : 4 ≤ 9 - j)).trans hcancel
  haveI : Nonempty {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧ (s : K ⧸ Q) = (x : K ⧸ Q)} :=
    ⟨⟨x, ⟨⟨1, by simp⟩, rfl⟩⟩⟩
  have hMpos : 0 < Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
      (s : K ⧸ Q) = (x : K ⧸ Q)} := Nat.card_pos
  have hM16or32 : Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
      (s : K ⧸ Q) = (x : K ⧸ Q)} = 16 ∨
      Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧ (s : K ⧸ Q) = (x : K ⧸ Q)} = 32 := by
    obtain ⟨k, hk⟩ := hFdiv
    have hk16 : Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
        (s : K ⧸ Q) = (x : K ⧸ Q)} = 16 * k := by
      rw [hk]; norm_num
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, mul_zero] at hk16; omega
      · exact hpos
    have hk2 : k ≤ 2 := by
      have : 16 * k ≤ 32 := by rw [← hk16]; exact hFle
      omega
    interval_cases k
    · left; omega
    · right; omega
  have h5D : 5 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set K)) := by
    have h5 : 5 ∣ Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
        (s : K ⧸ Q) = (x : K ⧸ Q)} *
          Nat.card ↥(Subgroup.centralizer ({x} : Set K)) := by
      rw [hFmul]; norm_num
    have h5M : ¬ 5 ∣ Nat.card {s : K // (∃ k : K, k * x * k⁻¹ = s) ∧
        (s : K ⧸ Q) = (x : K ⧸ Q)} := by
      rcases hM16or32 with h | h <;> rw [h] <;> norm_num
    rcases (Nat.prime_five.dvd_mul).mp h5 with h | h
    · exact absurd h h5M
    · exact h
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ρ', hρ'⟩ := exists_prime_orderOf_dvd_card' 5 h5D
  exact ⟨(ρ' : K), by rw [Subgroup.orderOf_coe, hρ'],
    Subgroup.mem_centralizer_singleton_iff.mp ρ'.2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
