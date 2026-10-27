module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

section Q8

variable {G : Type*} [Group G] {K : Subgroup G} {t : G}

theorem orderOf_eq_four (h8 : Nat.card K = 8) (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x)
    (hun : ∀ x ∈ K, x * x = 1 → x = 1 ∨ x = t) {b : G} (hb : b ∈ K) (hb1 : b ≠ 1) (hbt : b ≠ t) :
    orderOf b = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  set b' : ↥K := ⟨b, hb⟩ with hb'
  have hord : orderOf b' = orderOf b := Subgroup.orderOf_mk b hb
  have hdvd : orderOf b' ∣ 2 ^ 3 := by
    have := orderOf_dvd_natCard b'
    rwa [h8] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · exfalso
    exact hb1 (orderOf_eq_one_iff.mp (hord.symm.trans (by simpa using hk')))
  · exfalso
    have h2 : orderOf b = 2 := hord.symm.trans (by simpa using hk')
    have : b * b = 1 := by rw [← pow_two]; exact h2 ▸ pow_orderOf_eq_one b
    rcases hun b hb this with h | h
    · exact hb1 h
    · exact hbt h
  · simpa [hord] using hk'
  · exfalso
    have hcard : orderOf b' = Nat.card ↥K := by rw [h8]; simpa using hk'
    haveI := isCyclic_of_orderOf_eq_card b' hcard
    letI := IsCyclic.commGroup (α := ↥K)
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥K) ⟨y, hy⟩))

theorem eq_one_or_eq_of_central (h8 : Nat.card K = 8) (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x)
    (hun : ∀ x ∈ K, x * x = 1 → x = 1 ∨ x = t) {z : G} (hz : z ∈ K) (hc : ∀ x ∈ K, z * x = x * z) :
    z = 1 ∨ z = t := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : orderOf z = 4 := orderOf_eq_four h8 hnc hun hz hcon.1 hcon.2
  set z' : ↥K := ⟨z, hz⟩ with hz'
  set N : Subgroup ↥K := Subgroup.zpowers z' with hN
  have hNcard : Nat.card N = 4 := by
    rw [hN, Nat.card_zpowers, hz', Subgroup.orderOf_mk, h4]
  have hcent : z' ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  have hNle : N ≤ Subgroup.center ↥K := Subgroup.zpowers_le.mpr hcent
  haveI hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h := Subgroup.mem_center_iff.mp (hNle hn) g
    rwa [h, mul_inv_cancel_right]
  have hquot : Nat.card (↥K ⧸ N) = 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h8, hNcard] at this
    omega
  haveI : IsCyclic (↥K ⧸ N) := isCyclic_of_prime_card hquot
  letI := commGroupOfCyclicCenterQuotient (QuotientGroup.mk' N) (by rw [QuotientGroup.ker_mk']; exact hNle)
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  exact hxy (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥K) ⟨y, hy⟩))

theorem iter_conj {a x z : G} (h : a * x * a⁻¹ = x * z) (hz : a * z = z * a) (j : ℕ) :
    a ^ j * x * (a ^ j)⁻¹ = x * z ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hzj : a * z ^ j * a⁻¹ = z ^ j := by
      rw [mul_inv_eq_iff_eq_mul]
      exact ((Commute.pow_right (show Commute a z from hz) j).eq)
    calc a ^ (j + 1) * x * (a ^ (j + 1))⁻¹ = a * (a ^ j * x * (a ^ j)⁻¹) * a⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
      _ = (a * x * a⁻¹) * (a * z ^ j * a⁻¹) := by rw [ih]; group
      _ = x * z ^ (j + 1) := by rw [h, hzj, pow_succ']; group

theorem commute_of_fix (h8 : Nat.card K = 8) {b : G} (hb : b ∈ K) (h4 : orderOf b = 4) {a : G} {N : ℕ}
    (hN : Odd N) (haN : a ^ N = 1) (haK : ∀ x ∈ K, a * x * a⁻¹ ∈ K) (hab : a * b = b * a) {c : G}
    (hc : c ∈ K) : a * c = c * a := by
  classical
  haveI : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  set b' : ↥K := ⟨b, hb⟩ with hb'
  set T : Subgroup ↥K := Subgroup.zpowers b' with hT
  have hTcard : Nat.card T = 4 := by
    rw [hT, Nat.card_zpowers, hb', Subgroup.orderOf_mk, h4]
  have hTidx : T.index = 2 := by
    have := Subgroup.card_mul_index T
    rw [h8, hTcard] at this
    omega
  have hfix : ∀ k : ℤ, a * b ^ k * a⁻¹ = b ^ k := by
    intro k
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Commute.zpow_right (show Commute a b from hab) k).eq)
  have hfixn : ∀ k : ℕ, a * b ^ k * a⁻¹ = b ^ k := fun k => by
    have := hfix k
    rwa [zpow_natCast] at this
  have hmemT : ∀ x : ↥K, (⟨a * x * a⁻¹, haK x x.2⟩ : ↥K) ∈ T ↔ x ∈ T := by
    intro x
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      have hk' : a * (x : G) * a⁻¹ = b ^ k := (congrArg Subtype.val hk).symm
      have : (x : G) = b ^ k := by
        have h1 : (x : G) = a⁻¹ * (a * x * a⁻¹) * a := by group
        have h2 : a⁻¹ * b ^ k * a = b ^ k := by
          calc a⁻¹ * b ^ k * a = a⁻¹ * (a * b ^ k * a⁻¹) * a := by rw [hfix k]
            _ = b ^ k := by group
        rw [h1, hk', h2]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext this.symm⟩
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      have hk' : (x : G) = b ^ k := (congrArg Subtype.val hk).symm
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      show b ^ k = a * (x : G) * a⁻¹
      rw [hk', hfix k]
  have hcT : ∃ k : ℕ, k < 4 ∧ c⁻¹ * (a * c * a⁻¹) = b ^ k := by
    set c' : ↥K := ⟨c, hc⟩ with hc'
    have h1 : c'⁻¹ * (⟨a * c * a⁻¹, haK c hc⟩ : ↥K) ∈ T := by
      rw [Subgroup.mul_mem_iff_of_index_two hTidx, inv_mem_iff]
      exact (hmemT c').symm
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp h1)
    have hord : orderOf b' = 4 := by rw [hb', Subgroup.orderOf_mk, h4]
    refine ⟨k, by rwa [Finset.mem_range, hord] at hk, ?_⟩
    exact (congrArg Subtype.val hkx).symm
  obtain ⟨k, hk4, hkc⟩ := hcT
  have hconj : a * c * a⁻¹ = c * b ^ k := by
    rw [← hkc]; group
  have hit := iter_conj hconj (show a * b ^ k = b ^ k * a from (Commute.pow_right (show Commute a b from hab) k).eq) N
  rw [haN, ← pow_mul] at hit
  have hit1 : b ^ (k * N) = 1 := by
    have h2 : c = c * b ^ (k * N) := by simpa using hit
    exact (mul_eq_left.mp h2.symm)
  have hdvd : 4 ∣ k * N := by
    rw [← h4]
    exact orderOf_dvd_of_pow_eq_one hit1
  have hcop : Nat.Coprime 4 N := by
    have : Nat.Coprime (2 ^ 2) N := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hN)
    simpa using this
  have hk0 : k = 0 := by
    have := hcop.dvd_of_dvd_mul_right hdvd
    omega
  subst hk0
  rw [pow_zero, mul_one] at hconj
  calc a * c = (a * c * a⁻¹) * a := by group
    _ = c * a := by rw [hconj]

theorem cent_of_cent_prod {K' : Subgroup G} (h8 : Nat.card K = 8) (h8' : Nat.card K' = 8)
    (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) (hnc' : ∃ x ∈ K', ∃ y ∈ K', x * y ≠ y * x)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) (hun : ∀ x ∈ K, x * x = 1 → x = 1 ∨ x = t)
    (hun' : ∀ x ∈ K', x * x = 1 → x = 1 ∨ x = t) (hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x)
    {a : G} {N : ℕ} (hN : Odd N) (haN : a ^ N = 1) (hat : a * t = t * a)
    (haK : ∀ x ∈ K, a * x * a⁻¹ ∈ K) (haK' : ∀ x ∈ K', a * x * a⁻¹ ∈ K') {b b' : G} (hb : b ∈ K)
    (hb' : b' ∈ K') (hb1 : b ≠ 1) (hbt : b ≠ t) (hb'1 : b' ≠ 1) (hb't : b' ≠ t)
    (hab : a * (b * b') = (b * b') * a) :
    (∀ x ∈ K, a * x = x * a) ∧ (∀ x ∈ K', a * x = x * a) := by
  obtain ⟨γ, hγ⟩ : ∃ γ : G, γ = b⁻¹ * (a * b * a⁻¹) := ⟨_, rfl⟩
  obtain ⟨γ', hγ'⟩ : ∃ γ' : G, γ' = b'⁻¹ * (a * b' * a⁻¹) := ⟨_, rfl⟩
  have hγK : γ ∈ K := by rw [hγ]; exact K.mul_mem (K.inv_mem hb) (haK b hb)
  have hbγ : a * b * a⁻¹ = b * γ := by rw [hγ]; group
  have hbγ' : a * b' * a⁻¹ = b' * γ' := by rw [hγ']; group
  have hprod : γ * γ' = 1 := by
    have h1 : a * b * a⁻¹ * (a * b' * a⁻¹) = b * b' := by
      calc a * b * a⁻¹ * (a * b' * a⁻¹) = a * (b * b') * a⁻¹ := by group
        _ = b * b' := by rw [hab]; group
    rw [hbγ, hbγ'] at h1
    have h2 : γ * (b' * γ') = b' := by
      apply mul_left_cancel (a := b)
      calc b * (γ * (b' * γ')) = b * γ * (b' * γ') := by rw [mul_assoc]
        _ = b * b' := h1
    have h3 : γ * b' = b' * γ := hcomm γ hγK b' hb'
    have h4 : b' * (γ * γ') = b' * 1 := by
      rw [mul_one, ← mul_assoc, ← h3, mul_assoc]
      exact h2
    exact mul_left_cancel h4
  have hγK'' : γ ∈ K' := by
    have : γ = γ'⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [this, hγ']
    exact K'.inv_mem (K'.mul_mem (K'.inv_mem hb') (haK' b' hb'))
  have hγc : ∀ x ∈ K, γ * x = x * γ := fun x hx => (hcomm x hx γ hγK'').symm
  have hγ1 : γ = 1 := by
    rcases eq_one_or_eq_of_central h8 hnc hun hγK hγc with h | h
    · exact h
    · exfalso
      rw [h] at hbγ
      have hit := iter_conj hbγ hat N
      rw [haN] at hit
      have hbt' : b = b * t ^ N := by simpa using hit
      have htN : t ^ N = t := by
        obtain ⟨m, rfl⟩ := hN
        rw [pow_succ, pow_mul, show t ^ 2 = 1 by rw [pow_two]; exact ht2, one_pow, one_mul]
      rw [htN] at hbt'
      exact ht1 (mul_eq_left.mp hbt'.symm)
  have hγ'1 : γ' = 1 := by
    rw [hγ1, one_mul] at hprod
    exact hprod
  rw [hγ1, mul_one] at hbγ
  rw [hγ'1, mul_one] at hbγ'
  have hab1 : a * b = b * a := by
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [hbγ]
  have hab2 : a * b' = b' * a := by
    calc a * b' = (a * b' * a⁻¹) * a := by group
      _ = b' * a := by rw [hbγ']
  exact ⟨fun x hx => commute_of_fix h8 hb (orderOf_eq_four h8 hnc hun hb hb1 hbt) hN haN haK hab1 hx,
    fun x hx => commute_of_fix h8' hb' (orderOf_eq_four h8' hnc' hun' hb' hb'1 hb't) hN haN haK' hab2 hx⟩

end Q8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
