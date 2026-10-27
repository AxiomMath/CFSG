module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b

open CFSG.ClassicalInvolution.Generic

section Gen

variable {Y : Type*} [Group Y]

theorem pow_conj_eq {x k u : Y} {s : ℤ} (hxu : x * u * x⁻¹ = u) (hk : x * k * x⁻¹ = k * u ^ s)
    (i : ℕ) : x ^ i * k * (x ^ i)⁻¹ = k * u ^ ((i : ℤ) * s) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hxu' : x * u ^ ((i : ℤ) * s) * x⁻¹ = u ^ ((i : ℤ) * s) := by
      rw [← conj_zpow, hxu]
    calc x ^ (i + 1) * k * (x ^ (i + 1))⁻¹
        = x * (x ^ i * k * (x ^ i)⁻¹) * x⁻¹ := by group
      _ = x * (k * u ^ ((i : ℤ) * s)) * x⁻¹ := by rw [ih]
      _ = (x * k * x⁻¹) * (x * u ^ ((i : ℤ) * s) * x⁻¹) := by group
      _ = (k * u ^ s) * u ^ ((i : ℤ) * s) := by rw [hk, hxu']
      _ = k * u ^ (((i + 1 : ℕ) : ℤ) * s) := by
        rw [mul_assoc, ← zpow_add]
        congr 2
        push_cast
        ring

theorem centralizes_of_odd_fix {K : Subgroup Y} {x u : Y} (hK8 : Nat.card K = 8) (huK : u ∈ K)
    (hu4 : orderOf u = 4) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hxodd : Odd (orderOf x))
    (hxu : x * u * x⁻¹ = u) : ∀ k ∈ K, x * k * x⁻¹ = k := by
  classical
  set U : Subgroup Y := Subgroup.zpowers u with hU
  have hUK : U ≤ K := (Subgroup.zpowers_le).mpr huK
  have hUcard : Nat.card U = 4 := by rw [hU, Nat.card_zpowers, hu4]
  have hidx : (U.subgroupOf K).index = 2 := by
    have h1 := (U.subgroupOf K).card_mul_index
    have h2 : Nat.card (U.subgroupOf K) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
    rw [h2, hUcard, hK8] at h1
    omega
  have hmem_iff : ∀ {a b : Y} (ha : a ∈ K) (hb : b ∈ K), a * b ∈ U ↔ (a ∈ U ↔ b ∈ U) := by
    intro a b ha hb
    exact Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : K)) (b := ⟨b, hb⟩)
  have hxinj : ∀ a b : Y, x * a * x⁻¹ = x * b * x⁻¹ → a = b := fun a b h =>
    mul_left_cancel (mul_right_cancel h)
  have hxU : ∀ v ∈ U, x * v * x⁻¹ = v := by
    intro v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← conj_zpow, hxu]
  obtain ⟨m, hm⟩ := hxodd
  have hxm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  intro k hk
  by_cases hkU : k ∈ U
  · exact hxU k hkU
  · have hk1K : x * k * x⁻¹ ∈ K := hxK k hk
    have hk1U : x * k * x⁻¹ ∉ U := by
      intro h
      apply hkU
      have h1 : x * (x * k * x⁻¹) * x⁻¹ = x * k * x⁻¹ := hxU _ h
      have h2 : x * k * x⁻¹ = k := hxinj _ _ h1
      exact h2 ▸ h
    have hkinvU : k⁻¹ * (x * k * x⁻¹) ∈ U := by
      have hkinv : k⁻¹ ∈ K := K.inv_mem hk
      rw [hmem_iff hkinv hk1K]
      constructor
      · intro h
        exact absurd (by simpa using U.inv_mem h) hkU
      · intro h
        exact absurd h hk1U
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hkinvU
    have hks : x * k * x⁻¹ = k * u ^ s := by
      calc x * k * x⁻¹ = k * (k⁻¹ * (x * k * x⁻¹)) := by group
        _ = k * u ^ s := by rw [← hs]
    have hpow := pow_conj_eq hxu hks (orderOf x)
    rw [hxm] at hpow
    simp only [one_mul, inv_one, mul_one] at hpow
    have hu1 : u ^ ((orderOf x : ℤ) * s) = 1 := by
      have : k = k * u ^ ((orderOf x : ℤ) * s) := hpow
      exact (mul_eq_left.mp this.symm)
    have hdvd : (4 : ℤ) ∣ (orderOf x : ℤ) * s := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hu1
      rwa [hu4] at this
    have hcop : IsCoprime (4 : ℤ) (orderOf x : ℤ) := by
      have h2 : (orderOf x : ℤ) = 2 * m + 1 := by exact_mod_cast hm
      rw [h2]
      exact ⟨-((m : ℤ) ^ 2 + m), 2 * m + 1, by ring⟩
    have hs4 : (4 : ℤ) ∣ s := hcop.dvd_of_dvd_mul_left hdvd
    have hus : u ^ s = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hu4]; exact hs4)
    rw [hks, hus, mul_one]

theorem conjSub_fix_of_odd {K K' : Subgroup Y} {x : Y} (hne : K ≠ K') (hodd : Odd (orderOf x))
    (hK : conjSub x K = K ∨ conjSub x K = K') (hK' : conjSub x K' = K ∨ conjSub x K' = K') :
    conjSub x K = K ∧ conjSub x K' = K' := by
  have hKK : conjSub x K = K := by
    by_contra hcon
    have h1 : conjSub x K = K' := hK.resolve_left hcon
    have h2 : conjSub x K' = K := by
      rcases hK' with h | h
      · exact h
      · exfalso
        exact hne (conjSub_injective x (h1.trans h.symm))
    have h3 : ∀ j : ℕ, conjSub (x ^ (2 * j)) K = K := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, pow_succ, conjSub_mul, conjSub_mul,
          h1, h2, ih]
    obtain ⟨m, hm⟩ := hodd
    have hxm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    have h4 : x = x ^ (2 * (m + 1)) := by
      have : x ^ (2 * (m + 1)) = x ^ orderOf x * x := by
        rw [hm, ← pow_succ]
        congr 1
      rw [this, hxm, one_mul]
    have h5 : conjSub x K = K := by
      conv_lhs => rw [h4]
      exact h3 (m + 1)
    exact hcon h5
  refine ⟨hKK, ?_⟩
  rcases hK' with h | h
  · exfalso
    exact hne (conjSub_injective x (hKK.trans h.symm))
  · exact h

theorem eq_one_of_mem_odd_two {N Q : Subgroup Y} (hN : Odd (Nat.card N)) (hQ : IsPGroup 2 Q) {g : Y}
    (hgN : g ∈ N) (hgQ : g ∈ Q) : g = 1 := by
  have h1 : orderOf g ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨g, hgN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
  have h2 : orderOf g ∣ 2 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have := congrArg Subtype.val hk
    simpa using this
  have h3 : Nat.Coprime (orderOf g) 2 := Nat.coprime_two_right.mpr (Odd.of_dvd_nat hN h1)
  have h5 : Nat.Coprime (orderOf g) (2 ^ k) := Nat.Coprime.pow_right k h3
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h5 h2)

theorem comm_of_odd_of_le_two {N Q J : Subgroup Y} (hN : Odd (Nat.card N)) (hQ : IsPGroup 2 Q)
    (hJQ : J ≤ Q) {x : Y} (hxN : x ∈ N) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hJN : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N) : ∀ j ∈ J, x * j = j * x := by
  intro j hj
  have h1 : x * j * x⁻¹ * j⁻¹ ∈ Q := Q.mul_mem (hxQ j (hJQ hj)) (Q.inv_mem (hJQ hj))
  have h2 : x * j * x⁻¹ * j⁻¹ ∈ N := by
    have : x * (j * x⁻¹ * j⁻¹) = x * j * x⁻¹ * j⁻¹ := by group
    rw [← this]
    exact N.mul_mem hxN (hJN j hj x⁻¹ (N.inv_mem hxN))
  have h3 := eq_one_of_mem_odd_two hN hQ h2 h1
  calc x * j = x * j * x⁻¹ * j⁻¹ * j * x := by group
    _ = j * x := by rw [h3]; group

theorem conj_eq_of_odd_of_inv {x u : Y} (hodd : Odd (orderOf x))
    (h : x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u⁻¹) : x * u * x⁻¹ = u := by
  rcases h with h | h
  · exact h
  · have h2 : (x * x) * u * (x * x)⁻¹ = u := by
      calc (x * x) * u * (x * x)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by group
        _ = x * u⁻¹ * x⁻¹ := by rw [h]
        _ = (x * u * x⁻¹)⁻¹ := by group
        _ = u := by rw [h]; group
    have h3 : ∀ j : ℕ, (x ^ (2 * j)) * u * (x ^ (2 * j))⁻¹ = u := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc (x ^ (2 * (j + 1))) * u * (x ^ (2 * (j + 1)))⁻¹
            = (x * x) * (x ^ (2 * j) * u * (x ^ (2 * j))⁻¹) * (x * x)⁻¹ := by
              rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
              group
          _ = u := by rw [ih, h2]
    obtain ⟨m, hm⟩ := hodd
    have hxm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    have h4 : x = x ^ (2 * (m + 1)) := by
      have : x ^ (2 * (m + 1)) = x ^ orderOf x * x := by
        rw [hm, ← pow_succ]
        congr 1
      rw [this, hxm, one_mul]
    conv_lhs => rw [h4]
    exact h3 (m + 1)

theorem mem_zpowers_sq_eq_one {z g : Y} (hz : z * z = 1) (hg : g ∈ Subgroup.zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rcases Int.even_or_odd' k with ⟨j, hj | hj⟩
  · left
    rw [hj, zpow_mul, hz2, one_zpow]
  · right
    rw [hj, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

theorem odd_orderOf_of_mem {N : Subgroup Y} (hN : Odd (Nat.card N)) {x : Y} (hx : x ∈ N) :
    Odd (orderOf x) := by
  have := orderOf_dvd_natCard (⟨x, hx⟩ : N)
  rw [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat hN this

end Gen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b
