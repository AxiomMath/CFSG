module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Out

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T7U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {R V : Subgroup G} {z x y : G} {n : ℕ}

theorem z_eq_pow_of_coord (c : T7F2.QuatCoord R x y n) (hz : IsUniqueInvolution R z) :
    z = x ^ (2 ^ n) := by
  have h1 : x ^ (2 ^ n) * x ^ (2 ^ n) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']; exact c.pow_card
  have h2 : x ^ (2 ^ n) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [c.hord]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases hz.unique _ (R.pow_mem c.ha _) h1 with h3 | h3
  · exact absurd h3 h2
  · exact h3.symm

theorem coord_of_isFAut (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (s : T7F2.Out.Setting R V x y n) {a : G} (haV : a ∈ V) (hF : IsFAut R a)
    (ha2 : a * a ∈ Subgroup.zpowers z) :
    2 ≤ n ∧ a * x * a⁻¹ = x ^ ((1 : ℤ) + 2 ^ n) ∧
      ∃ j : ℤ, a * y * a⁻¹ = y * x ^ j ∧ (x ^ j = 1 ∨ x ^ j = x ^ (2 ^ n)) := by
  have c := s.coord
  obtain ⟨haN, hsq, Q, R₀, hQ, hQq, hR₀, hcard⟩ := hF
  have hR2 : IsPGroup 2 ↥R := AscL62.isPGroup_of_isQuatSub hR
  have hR₀R : R₀ = R := (hR₀.2.2 R le_rfl hR2 hR₀.1).symm
  have hQeq : Q = R ⊓ Subgroup.centralizer ({a} : Set G) :=
    (hQ.2.2 (R ⊓ Subgroup.centralizer ({a} : Set G)) le_rfl (hR2.to_le inf_le_left) hQ.1).symm
  have hQR : Q ≤ R := hQeq ▸ inf_le_left
  have hmemQ : ∀ r : G, r ∈ Q ↔ r ∈ R ∧ a * r * a⁻¹ = r := by
    intro r
    rw [hQeq, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← h2]; group
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : a * r = r * a := by
        calc a * r = (a * r * a⁻¹) * a := by group
          _ = r * a := by rw [h2]
      exact this.symm
  have hcardQ : Nat.card R = 2 * Nat.card Q := by rw [← hR₀R]; exact hcard
  have hcardR : Nat.card R = 2 ^ (n + 2) := c.natCard
  have hQ8 := hQq.eight_le
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ (n + 2) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hQcard : Nat.card Q = 2 ^ (n + 1) := by
    have : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    omega
  have hrel : (Q.subgroupOf R).index = 2 := by
    have h1 : Q.relIndex R * Nat.card ↥(Q ⊓ R) = Nat.card R := Subgroup.relIndex_mul_card Q R
    rw [inf_of_le_left hQR] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have : Q.relIndex R * Nat.card Q = 2 * Nat.card Q := by rw [h1, hcardQ]
    exact Nat.eq_of_mul_eq_mul_right hQpos this
  have hxxQ : x * x ∈ Q :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hrel ⟨x, c.ha⟩)
  obtain ⟨i, j, hi, hia, hjb⟩ := s.coord_of_mem haV
  have h1 : (2 : ℤ) ^ n ∣ i - 1 := by
    have e := ((hmemQ _).mp hxxQ).2
    have e1 : a * (x * x) * a⁻¹ = x ^ (i + i) := by
      calc a * (x * x) * a⁻¹ = (a * x * a⁻¹) * (a * x * a⁻¹) := by group
        _ = x ^ i * x ^ i := by rw [hia]
        _ = x ^ (i + i) := (zpow_add x i i).symm
    have e2 : x * x = x ^ (2 : ℤ) := (zpow_two x).symm
    have h3 : x ^ (i + i) = x ^ (2 : ℤ) := by rw [← e1, e, e2]
    rw [c.zpow_eq_iff] at h3
    have e3 : (i + i) - 2 = 2 * (i - 1) := by ring
    rw [e3, pow_succ'] at h3
    exact (mul_dvd_mul_iff_left (by norm_num)).mp h3
  have h2 : ¬ (2 : ℤ) ^ (n + 1) ∣ i - 1 := by
    intro hdiv
    have hax : a * x * a⁻¹ = x := by
      rw [hia, c.zpow_eq_iff.mpr hdiv, zpow_one]
    have hxQ : x ∈ Q := (hmemQ x).mpr ⟨c.ha, hax⟩
    have hle : Subgroup.zpowers x ≤ Q := Subgroup.zpowers_le.mpr hxQ
    have hcz : Nat.card (Subgroup.zpowers x) = 2 ^ (n + 1) := by
      rw [Nat.card_zpowers, c.hord]
    have hQz : Subgroup.zpowers x = Q := Subgroup.eq_of_le_of_card_ge hle (by omega)
    obtain ⟨u, hu, v, hv, huv⟩ := hQq.exists_not_commute
    rw [← hQz] at hu hv
    obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨q, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact huv (((Commute.refl x).zpow_zpow p q).eq)
  obtain ⟨t, ht⟩ := h1
  have htodd : Odd t := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨u, hu⟩ := hev
    apply h2
    refine ⟨u, ?_⟩
    rw [ht, hu]; ring
  obtain ⟨u₀, hu₀⟩ := htodd
  have hi_eq : i = 1 + 2 ^ n * (2 * u₀ + 1) := by rw [← hu₀]; linarith [ht]
  have hkey : a * x * a⁻¹ = x ^ ((1 : ℤ) + 2 ^ n) := by
    rw [hia, c.zpow_eq_iff]
    refine ⟨u₀, ?_⟩
    rw [hi_eq]; ring
  refine ⟨hn2, hkey, j, hjb, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha2
  have hjy : (a * a) * y * (a * a)⁻¹ = y := by
    rw [← hk]
    have hyz : Commute y z := AscL62.uniqueInvolution_comm hz c.hb
    have hcomm : y * z ^ k = z ^ k * y := (hyz.zpow_right k).eq
    calc z ^ k * y * (z ^ k)⁻¹ = (y * z ^ k) * (z ^ k)⁻¹ := by rw [hcomm]
      _ = y := by group
  have hjy2 : (a * a) * y * (a * a)⁻¹ = y * x ^ (j + i * j) := by
    calc (a * a) * y * (a * a)⁻¹ = a * (a * y * a⁻¹) * a⁻¹ := by group
      _ = a * (y * x ^ j) * a⁻¹ := by rw [hjb]
      _ = (a * y * a⁻¹) * (a * x ^ j * a⁻¹) := by group
      _ = (y * x ^ j) * x ^ (i * j) := by rw [hjb, T7F2.Out.conj_zpow_a hia j]
      _ = y * x ^ (j + i * j) := by rw [mul_assoc, ← zpow_add]
  have hx1 : x ^ (j + i * j) = 1 := by
    have : y * x ^ (j + i * j) = y * 1 := by rw [mul_one, ← hjy2, hjy]
    exact mul_left_cancel this
  have hdiv : (2 : ℤ) ^ (n + 1) ∣ j + i * j := by
    have : x ^ (j + i * j) = x ^ (0 : ℤ) := by rw [hx1, zpow_zero]
    rw [c.zpow_eq_iff] at this
    simpa using this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set w : ℤ := 1 + 2 ^ (m' + 1) * (2 * u₀ + 1) with hw
  have hwodd : Odd w := by
    have : Even (2 ^ (m' + 1) * (2 * u₀ + 1) : ℤ) :=
      (Even.pow_of_ne_zero (by decide : Even (2 : ℤ)) (Nat.succ_ne_zero m')).mul_right _
    exact this.one_add
  have hexp : j + i * j = 2 * (w * j) := by rw [hi_eq, hw]; ring
  have hdiv2 : (2 : ℤ) ^ (m' + 1 + 1) ∣ w * j := by
    rw [hexp, pow_succ' (2 : ℤ) (m' + 1 + 1)] at hdiv
    exact (mul_dvd_mul_iff_left (by norm_num)).mp hdiv
  have hcop : IsCoprime ((2 : ℤ) ^ (m' + 1 + 1)) w :=
    IsCoprime.pow_left (Int.isCoprime_two_left.mpr hwodd)
  have hjd : (2 : ℤ) ^ (m' + 1 + 1) ∣ j := hcop.dvd_of_dvd_mul_left hdiv2
  obtain ⟨r, hr⟩ := hjd
  rcases Int.even_or_odd' r with ⟨r', hr' | hr'⟩
  · left
    have : x ^ j = x ^ (0 : ℤ) := by
      rw [c.zpow_eq_iff]
      refine ⟨r', ?_⟩
      rw [hr, hr']; ring
    rw [this, zpow_zero]
  · right
    have : x ^ j = x ^ ((2 : ℤ) ^ (m' + 1 + 1)) := by
      rw [c.zpow_eq_iff]
      refine ⟨r', ?_⟩
      rw [hr, hr']; ring
    rw [this]
    norm_cast

end CFSG.ClassicalInvolution.Asc77.T7U
