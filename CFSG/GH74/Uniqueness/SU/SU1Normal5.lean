module

public import CFSG.GH74.Uniqueness.SU.SU1Normal3

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

theorem odd_of_pow_mod {k n u : ℕ} (hk : 1 ≤ k) (hn : n ≠ 0) (h : u ^ n % 2 ^ k = 1) :
    u % 2 = 1 := by
  have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h3 : u ^ n % 2 = 1 := by
    have := Nat.mod_mod_of_dvd (u ^ n) h2k
    rw [h] at this
    omega
  rcases Nat.mod_two_eq_zero_or_one u with h0 | h0
  · exfalso
    have : u ^ n % 2 = 0 := by
      rw [Nat.pow_mod, h0, zero_pow hn, Nat.zero_mod]
    omega
  · exact h0

theorem sq_mod_four {v : ℕ} (h : v % 2 = 1) : v ^ 2 % 4 = 1 := by
  obtain ⟨t, ht⟩ : ∃ t, v = 2 * t + 1 := ⟨v / 2, by omega⟩
  have e : v ^ 2 = 4 * (t * t + t) + 1 := by rw [ht]; ring
  omega

theorem mul_residue {N x y : ℕ} (hN : 2 ≤ N) (hx : x % (2 * N) = 2 * N - 1)
    (hy : y % (2 * N) = N - 1) : (x * y) % (2 * N) = N + 1 := by
  rw [Nat.mul_mod, hx, hy]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have e1 : 2 * (M + 2) - 1 = 2 * M + 3 := by omega
  have e2 : M + 2 - 1 = M + 1 := by omega
  rw [e1, e2]
  have : (2 * M + 3) * (M + 1) = (M + 2 + 1) + (2 * (M + 2)) * M := by ring
  rw [this, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem commute_of_mem_zpowers {a g : P} (hg : g ∈ zpowers a) : g * a = a * g := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((Commute.refl a).zpow_left m).eq

omit [Finite P] in
theorem NSetting.mem_zpowers_iff_exp {Q : Subgroup P} {a : P} (h : NSetting Q a)
    (h1 : 1 < orderOf a) {g : P} (hg : g ∈ Q) {u : ℕ} (hu : g * a * g⁻¹ = a ^ u) :
    g ∈ zpowers a ↔ u % orderOf a = 1 := by
  constructor
  · intro hmem
    have hc : g * a = a * g := commute_of_mem_zpowers hmem
    have h2 : a ^ u = a ^ 1 := by
      rw [← hu, pow_one, hc]
      group
    have h3 := pow_inj_mod.mp h2
    have h4 : 1 % orderOf a = 1 := Nat.mod_eq_of_lt h1
    rwa [h4] at h3
  · intro hmod
    apply h.centralizer g hg
    have h2 : a ^ u = a := by
      rw [pow_eq_pow_mod u (pow_orderOf_eq_one a), hmod, pow_one]
    rw [h2] at hu
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [hu]

omit [Finite P] in
theorem NSetting.inv_mul_mem_of_same_exp {Q : Subgroup P} {a : P} (h : NSetting Q a) {y g : P}
    (hy : y ∈ Q) (hg : g ∈ Q) {u w : ℕ} (hu : y * a * y⁻¹ = a ^ u) (hw : g * a * g⁻¹ = a ^ w)
    (hmod : u % orderOf a = w % orderOf a) : y⁻¹ * g ∈ zpowers a := by
  apply h.centralizer _ (Q.mul_mem (Q.inv_mem hy) hg)
  have huw : a ^ u = a ^ w := pow_inj_mod.mpr hmod
  have e : (y⁻¹ * g) * a * (y⁻¹ * g)⁻¹ = a := by
    calc (y⁻¹ * g) * a * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * a * g⁻¹) * y := by group
      _ = y⁻¹ * a ^ w * y := by rw [hw]
      _ = y⁻¹ * a ^ u * y := by rw [huw]
      _ = y⁻¹ * (y * a * y⁻¹) * y := by rw [hu]
      _ = a := by group
  calc y⁻¹ * g * a = (y⁻¹ * g) * a * (y⁻¹ * g)⁻¹ * (y⁻¹ * g) := by group
    _ = a * (y⁻¹ * g) := by rw [e]

theorem two_le_of_setting (hP : IsPGroup 2 P) {Q : Subgroup P} {a : P} (h : NSetting Q a) {k : ℕ}
    (hord : orderOf a = 2 ^ k) (hk : 1 ≤ k) (hne : zpowers a ≠ Q) : 2 ≤ k := by
  by_contra hcon
  have hk1 : k = 1 := by omega
  subst hk1
  have ha2 : a ^ 2 = 1 := by
    rw [← pow_one 2, ← hord]
    exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hcen : a ∈ center P := mem_center_of_normal_prime Nat.prime_two hP ha1 ha2 h.normalA
  apply hne
  refine le_antisymm h.le (fun g hg => ?_)
  exact h.centralizer g hg (Subgroup.mem_center_iff.mp hcen g)

theorem sq_mem_of_pow_four_mem {k : ℕ} (hP : IsPGroup 2 P) {Q : Subgroup P} {a : P}
    (h : NSetting Q a) (hord : orderOf a = 2 ^ k) (hk : 2 ≤ k)
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False)
    {z : P} (hz : z ∈ Q) (hz4 : z ^ 4 ∈ zpowers a) : z ^ 2 ∈ zpowers a := by
  have h1 : 1 < orderOf a := by rw [hord]; exact Nat.one_lt_two_pow (by omega)
  have h1' : 1 % 2 ^ k = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have ha1 : a ^ (2 ^ k) = 1 := by rw [← hord]; exact pow_orderOf_eq_one a
  obtain ⟨v, hv⟩ := h.exists_conj_pow z
  have hv4 : v ^ 4 % 2 ^ k = 1 := by
    have e := conj_npow hv 4
    have e2 : a ^ (v ^ 4) = a ^ 1 := by
      rw [← e, pow_one, commute_of_mem_zpowers hz4]
      group
    have h3 := pow_inj_mod.mp e2
    rw [hord, h1'] at h3
    exact h3
  have hodd : v % 2 = 1 := odd_of_pow_mod (by omega) (by norm_num) hv4
  have hs4 : v ^ 2 % 4 = 1 := sq_mod_four hodd
  have hz2 : z ^ 2 * a * (z ^ 2)⁻¹ = a ^ (v ^ 2) := conj_npow hv 2
  have hz2Q : z ^ 2 ∈ Q := Q.pow_mem hz 2
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2 : k = 2 := by omega
    subst hk2
    refine (h.mem_zpowers_iff_exp h1 hz2Q hz2).mpr ?_
    have e4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [hord, e4]
    exact hs4
  · set q : ℕ := 2 ^ (k - 2) with hq
    have hq4 : 4 * q = 2 ^ k := by
      rw [hq, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have hq2 : 2 * q = 2 ^ (k - 1) := by
      rw [hq, ← pow_succ']
      congr 1
      omega
    have hqpp : IsPrimePow q := Nat.prime_two.isPrimePow.pow (by omega)
    have hq_even : 2 ∣ q := dvd_pow_self 2 (by omega)
    obtain ⟨q', hq'⟩ := hq_even
    have hq0 : 0 < q := by positivity
    have e4 : v ^ 2 * v ^ 2 = v ^ 4 := by ring
    have hsq : v ^ 2 * v ^ 2 % (4 * q) = 1 := by rw [e4, hq4]; exact hv4
    have hmod4 := Nat.mod_mod_of_dvd (v ^ 2) (dvd_mul_right 4 q)
    rcases sq_mod_eq_one hqpp ⟨q', hq'⟩ hsq with h1'' | h2'' | h3'' | h4''
    · refine (h.mem_zpowers_iff_exp h1 hz2Q hz2).mpr ?_
      rw [hord, ← hq4]
      exact h1''
    · exfalso
      refine false_of_u0 hP h hord hk3 hstar hz2Q ?_
      rw [hz2, pow_eq_pow_mod (v ^ 2) ha1, ← hq4, h2'', hq2]
    · exfalso
      rw [h3'', hs4] at hmod4
      omega
    · exfalso
      rw [h4'', hs4] at hmod4
      omega

theorem sq_mem {k : ℕ} (hP : IsPGroup 2 P) {Q : Subgroup P} {a : P} (h : NSetting Q a)
    (hord : orderOf a = 2 ^ k) (hk : 2 ≤ k)
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False)
    {y : P} (hy : y ∈ Q) : y ^ 2 ∈ zpowers a := by
  have key : ∀ n : ℕ, ∀ y ∈ Q, y ^ (2 ^ (n + 1)) ∈ zpowers a → y ^ 2 ∈ zpowers a := by
    intro n
    induction n with
    | zero =>
      intro y hy hmem
      simpa using hmem
    | succ n ih =>
      intro y hy hmem
      have hy2 : y ^ 2 ∈ Q := Q.pow_mem hy 2
      have h1 : (y ^ 2) ^ (2 ^ (n + 1)) ∈ zpowers a := by
        rw [← pow_mul, ← pow_succ']
        exact hmem
      have h2 := ih (y ^ 2) hy2 h1
      have h3 : y ^ 4 ∈ zpowers a := by
        have e : (y ^ 2) ^ 2 = y ^ 4 := by rw [← pow_mul]
        rwa [e] at h2
      exact sq_mem_of_pow_four_mem hP h hord hk hstar hy h3
  obtain ⟨n, hn⟩ := hP y
  apply key n y hy
  rw [pow_succ, pow_mul, hn, one_pow]
  exact Subgroup.one_mem _

theorem exp_cases {k : ℕ} (hP : IsPGroup 2 P) {Q : Subgroup P} {a : P} (h : NSetting Q a)
    (hord : orderOf a = 2 ^ k) (hk : 2 ≤ k)
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False)
    {g : P} (hg : g ∈ Q) {u : ℕ} (hu : g * a * g⁻¹ = a ^ u) :
    u % 2 ^ k = 1 ∨ u % 2 ^ k = 2 ^ k - 1 ∨ (3 ≤ k ∧ u % 2 ^ k = 2 ^ (k - 1) - 1) := by
  have h1' : 1 % 2 ^ k = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have ha1 : a ^ (2 ^ k) = 1 := by rw [← hord]; exact pow_orderOf_eq_one a
  have hg2 := sq_mem hP h hord hk hstar hg
  have hu2 : u ^ 2 % 2 ^ k = 1 := by
    have e := conj_npow hu 2
    have e2 : a ^ (u ^ 2) = a ^ 1 := by
      rw [← e, pow_one, commute_of_mem_zpowers hg2]
      group
    have h3 := pow_inj_mod.mp e2
    rw [hord, h1'] at h3
    exact h3
  have hodd : u % 2 = 1 := odd_of_pow_mod (by omega) (by norm_num) hu2
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2 : k = 2 := by omega
    subst hk2
    have hmod : u % 4 = 1 ∨ u % 4 = 3 := by omega
    norm_num
    exact hmod
  · set q : ℕ := 2 ^ (k - 2) with hq
    have hq4 : 4 * q = 2 ^ k := by
      rw [hq, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have hq2 : 2 * q = 2 ^ (k - 1) := by
      rw [hq, ← pow_succ']
      congr 1
      omega
    have hqpp : IsPrimePow q := Nat.prime_two.isPrimePow.pow (by omega)
    have hq_even : 2 ∣ q := dvd_pow_self 2 (by omega)
    have hsq : u * u % (4 * q) = 1 := by rw [← pow_two, hq4]; exact hu2
    rcases sq_mod_eq_one hqpp hq_even hsq with h1'' | h2'' | h3'' | h4''
    · left
      rw [← hq4]
      exact h1''
    · exfalso
      refine false_of_u0 hP h hord hk3 hstar hg ?_
      rw [hu, pow_eq_pow_mod u ha1, ← hq4, h2'', hq2]
    · right; right
      refine ⟨hk3, ?_⟩
      rw [← hq4, h3'', hq2]
    · right; left
      rw [← hq4, h4'']

theorem two_shape {k : ℕ} (hP : IsPGroup 2 P) {Q : Subgroup P} {a : P} (h : NSetting Q a)
    (hord : orderOf a = 2 ^ k) (hk : 2 ≤ k) (hne : zpowers a ≠ Q)
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False) :
    ∃ y ∈ Q, y ∉ zpowers a ∧ y * y ∈ zpowers a ∧
      (∀ g ∈ Q, g ∈ zpowers a ∨ y⁻¹ * g ∈ zpowers a) ∧
      (y * a * y⁻¹ = a⁻¹ ∨ (3 ≤ k ∧ y * a * y⁻¹ = a ^ (2 ^ (k - 1) - 1))) := by
  have h1 : 1 < orderOf a := by rw [hord]; exact Nat.one_lt_two_pow (by omega)
  have ha1 : a ^ (2 ^ k) = 1 := by rw [← hord]; exact pow_orderOf_eq_one a
  obtain ⟨y, hyQ, hyA⟩ : ∃ y ∈ Q, y ∉ zpowers a := by
    have : ¬ Q ≤ zpowers a := fun hle => hne (le_antisymm h.le hle)
    exact IsConcreteLE.not_le_iff_exists.mp this
  obtain ⟨u, hu⟩ := h.exists_conj_pow y
  have hne1 : u % 2 ^ k ≠ 1 := by
    intro hmod
    apply hyA
    exact (h.mem_zpowers_iff_exp h1 hyQ hu).mpr (by rw [hord]; exact hmod)
  have hy2 : y * y ∈ zpowers a := by
    rw [← pow_two]
    exact sq_mem hP h hord hk hstar hyQ
  have hy_exp : u % 2 ^ k = 2 ^ k - 1 ∨ (3 ≤ k ∧ u % 2 ^ k = 2 ^ (k - 1) - 1) := by
    rcases exp_cases hP h hord hk hstar hyQ hu with h' | h' | h'
    · exact absurd h' hne1
    · exact Or.inl h'
    · exact Or.inr h'
  have hN2 : 2 * 2 ^ (k - 1) = 2 ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  have hmixed : ∀ g ∈ Q, ∀ w : ℕ, g * a * g⁻¹ = a ^ w → 3 ≤ k →
      ((u % 2 ^ k = 2 ^ k - 1 ∧ w % 2 ^ k = 2 ^ (k - 1) - 1) ∨
        (u % 2 ^ k = 2 ^ (k - 1) - 1 ∧ w % 2 ^ k = 2 ^ k - 1)) → False := by
    intro g hg w hw hk3 hcase
    have hN : 2 ≤ 2 ^ (k - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right two_pos (by omega)
    have hprod : (u * w) % 2 ^ k = 2 ^ (k - 1) + 1 := by
      rcases hcase with ⟨hx, hy'⟩ | ⟨hx, hy'⟩
      · have := mul_residue (N := 2 ^ (k - 1)) (x := u) (y := w) hN (by rw [hN2]; exact hx)
          (by rw [hN2]; exact hy')
        rwa [hN2] at this
      · have := mul_residue (N := 2 ^ (k - 1)) (x := w) (y := u) hN (by rw [hN2]; exact hy')
          (by rw [hN2]; exact hx)
        rw [hN2, mul_comm] at this
        exact this
    refine false_of_u0 hP h hord hk3 hstar (Q.mul_mem hyQ hg) ?_
    rw [NSetting.conj_mul hu hw, pow_eq_pow_mod _ ha1, hprod]
  refine ⟨y, hyQ, hyA, hy2, ?_, ?_⟩
  · intro g hg
    obtain ⟨w, hw⟩ := h.exists_conj_pow g
    have hsame : u % 2 ^ k = w % 2 ^ k → y⁻¹ * g ∈ zpowers a := fun hmod =>
      h.inv_mul_mem_of_same_exp hyQ hg hu hw (by rw [hord]; exact hmod)
    rcases exp_cases hP h hord hk hstar hg hw with hw1 | hw2 | hw3
    · left
      exact (h.mem_zpowers_iff_exp h1 hg hw).mpr (by rw [hord]; exact hw1)
    · right
      rcases hy_exp with hy1 | ⟨hk3, hy1⟩
      · exact hsame (by rw [hy1, hw2])
      · exact (hmixed g hg w hw hk3 (Or.inr ⟨hy1, hw2⟩)).elim
    · right
      obtain ⟨hk3, hw3⟩ := hw3
      rcases hy_exp with hy1 | ⟨_, hy1⟩
      · exact (hmixed g hg w hw hk3 (Or.inl ⟨hy1, hw3⟩)).elim
      · exact hsame (by rw [hy1, hw3])
  · rcases hy_exp with hy1 | ⟨hk3, hy1⟩
    · left
      rw [hu, pow_eq_pow_mod u ha1, hy1]
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
      exact ha1
    · right
      refine ⟨hk3, ?_⟩
      rw [hu, pow_eq_pow_mod u ha1, hy1]

theorem two_shape_of_rank (hP : IsPGroup 2 P) {Q : Subgroup P} [hQ : Q.Normal]
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False)
    (hrank : ∃ E : Subgroup P, E ≤ Q ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 2) :
    ∃ (k : ℕ) (a : P), 2 ≤ k ∧ orderOf a = 2 ^ k ∧ a ∈ Q ∧
      ∃ y ∈ Q, y ∉ zpowers a ∧ y * y ∈ zpowers a ∧
        (∀ g ∈ Q, g ∈ zpowers a ∨ y⁻¹ * g ∈ zpowers a) ∧
        (y * a * y⁻¹ = a⁻¹ ∨ (3 ≤ k ∧ y * a * y⁻¹ = a ^ (2 ^ (k - 1) - 1))) := by
  obtain ⟨a, k, hset, hord, hk1, hne⟩ := exists_setting Nat.prime_two hP hstar hrank
  have hk2 := two_le_of_setting hP hset hord hk1 hne
  obtain ⟨y, hyQ, hyA, hy2, hcos, hconj⟩ := two_shape hP hset hord hk2 hne hstar
  exact ⟨k, a, hk2, hord, hset.le (Subgroup.mem_zpowers a), y, hyQ, hyA, hy2, hcos, hconj⟩

end CFSG.GH74.Uniqueness.SU.SU1
