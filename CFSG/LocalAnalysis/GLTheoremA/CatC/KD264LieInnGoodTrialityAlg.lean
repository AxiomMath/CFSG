module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutExcBurnside

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

theorem exists_cycle_dvd {ν : ℕ} {L : Type} [Field L] {p : ℕ} (hp : p.Prime)
    (π : Equiv.Perm (Fin ν)) (Q : ℤ) (ω : Fin ν → Fin ν → Lˣ) (hω : ∀ x y, ω x y ^ p = 1)
    (hcoc : ∀ x y z, ω x y * ω y z = ω x z)
    (hπ0 : ∀ x y, x ≠ y → ω (π x) (π y) = ω x y ^ Q)
    {x₀ y₀ : Fin ν} (h1 : ω x₀ y₀ ≠ 1) :
    ∃ m : ℕ, 2 ≤ m ∧ m ≤ ν ∧ (p : ℤ) ∣ Q ^ m - 1 := by
  classical
  have hxx : ∀ x, ω x x = 1 := fun x => by
    have := hcoc x x x
    exact mul_left_cancel (a := ω x x) (this.trans (mul_one _).symm)
  have hπ : ∀ x y, ω (π x) (π y) = ω x y ^ Q := fun x y => by
    by_cases hxy : x = y
    · subst hxy
      rw [hxx, hxx, one_zpow]
    · exact hπ0 x y hxy
  have hneg : ∀ x y, ω y x = (ω x y)⁻¹ := fun x y => by
    have := hcoc x y x
    rw [hxx] at this
    exact (inv_eq_of_mul_eq_one_right this).symm
  have hne : x₀ ≠ y₀ := fun h => h1 (by rw [h]; exact hxx _)
  have hν2 : 2 ≤ ν := by
    have : 1 < Fintype.card (Fin ν) := Fintype.one_lt_card_iff.2 ⟨x₀, y₀, hne⟩
    have h1ν : 1 < ν := by simpa using this
    omega
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hQ1 : (p : ℤ) ∣ Q - 1
  · refine ⟨2, le_rfl, hν2, ?_⟩
    have : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_right hQ1 _
  set z : Fin ν := x₀ with hz
  set u : Fin ν → Lˣ := fun x => ω x z with hu
  have hωu : ∀ x y, ω x y = u x * (u y)⁻¹ := fun x y => by
    rw [hu, ← hneg y z, ← hcoc x z y]
  have hup : ∀ x, u x ^ p = 1 := fun x => hω x z
  set c : Lˣ := u (π z) * (u z ^ Q)⁻¹ with hc
  have hcu : ∀ x, u (π x) = c * u x ^ Q := fun x => by
    have h := hπ x z
    rw [hωu, hωu, mul_zpow, inv_zpow] at h
    rw [hc]
    calc u (π x) = (u (π x) * (u (π z))⁻¹) * u (π z) := (inv_mul_cancel_right _ _).symm
      _ = (u x ^ Q * (u z ^ Q)⁻¹) * u (π z) := by rw [h]
      _ = u (π z) * (u z ^ Q)⁻¹ * u x ^ Q := by ac_rfl
  have hzp : ∀ (g : Lˣ) (n : ℤ), g ^ p = 1 → (g ^ n) ^ p = 1 := fun g n hg => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  have hcp : c ^ p = 1 := by
    rw [hc, mul_pow, inv_pow, hzp _ _ (hup z), inv_one, mul_one]
    exact hup _
  have hcop : IsCoprime (p : ℤ) (Q - 1) :=
    ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hQ1
  obtain ⟨l, k, hlk⟩ := hcop
  set c' : Lˣ := c ^ k with hc'
  have hcc : c' ^ (Q - 1) = c := by
    rw [hc', ← zpow_mul]
    have h2 : k * (Q - 1) = 1 - (p : ℤ) * l := by linear_combination hlk
    rw [h2, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hcp, one_zpow, inv_one, mul_one]
  set v : Fin ν → Lˣ := fun x => u x * c' with hv
  have hvπ : ∀ x, v (π x) = v x ^ Q := fun x => by
    simp only [hv]
    rw [hcu x, mul_zpow]
    calc c * u x ^ Q * c' = c' ^ (Q - 1) * u x ^ Q * c' := by rw [hcc]
      _ = u x ^ Q * (c' ^ (Q - 1) * c') := by ac_rfl
      _ = u x ^ Q * c' ^ Q := by rw [zpow_sub_one, inv_mul_cancel_right]
  have hvp : ∀ x, v x ^ p = 1 := fun x => by
    simp only [hv]
    rw [mul_pow, hup x, hzp c k hcp, one_mul]
  have hvne : ∃ a, v a ≠ 1 := by
    by_contra hall
    push Not at hall
    apply h1
    have h3 : ω x₀ y₀ = v x₀ * (v y₀)⁻¹ := by
      rw [hωu]
      simp only [hv, ← div_eq_mul_inv]
      exact (mul_div_mul_right_eq_div _ _ _).symm
    rw [h3, hall x₀, hall y₀]
    simp
  obtain ⟨a, ha⟩ := hvne
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (v a) = p := orderOf_eq_prime (hvp a) ha
  have hiter : ∀ n : ℕ, v (π^[n] a) = v a ^ (Q ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', hvπ, ih, ← zpow_mul, pow_succ]
  have hper : a ∈ Function.periodicPts π := by
    obtain ⟨n, hn, hn1⟩ := (isOfFinOrder_of_finite π).exists_pow_eq_one
    refine ⟨n, hn, ?_⟩
    show π^[n] a = a
    rw [Equiv.Perm.iterate_eq_pow, hn1]
    rfl
  set m := Function.minimalPeriod π a with hm
  have hmpos : 0 < m := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hmper : π^[m] a = a := Function.isPeriodicPt_minimalPeriod π a
  have hdvd : (p : ℤ) ∣ Q ^ m - 1 := by
    have h4 : v a ^ (Q ^ m - 1) = 1 := by
      rw [zpow_sub_one, ← hiter m, hmper, mul_inv_cancel]
    have h5 := (orderOf_dvd_iff_zpow_eq_one.2 h4)
    rwa [hord] at h5
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    have hfix : π a = a := Function.minimalPeriod_eq_one_iff_isFixedPt.1 hm1
    apply hQ1
    have h4 : v a ^ (Q - 1) = 1 := by
      rw [zpow_sub_one, ← hvπ a, hfix, mul_inv_cancel]
    have h5 := (orderOf_dvd_iff_zpow_eq_one.2 h4)
    rwa [hord] at h5
  have hmle : m ≤ ν := by
    have := Function.minimalPeriod_le_card (f := π) (x := a)
    simpa using this
  exact ⟨m, hm2, hmle, hdvd⟩

theorem dvd_card_range_of_perfect_central {X G : Type*} [Group X] [Finite X] [Group G]
    (g : X →* G) (hperf : Group.IsPerfect X) (hker : g.ker ≤ Subgroup.center X) {p : ℕ}
    (hp : p.Prime) (hpX : p ∣ Nat.card X) : p ∣ Nat.card g.range := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  have hcen : ∀ x : X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ Subgroup.center X := by
    rintro x ⟨k, hk⟩
    apply hker
    rw [MonoidHom.mem_ker]
    have hgx : (g x) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    by_contra hne
    have hord : orderOf (g x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hgx
    obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow hp).1 hord
    have hj0 : j ≠ 0 := fun h => hne (orderOf_eq_one_iff.1 (by rw [hjo, h]; simp))
    have hpo : p ∣ orderOf (g x) := by rw [hjo]; exact dvd_pow_self p hj0
    have hmem : g x ∈ g.range := ⟨x, rfl⟩
    have h2 : orderOf (g x) ∣ Nat.card g.range := by
      have := orderOf_dvd_natCard (⟨g x, hmem⟩ : g.range)
      rwa [Subgroup.orderOf_mk] at this
    exact hnd (hpo.trans h2)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) p hpX
  have hxc : x ∈ commutator X := by
    rw [Group.isPerfect_def.1 hperf]
    exact Subgroup.mem_top x
  have hxp : x ^ (p ^ 1) = 1 := by rw [pow_one, ← hx]; exact pow_orderOf_eq_one x
  have h1 := eq_one_of_mem_commutator_of_central_pElements hcen hxc ⟨1, hxp⟩
  rw [h1, orderOf_one] at hx
  exact hp.one_lt.ne hx

theorem commutator_range_eq_of_perfect {X G : Type*} [Group X] [Group G] (g : X →* G)
    (hperf : Group.IsPerfect X) : ⁅g.range, g.range⁆ = g.range := by
  have h1 : g.range = (⊤ : Subgroup X).map g := MonoidHom.range_eq_map g
  rw [h1, ← Subgroup.map_commutator, ← commutator_def, Group.isPerfect_def.1 hperf]

theorem perfect_range_dvd_of_central {X G : Type*} [Group X] [Finite X] [Group G]
    (g : X →* G) (hperf : Group.IsPerfect X) (hker : g.ker ≤ Subgroup.center X) {p : ℕ}
    (hp : p.Prime) (hpX : p ∣ Nat.card X) :
    ⁅g.range, g.range⁆ = g.range ∧ p ∣ Nat.card g.range :=
  ⟨commutator_range_eq_of_perfect g hperf, dvd_card_range_of_perfect_central g hperf hker hp hpX⟩

theorem nat_dvd_pow_sub_one_of_int {p N m : ℕ} (hN : 1 ≤ N)
    (h : (p : ℤ) ∣ (N : ℤ) ^ m - 1) : p ∣ N ^ m - 1 := by
  have h1 : 1 ≤ N ^ m := Nat.one_le_pow _ _ hN
  have h2 : ((N ^ m - 1 : ℕ) : ℤ) = (N : ℤ) ^ m - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  exact Int.natCast_dvd_natCast.1 (h2 ▸ h)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

end
