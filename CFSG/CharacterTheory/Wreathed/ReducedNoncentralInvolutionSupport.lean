module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Wreathed.ReducedInvolution

theorem two_pow_dvd_sub_one {s e : ℕ} {n : ℤ} (he : Odd e) (h : (2 : ℤ) ^ s ∣ n ^ e - 1) :
    (2 : ℤ) ^ s ∣ n - 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [pow_zero]
    exact one_dvd _
  have h2 : (2 : ℤ) ∣ n ^ e - 1 := (dvd_pow_self 2 hs.ne').trans h
  have hn : Odd n := by
    have hodd : Odd (n ^ e) := by
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, by linarith⟩
    exact (Int.odd_pow.mp hodd).resolve_right he.pos.ne'
  have hS : ¬ (2 : ℤ) ∣ ∑ i ∈ Finset.range e, n ^ i := by
    intro hdvd
    have hdvd' : ((2 : ℕ) : ℤ) ∣ ∑ i ∈ Finset.range e, n ^ i := by exact_mod_cast hdvd
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdvd'
    have hn1 : (n : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hn
    simp only [Int.cast_sum, Int.cast_pow, hn1, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at h0
    rw [ZMod.natCast_eq_one_iff_odd.mpr he] at h0
    exact one_ne_zero h0
  rw [← geom_sum_mul] at h
  exact Int.prime_two.pow_dvd_of_dvd_mul_left s hS h

theorem fix_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (ψ : G →* G) {e : ℕ} (he : Odd e)
    (hψ : ∀ g, ψ^[e] g = g) {t : G} {s : ℕ} (ht : t ^ 2 ^ s = 1) : ψ t = t := by
  obtain ⟨n, hn⟩ := ψ.map_cyclic
  have hiter : ∀ (j : ℕ) (g : G), ψ^[j] g = g ^ (n ^ j) := by
    intro j
    induction j with
    | zero =>
      intro g
      rw [Function.iterate_zero_apply, pow_zero, zpow_one]
    | succ j ih =>
      intro g
      rw [Function.iterate_succ_apply', ih, hn, ← zpow_mul, pow_succ]
  have h1 : t ^ (n ^ e - 1) = 1 := by
    have h := hψ t
    rw [hiter] at h
    rw [zpow_sub_one, h, mul_inv_cancel]
  have hord : (orderOf t : ℤ) ∣ n ^ e - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  obtain ⟨r, -, hrt⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ht)
  rw [hrt] at hord
  push_cast at hord
  have h3 : t ^ (n - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hrt]
    push_cast
    exact two_pow_dvd_sub_one he hord
  rw [hn, ← mul_inv_eq_one, ← zpow_sub_one, h3]

theorem odd_card_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, Odd (orderOf g)) : Odd (Nat.card G) := by
  by_contra hc
  have h2 : 2 ∣ Nat.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hc)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx' := h x
  rw [hx] at hx'
  exact (Nat.not_odd_iff_even.mpr even_two) hx'

theorem eq_one_of_pow_two_pow {G : Type*} [Monoid G] {g : G} {s : ℕ} (hg : g ^ 2 ^ s = 1)
    (hodd : Odd (orderOf g)) : g = 1 := by
  have hcop : (orderOf g).Coprime (2 ^ s) :=
    Nat.Coprime.pow_right s (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hg))

theorem oddCore_map_le {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    (CFSG.oddCore G).map e.toMonoidHom ≤ CFSG.oddCore G' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  refine ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective]
  exact hN.2

theorem oddCore_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    (CFSG.oddCore G).map e.toMonoidHom = CFSG.oddCore G' := by
  refine le_antisymm (oddCore_map_le e) fun x hx => ?_
  rw [Subgroup.mem_map_equiv]
  exact oddCore_map_le e.symm (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx)

end CFSG.Wreathed.ReducedInvolution
