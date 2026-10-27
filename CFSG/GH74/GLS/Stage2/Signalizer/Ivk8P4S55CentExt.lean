module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

theorem eq_one_of_pow_pow_of_pow {G : Type*} [Group G] {w : G} {r n z : ℕ}
    (hrz : Nat.Coprime r z) (h1 : w ^ r ^ n = 1) (h2 : w ^ z = 1) : w = 1 := by
  have h : orderOf w ∣ Nat.gcd (r ^ n) z :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [(Nat.Coprime.pow_left n hrz).gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

theorem exists_sylow_rmax_of_isNilpotent (G : Type*) [Group G] [Finite G] [Group.IsNilpotent G]
    {r : ℕ} (hr : r.Prime) :
    ∃ Q : Sylow r G, ∀ g : G, (∃ n : ℕ, g ^ r ^ n = 1) → g ∈ (Q : Subgroup G) := by
  have := Fact.mk hr
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r G))
  refine ⟨Q, fun g ⟨n, hn⟩ => ?_⟩
  have hg : IsPGroup r (zpowers g) := by
    have hd : orderOf g ∣ r ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hr).mp hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  obtain ⟨Q', hQ'⟩ := hg.exists_le_sylow
  have : Unique (Sylow r G) := Sylow.unique_of_normal Q inferInstance
  have hQQ : Q' = Q := Subsingleton.elim _ _
  rw [← hQQ]
  exact hQ' (mem_zpowers g)

theorem map_sylow_eq_top_of_isPGroup {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {r : ℕ} [Fact r.Prime] (f : G →* H) (hf : Function.Surjective f) (hH : IsPGroup r H)
    (Q : Sylow r G) : (Q : Subgroup G).map f = ⊤ := by
  rw [← Sylow.coe_mapSurjective hf Q]
  obtain ⟨n, hn⟩ := hH.index (Q.mapSurjective hf : Subgroup H)
  have hnd := (Q.mapSurjective hf).not_dvd_index
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero] at hn
    exact Subgroup.index_eq_one.mp hn
  · exact absurd (hn ▸ dvd_pow_self r hpos.ne') hnd

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
