module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem smul_eq_of_normal_coprime [IsPretransitive G Ω] {p : ℕ}
    (hΩ : Nat.card Ω = p) (N : Subgroup G) [N.Normal] [Finite N]
    (hN : Nat.Coprime p (Nat.card N)) (n : G) (hn : n ∈ N) (ω : Ω) : n • ω = ω := by
  have hblock : IsBlock G (orbit N ω) := IsBlock.orbit_of_normal ω
  have hne : (orbit N ω).Nonempty := ⟨ω, mem_orbit_self ω⟩
  have h1 : (orbit N ω).ncard ∣ p := hΩ ▸ hblock.ncard_dvd_card hne
  have h2 : (orbit N ω).ncard ∣ Nat.card N := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  have h3 : (orbit N ω).ncard = 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [Nat.Coprime.gcd_eq_one (by rw [Nat.Coprime] at hN; exact hN), Nat.dvd_one] at this
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h3
  have h4 : ω ∈ orbit N ω := mem_orbit_self ω
  have h5 : (⟨n, hn⟩ : N) • ω ∈ orbit N ω := mem_orbit ω _
  rw [ha, Set.mem_singleton_iff] at h4 h5
  exact h5.trans h4.symm

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
