module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

open Subgroup

theorem injective_of_perfect_central {E S T : Type} [Group E] [Group S] [Group T] [IsSimpleGroup S]
    (π : E →* S) (hπ : Function.Surjective π) (hc : π.ker ≤ center E)
    (hperf : commutator E = ⊤) (hcard : Nat.card π.ker = 3) (f : E →* T) {z : E}
    (hz : z ∈ π.ker) (hfz : f z ≠ 1) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hfin : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hnorm : (f.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map π) with hbot | htop
  · have hle : f.ker ≤ π.ker := by
      intro x hx
      have h1 := Subgroup.mem_map_of_mem π hx
      rw [hbot, Subgroup.mem_bot] at h1
      exact h1
    have hdvd : Nat.card f.ker ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le hle
    have hp : Nat.Prime 3 := Nat.prime_three
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · have heq : f.ker = π.ker := Subgroup.eq_of_le_of_card_ge hle (by omega)
      exact absurd ((MonoidHom.mem_ker).1 (heq ▸ hz)) hfz
  · exfalso
    have hsup : f.ker ⊔ π.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : π x ∈ f.ker.map π := htop ▸ mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have hnk : n⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
      have : x = n * (n⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hn hnk
    have hcomm : commutator E ≤ f.ker := by
      rw [_root_.commutator_def]
      calc ⁅(⊤ : Subgroup E), ⊤⁆ = ⁅f.ker ⊔ π.ker, f.ker ⊔ π.ker⁆ := by rw [hsup]
        _ = ⁅f.ker, f.ker ⊔ π.ker⁆ ⊔ ⁅π.ker, f.ker ⊔ π.ker⁆ :=
          commutator_sup_right _ _ _
        _ ≤ f.ker := by
          refine sup_le (commutator_le_left _ _) ?_
          calc ⁅π.ker, f.ker ⊔ π.ker⁆ ≤ ⁅center E, f.ker ⊔ π.ker⁆ := commutator_mono_left hc
            _ = ⊥ := commutator_center_left _
            _ ≤ f.ker := bot_le
    rw [hperf] at hcomm
    exact hfz ((MonoidHom.mem_ker).1 (hcomm (mem_top z)))

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
