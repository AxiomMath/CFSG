module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.PerfectQuotient
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Subgroup

theorem three_dvd_card_map_of_perfect {G P : Type*} [Group G] [Group P] [Finite G]
    (π : G →* P) (hker : π.ker ≤ center G) {B : Subgroup G} (hB : ⁅B, B⁆ = B)
    (h3 : 3 ∣ Nat.card B) : 3 ∣ Nat.card (B.map π) := by
  let f : B →* P := π.comp B.subtype
  have hrange : f.range = B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker' : f.ker ≤ center B := by
    intro g hg
    rw [mem_center_iff]
    intro h
    have hg' : π (g : G) = 1 := hg
    have hc : (g : G) ∈ center G := hker hg'
    exact Subtype.ext ((mem_center_iff.1 hc) (h : G))
  have hperf : commutator B = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hB)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := dvd_card_quotient_of_perfect (p := 3) hperf h3 (N := f.ker) hker'
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h

end CFSG.HardMathSupport.Malle.E27Lie
