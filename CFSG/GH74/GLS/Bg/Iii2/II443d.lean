module

public import CFSG.GH74.GLS.Bg.Iii2.Statements
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.ABGLocalTools

theorem ii4_43d_of (h44 : II4_44) (hAut : II4_Aut) : II4_43d := by
  intro G _ _ hG x hx K hK u huu hux huN P hP hPu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsSL2Or2A7 (Hat K) := h44 G hG x hx K hK.1.1.2.2 hK.2
  have hφ2 : phi K u huN * phi K u huN = 1 := phi_mul_self K huN huu
  have hS : IsSylow2In P K := isSylowOf_iff.1 hP
  have hS' : IsSylow2In (hatImg K P) (⊤ : Subgroup (Hat K)) := isSylow2In_hatImg hS
  have hfix : ∀ q ∈ hatImg K P, phi K u huN q = q := by
    intro q hq
    obtain ⟨a, haP, rfl⟩ := mem_hatImg.1 hq
    rw [phi_mk]
    congr 1
    apply Subtype.ext
    have := hPu a haP
    show u * (a : G) * u⁻¹ = a
    rw [this]
    group
  by_contra hne
  have hφ1 : phi K u huN ≠ 1 := fun h => hne ((phi_eq_one_iff K huN).mp h)
  obtain ⟨w, hw, hw4, hww⟩ := ((hAut (Hat K) hQ).2.2 (phi K u huN) hφ2).1 hφ1 (hatImg K P) hS'
    (fun q hq => by rw [hfix q hq]; exact hq)
  rw [hfix w hw] at hww
  have hw2 : w ^ 2 = 1 := by
    have : w * w = 1 := mul_eq_one_iff_eq_inv.2 hww
    rw [sq]
    exact this
  have := orderOf_dvd_of_pow_eq_one hw2
  rw [hw4] at this
  omega

end CFSG.GH74.GLS.Bg.Iii2
