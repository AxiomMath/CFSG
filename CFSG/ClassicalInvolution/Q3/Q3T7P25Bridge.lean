module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25A05
public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T7

section Bridge


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem std7_of_three (h : Std7Three Ω K K' z) : Q3T8.Asc77.Std7 Ω K K' z where
  stand := Q3T8.Asc77.AscStand.of_stand3 h.stand h.rank (fun h4 => h.cex (Or.inr h4))
  disconnected := h.disconnected
  hz := h.hz
  hK' := h.hK'
  hne := h.hne
  cex := h.cex

theorem hyp23_of_three (h : Hyp23Three Ω K K' z) : Q3T8.Asc77.Hyp23 Ω K K' z :=
  ⟨std7_of_three h.1, h.2⟩

theorem c25_16_proved : Q3T8.Asc77.C25_16 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS hF
  obtain ⟨-, -, Q, R₀, -, hQq, hR₀, hcard⟩ := hF
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hyp.hR'.1
  have h8 : Nat.card R' = 8 := natCard_isSylow2In_member hyp.std.1.stand.modU hJ hRJ
  have hle : Nat.card R₀ ≤ Nat.card R' := Subgroup.card_le_of_le hR₀.1
  have hQ8 := hQq.eight_le
  omega

abbrev C25_11Three : Prop := Q3T8.Asc77.C25_11

theorem c25_E4Three_of_c25_11 (h11 : C25_11Three) : C25_E4Three := by
  intro G _ _ _ Ω K K' z hyp W hW hzW hE4
  exact Q3T8.Asc77.T7Q.c25_E4_of_11_16 h11 c25_16_proved G Ω K K' z (hyp23_of_three hyp) W hW
    hzW hE4

end Bridge

end CFSG.ClassicalInvolution.Q3.Q3T7P25
