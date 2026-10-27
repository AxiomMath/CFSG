module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGA5
public import CFSG.Sporadic.Schreier.J1OddCore

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5

theorem footeKnownSmall_J1
    (G : Type) [Group G] [Finite G]
    (hG : Blueprint.NativeSporadic.IsSporadic G .J1) : FooteKnownSmall G := by
  have hG' : Nonempty (G ≃* Blueprint.NativeSporadic.J1) := hG
  obtain ⟨e⟩ := id hG'
  have hcardG : Nat.card G = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    obtain ⟨-, -, -, -, -, -, -, -, h⟩ := Sporadic.Schreier.fam_j1_order
    exact h
  refine footeKnownSmall_of_alt5 (c := 120)
    (fun t ht => (Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free hG' t ht).2.2.1)
    (fun t ht => by
      rw [(Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free hG' t ht).1])
    (eq_of_isSmallOrder_dvd (q₁ := 16) (by norm_num) (by norm_num) (by decide) (by norm_num)
      (by norm_num))
    (pRank_le_of_not_dvd (by rw [hcardG]; norm_num))

end CFSG.ComponentClassification.FooteLit.KG
