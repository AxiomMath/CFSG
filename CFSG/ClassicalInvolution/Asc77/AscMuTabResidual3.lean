module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual
public import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual2
public import CFSG.ClassicalInvolution.Asc77.AscMuTabG2
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTD4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected

namespace MuTab

theorem muResidualG2D4_proved (p f : ℕ) [Fact p.Prime] : MuResidualG2D4 p f where
  g2 hp2 hq X _ _ Φ hS hne _ hL := by
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    exact g2_omegaStarNbr_nonempty M hS.hyp hp2 hq hne
  trialityD4 hp2 hq X _ _ Φ hS hne _ hL := by
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    exact td4_omegaStarNbr_nonempty M hS.hyp hp2 hq hne

theorem muResidual_of_d4Star {p f : ℕ} [Fact p.Prime] (hD4 : Ih8D4Star p f) : MuResidual p f where
  pOmegaOdd3 hp2 hq hπ X _ _ Φ hS hne _ hL := by
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    exact split_pOmegaOdd3_minus M hS.hyp hp2 hq hne (pow_mod_four_of_piSign_false hp2 hπ)
  pOmegaMinus4 hp2 hq hπ X _ _ Φ hS hne _ hL := by
    obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieType hS hL
    exact split_pOmegaMinus4_minus M hS.hyp hp2 hq hne (pow_mod_four_of_piSign_false hp2 hπ)
  g2 := (muResidualG2D4_proved p f).g2
  trialityD4 := (muResidualG2D4_proved p f).trialityD4
  pOmegaPlus4 := smallShape_pOmegaPlus4_of hD4

end MuTab

variable {p f : ℕ} [Fact p.Prime]

theorem ih8MuTableSect_of_d4Star (hD4 : Ih8D4Star p f) : Ih8MuTableSect p f :=
  ih8MuTableSect_of_g2d4 hD4 (MuTab.muResidualG2D4_proved p f)

theorem ih8MuTable_of_d4Star (hD4 : Ih8D4Star p f) : Ih8MuTable p f :=
  ih8MuTable_of_g2d4 hD4 (MuTab.muResidualG2D4_proved p f)

end CFSG.ClassicalInvolution.Asc77
