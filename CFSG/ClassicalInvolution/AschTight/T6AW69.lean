module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen69
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.T6A

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem w69 (p f : ℕ) [Fact p.Prime] : Asc77.W69 p f := by
  intro G _ _ _ Ω K hs S
  have hΩ : HypOmegaGen Ω := hypOmegaGen_of_mod hs.odd hs.five hs.hyp
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.T6A
