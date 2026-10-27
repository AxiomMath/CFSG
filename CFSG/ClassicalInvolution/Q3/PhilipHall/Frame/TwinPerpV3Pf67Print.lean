module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWBridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson

section PrintedW

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G}

theorem exists_printedWT (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    ∃ W : Subgroup G, TwinThmEW.PrintedWT Ω K W ∧ K ⊓ W ∈ USet Ω := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  obtain ⟨R', hR', hR'fix⟩ := exists_sylow_normalized hR₀.2.1 (hR₀.1.trans hKN)
  have hRn : R₀ ≤ Subgroup.normalizer (R' : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix r hr)
  have h2 : IsPGroup 2 ↥(R₀ ⊔ R') := hR₀.2.1.to_sup_of_normal_right' hR'.2.1 hRn
  obtain ⟨S, hS⟩ := h2.exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hWS : (⨆ U ∈ η, U : Subgroup G) ≤ (S : Subgroup G) :=
    iSup₂_le fun U hU => (hη.1 hU).2
  have hW : (⨆ U ∈ η, U : Subgroup G) ∈ WSet Ω := ⟨η, ⟨S, hη, hηinv⟩, rfl⟩
  refine ⟨⨆ U ∈ η, U, ⟨S, R₀, hR₀, le_sup_left.trans hS, hW, hWS,
    fun s hs => T7A.conjSub_eta_eq hηinv hs, K', hK', hne, R', mem_RSet_of_isSylow2In hK'Ω hR',
    hR'.1, le_sup_right.trans hS⟩, ?_⟩
  exact TwinThmEW.inf_W_mem_USet' hΩ hW hWS hK (mem_RSet_of_isSylow2In hK hR₀) hR₀.1
    (le_sup_left.trans hS)

end PrintedW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
