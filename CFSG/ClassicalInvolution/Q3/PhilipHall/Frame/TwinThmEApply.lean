module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscThmE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmE

section Apply

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_estandQ8 {K K' : Subgroup G} (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hTwo : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hih : EIH (Nat.card G)) (hK : K ∈ Ω) (hA : AEmpty Ω K) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    ∃ (S : Sylow 2 G) (R W : Subgroup G), EStandQ8 Ω K S R W := by
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
  refine ⟨S, R₀, ⨆ U ∈ η, U, ?_⟩
  refine
    { hyp := hΩ
      cls := hcls
      q8 := hq8
      two := hTwo
      ih := hih
      mem := hK
      aEmpty := hA
      twin := ⟨K', hK', hne, R', mem_RSet_of_isSylow2In hK'Ω hR', hR'.1,
        le_sup_right.trans hS⟩
      hR := ⟨mem_RSet_of_isSylow2In hK hR₀, hR₀.1, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, ?_, fun s hs => T7A.conjSub_eta_eq hηinv hs⟩ }
  exact iSup₂_le fun U hU => (hη.1 hU).2

end Apply

section TwinCore

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

@[expose] def TwinThmEP (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n → TwinDisc.TwinThmE n

end TwinCore

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
