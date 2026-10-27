module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Path

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Equiv

theorem classicalInvolutionOddCore_map_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) :
    (classicalInvolutionOddCore A).map e.toMonoidHom = classicalInvolutionOddCore B := by
  apply le_antisymm
  · exact le_sSup ⟨(inferInstance : (classicalInvolutionOddCore A).Normal).map _ e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]
         exact CFSG.ComponentClassification.OddCore.odd_card A⟩
  · have hle : (classicalInvolutionOddCore B).map e.symm.toMonoidHom ≤ classicalInvolutionOddCore A :=
      le_sSup ⟨(inferInstance : (classicalInvolutionOddCore B).Normal).map _ e.symm.surjective,
        by rw [Subgroup.card_map_of_injective e.symm.injective]
           exact CFSG.ComponentClassification.OddCore.odd_card B⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

end Equiv

section Bridge

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem coreHull_map_eq_rLayer (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    (coreHull Ω c).map (Subgroup.centralizer ({c} : Set G)).subtype = rLayer Ω c := by
  refine le_antisymm (coreHull_map_le_rLayer hΩ hc2) ?_
  unfold rLayer
  refine iSup₂_le fun R' hR' => iSup_le fun hRc => ?_
  obtain ⟨J, hJΩ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hJ : J ∈ tqMembers3 Ω c :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨R', hRJ, hRc⟩⟩
  have hRs : IsSylow2In R' (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hRJ, hRc⟩
  intro a ha
  have haC : a ∈ Subgroup.centralizer ({c} : Set G) := hRc ha
  have haH : (⟨a, haC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c :=
    le_coreHull hJ (Subgroup.mem_subgroupOf.mpr (hRs.1 ha))
  exact ⟨⟨a, haC⟩, haH, rfl⟩

@[expose] noncomputable def hullEquiv (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set G)).subtype = rLayer Ω c) :
    ↥(coreHull Ω c) ≃* ↥(rLayer Ω c) :=
  (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hmap)

theorem hullEquiv_coe (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set G)).subtype = rLayer Ω c)
    (h : ↥(coreHull Ω c)) : ((hullEquiv hmap h : ↥(rLayer Ω c)) : G) = (((h : ↥(Subgroup.centralizer ({c} : Set G)))) : G) :=
  rfl

@[expose] noncomputable def secEquiv (hmap : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set G)).subtype = rLayer Ω c) :
    (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ≃* SecQuot (rLayer Ω c) :=
  QuotientGroup.congr _ _ (hullEquiv hmap) (classicalInvolutionOddCore_map_equiv (hullEquiv hmap))

theorem rLayer_le_centralizer (Ω : Set (Subgroup G)) (c : G) : rLayer Ω c ≤ Subgroup.centralizer ({c} : Set G) :=
  iSup₂_le fun R' _ => iSup_le fun hR => hR

end Bridge

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
