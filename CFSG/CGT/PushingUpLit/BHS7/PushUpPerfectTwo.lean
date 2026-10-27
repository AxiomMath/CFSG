module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightGaps
public import CFSG.CGT.PushingUpLit.BHS7.CoverCampbell
public import CFSG.CGT.PushingUpLit.BHS.ThreeEight

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Lift.Piece CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

theorem pushUpPerfectTwo_holds : PushUpPerfectTwo := by
  intro Γ _ _ G T V P' α β hG hT hne hVn hVT hVQ hα hαk hβ hβe hβk hP'G hSP' hVP' hSylP'
    hminP' hcharP' hαP' hnc hTSC hJS hchi hlin
  classical
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_le' hVQ (isElemAbelian_omegaOneCenterOf' _)
  have hVnP' : P' ≤ Subgroup.normalizer (V : Set Γ) := hP'G.trans hVn
  obtain ⟨hαP'', hαkP', hβeP', hβkP'⟩ := natural_data_restrict α hαk β hβe hβk hP'G hαP'
  obtain ⟨M', ρ', hρ', hset⟩ := exists_natQuotSetting_of_isMinParabolic2 hminP' hVP' hVe hVnP'
    (α.comp (Subgroup.inclusion hP'G)) hαP'' hαkP' β hβ hβeP' hβkP'
  have hchar : CharTwo (⊤ : Subgroup ↥P') := charTwo_top_of_charTwo' hcharP'
  have hnc' : NoCharNormal ((baum T).subgroupOf P') (⊤ : Subgroup ↥P') :=
    noCharNormal_top_subgroupOf' hSP' hnc
  have hJ' : ⁅elemThompsonIn 2 ((baum T).subgroupOf P'), V.subgroupOf P'⁆ ≠ ⊥ :=
    commutator_thompson_ne_bot hSP' hVP' hJS
  obtain ⟨n, hn, hcard⟩ := card_eq_two_pow (k := GaloisField 2 2)
  have hBB : elemBaumannIn 2 ((baum T).subgroupOf P') = (baum T).subgroupOf P' := by
    have h1 := C56.elemBaumannIn_subgroupOf_map hSP'
    rw [C1GN.baum_baum] at h1
    have h2 : ((baum T).subgroupOf P').map P'.subtype = baum T :=
      Subgroup.map_subgroupOf_eq_of_le hSP'
    exact Subgroup.map_injective P'.subtype_injective (h1.trans h2.symm)
  have hGb : baumannOvergroup ((baum T).subgroupOf P') = ⊤ := by
    unfold baumannOvergroup
    rw [hBB]
    apply Subgroup.map_injective P'.subtype_injective
    rw [Subgroup.map_sup, map_oddOrderSubgroup_top, Subgroup.map_subgroupOf_eq_of_le hSP',
      ← twoResidual_eq_oddOrderSubgroup, sup_comm, sup_twoResidual_eq hSylP']
    exact (Subgroup.range_subtype P').symm.trans (MonoidHom.range_eq_map _)
  have hQU := natural_blockQ_le_blockU hset hchar hnc' hJ' hn hcard hGb
  have hf : Function.Injective P'.subtype := P'.subtype_injective
  have hEeq : (oddOrderSubgroup (⊤ : Subgroup ↥P')).map P'.subtype = twoResidual P' := by
    rw [map_oddOrderSubgroup_top, twoResidual_eq_oddOrderSubgroup]
  have hQU' : blockQ (twoResidual P') ≤ blockU (twoResidual P') := by
    have h1 := Subgroup.map_mono (f := P'.subtype) hQU
    rwa [← blockQ_map_injective P'.subtype hf, ← blockU_map_injective P'.subtype hf, hEeq] at h1
  exact le_antisymm (CFSG.QuasithinUnique.C1.blockU_le_blockQ hchi.1.1) hQU'

end CFSG.CGT.PushingUpLit.BHS7
