module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInnerY
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (quadOdd nondegenerate_quadOdd)

abbrev Sec4IV : Type := Fin 3 ⊕ Fin 3 ⊕ Unit → ZMod 3

noncomputable abbrev Sec4IQ : QuadraticForm (ZMod 3) Sec4IV := quadOdd 3 (ZMod 3)

theorem sec4IQ_nondegenerate : Sec4IQ.Nondegenerate := nondegenerate_quadOdd 3 (ZMod 3)

theorem sec4IQ_finrank : Module.finrank (ZMod 3) Sec4IV = 7 := by
  rw [Module.finrank_fintype_fun_eq_card]
  decide

theorem sec4IQ_quadSign : quadSign Sec4IQ = 1 := quadSign_quadOdd 3

noncomputable abbrev Sec4IOmega : Subgroup (ProjOrth Sec4IQ) :=
  omegaProj sec4IQ_nondegenerate

theorem sec4I_center_eq_oddCore {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsOmega7Group L) : Subgroup.center ↥L = oddCore ↥L :=
  center_eq_oddCore_of_simple hL.1 (sec4_isSimpleGroup_quotient_oddCore hL)

theorem sec4I_exists_model {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsOmega7Group L) : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) := by
  have hcen := sec4I_center_eq_oddCore hL
  obtain ⟨e⟩ := (isOmegaStar_of_lieModel_odd hL.2).nonempty_equiv (by norm_num : 2 ≤ 7)
    sec4IQ_nondegenerate sec4IQ_finrank sec4IQ_quadSign
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans e⟩

@[expose] noncomputable def sec4ICover {G : Type} [Group G] {L : Subgroup G}
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) : ↥L →* Sec4IOmega :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem sec4ICover_apply {G : Type} [Group G] {L : Subgroup G}
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (l : ↥L) :
    sec4ICover e l = e (QuotientGroup.mk l) := rfl

theorem sec4ICover_odd {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) : OddCentralCover (sec4ICover e) := by
  have hcen := sec4I_center_eq_oddCore hL
  have h := oddCentralCover_quotient_oddCore hL.1
    ((QuotientGroup.quotientMulEquivOfEq hcen.symm).trans e)
  convert h using 1
  ext l
  rfl

end CFSG.OddStandard.SmallF3.Omega
