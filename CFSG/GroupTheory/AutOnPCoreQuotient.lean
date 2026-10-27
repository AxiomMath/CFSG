module

public import CFSG.Quasithin.Background.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.Quasithin Subgroup

variable {Ω : Type*} [Group Ω]

private lemma conjAct_ker_aoq (W : Subgroup Ω) :
    (conjAct W).ker = (Subgroup.centralizer (W : Set Ω)).subgroupOf
      (Subgroup.normalizer (W : Set Ω)) := by
  rw [conjAct, ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
    Subgroup.comap_inclusion_subgroupOf]

private lemma quotientKerEquivRange_mk_aoq {B W : Subgroup Ω}
    (ψ : ↥B →* MulAut ↥W) (b : ↥B) :
    ((QuotientGroup.quotientKerEquivRange ψ (QuotientGroup.mk b) : ↥ψ.range) :
      MulAut ↥W) = ψ b := by
  show ((QuotientGroup.rangeKerLift ψ (QuotientGroup.mk b) : ↥ψ.range) :
    MulAut ↥W) = ψ b
  rfl

theorem exists_quotient_pCore_mulEquiv_autOn {B W : Subgroup Ω}
    (hBW : B ≤ normalizer (W : Set Ω)) (hker : B ⊓ centralizer (W : Set Ω) = pCoreOf 2 B) :
    ∃ φ : (↥B ⧸ CFSG.pCore 2 ↥B) ≃* ↥(autOn B W), ∀ b : ↥B,
      ((φ (b : ↥B ⧸ CFSG.pCore 2 ↥B) : ↥(autOn B W)) : MulAut ↥W) =
        conjAct W ⟨b, hBW b.2⟩ := by
  let ψ : ↥B →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hBW)
  have h2 : ψ.range = autOn B W := by
    rw [show ψ = (conjAct W).comp (Subgroup.inclusion hBW) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range]
    rfl
  have h3 : ψ.ker = CFSG.pCore 2 ↥B := by
    have hψker : ψ.ker = (Subgroup.centralizer (W : Set Ω)).subgroupOf B := by
      rw [show ψ = (conjAct W).comp (Subgroup.inclusion hBW) from rfl,
        ← MonoidHom.comap_ker, conjAct_ker_aoq, Subgroup.comap_inclusion_subgroupOf]
    rw [hψker, ← Subgroup.inf_subgroupOf_left (H := Subgroup.centralizer (W : Set Ω)) (K := B),
      hker, pCoreOf]
    exact Subgroup.comap_map_eq_self_of_injective B.subtype_injective (CFSG.pCore 2 ↥B)
  refine ⟨(QuotientGroup.quotientMulEquivOfEq h3.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr h2)), ?_⟩
  intro b
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    MulEquiv.subgroupCongr_apply, quotientKerEquivRange_mk_aoq]
  rfl

end CFSG.GroupTheory
