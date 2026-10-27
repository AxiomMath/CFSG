module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DObj
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3LeviG
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2G1Fac
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Matrix CFSG.Fischer Subgroup
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (conjR msigma pstd)
open scoped MatrixGroups

theorem chi0_dωS : chi0 YamadaN2.dωS = yamWord [16, 3, 16, 2, 3, 16, 3] := by
  apply Subtype.ext
  apply Subtype.ext
  decide +kernel

section Model

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

theorem chiG_dωS_mem : chiG e YamadaN2.dωS ∈ sK₂ e := by
  rw [chiG, MonoidHom.comp_apply, chi0_dωS]
  exact gw_mem_ch (c := chK2) (w := [16, 3, 16, 2, 3, 16, 3]) (by decide)

theorem chiG_mem_sS {A : msigma F4} (hA : (A : SL(4, F4)) ∈ pstd F4) : chiG e A ∈ sS e := by
  have h : chiG e A ∈ sS e ⊓ conjR (sS e) (sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0) := by
    rw [S_u₁_eq, chiG, MonoidHom.comp_apply, phiG_mem_toG]
    exact psiChi_mem_T1 hA
  exact h.1

theorem exists_k1Model (e : L ≃* T46) (t : G) : ∃ χ : msigma F4 ≃* (sec3DData e t).K₁,
    (∀ A : msigma F4, (A : SL(4, F4)) ∈ pstd F4 → (χ A : G) ∈ sS e) ∧
      (χ YamadaN2.dωS : G) ∈ sK₂ e :=
  ⟨(MonoidHom.ofInjective chiG_injective).trans (MulEquiv.subgroupCongr range_chiG),
    fun _ hA => chiG_mem_sS hA, chiG_dωS_mem⟩

end Model

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
