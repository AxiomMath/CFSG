module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6EdgeFrame
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg TauCeti.GLSymplecticFin
open CFSG.LieType.Universal.Symplectic.SpExtras (elt)
open CFSG.Timmesfeld.LieEmbed (c3ToF4)
open CFSG.Assembly.LowTwoRank (StatedSp StatedOmega StatedQuadPlus)
open CFSG.SeitzReduction.SymplecticPilot (q2OmIota)

local instance f4PilotQ2TwistedE6EdgeFrameNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩


section YParam

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {X₀ : Subgroup (adjointGroup .F4 K)}

theorem twTrans_graphAutF4_symm_symm_apply (e : L ≃* adjointGroup .F4 K)
    (m : adjointGroup .F4 K) :
    (e.trans (graphAutF4 K).symm).symm m = e.symm (graphAutF4 K m) := by
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm]

variable (e : L ≃* adjointGroup .F4 K) (g : adjointGroup .F4 K)

@[expose] noncomputable def twEdgeYParam
    (Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) :
    StatedOmega (StatedQuadPlus (3 + 1) K) →* G :=
  (MulAut.conj ((e.symm g : L) : G)).toMonoidHom.comp
    ((centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)).subtype.comp
      Φ₁.toMonoidHom)

variable {e g}

theorem twEdgeYParam_apply
    (Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))
    (y : StatedOmega (StatedQuadPlus (3 + 1) K)) :
    twEdgeYParam e g Φ₁ y = ((e.symm g : L) : G) * (Φ₁ y : G) * ((e.symm g : L) : G)⁻¹ :=
  rfl

theorem twEdgeYParam_injective
    (Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) :
    Function.Injective (twEdgeYParam e g Φ₁) :=
  (MulAut.conj _).injective.comp (Subtype.val_injective.comp Φ₁.injective)

theorem twEdgeYParam_iota {ι : StatedSp 3 K →* StatedOmega (StatedQuadPlus (3 + 1) K)}
    {Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)}
    (hΦ₁ : IsTwoGraphParam (e.trans (graphAutF4 K).symm) X₀ ι Φ₁) (s : StatedSp 3 K) :
    twEdgeYParam e g Φ₁ (ι s) =
      ((e.symm (g * graphAutF4 K (c3LeviHom K s) * g⁻¹) : L) : G) := by
  rw [twEdgeYParam_apply, hΦ₁ s, twTrans_graphAutF4_symm_symm_apply, map_mul, map_mul, map_inv,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem commute_twEdgeYParam
    (Φ₁ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
      centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))
    (y : StatedOmega (StatedQuadPlus (3 + 1) K)) {z : adjointGroup .F4 K} (hz : z ∈ X₀) :
    Commute (twEdgeYParam e g Φ₁ y) ((e.symm (g * graphAutF4 K z * g⁻¹) : L) : G) := by
  have hc : Commute ((Φ₁ y : centralizerPerfectCore _) : G)
      (((e.trans (graphAutF4 K).symm).symm z : L) : G) := by
    have h := centralizerPerfectCore_le_centralizer _ (Φ₁ y).2
    exact (mem_centralizer_iff.1 h _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩).symm
  rw [twTrans_graphAutF4_symm_symm_apply] at hc
  rw [twEdgeYParam_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv]
  exact (Commute.conj_iff _).2 hc

end YParam

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
include hK

theorem twFrame1_L2 :
    edgeH1 K * wRep K [3, 2] * graphAutF4 K (c3LeviHom K (elt (.positiveLong 2) 1)) *
        (edgeH1 K * wRep K [3, 2])⁻¹ = Adjoint.f4Par K (Pi.single 3 1) 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, 0, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)).trans (edge_conj_eq_of_mul_eq (commute_edgeH1_f4Par hK (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).eq)

theorem twFrame3_L2 :
    edgeH3 K * wRep K [] * graphAutF4 K (c3LeviHom K (elt (.positiveLong 2) 1)) *
        (edgeH3 K * wRep K [])⁻¹ = Adjoint.f4Par K (Pi.single 2 1) 1 :=
  (frame_c3LeviHom_elt hK _ _ (δ := ![0, 0, 1]) (by decide) (mem_rootFinset.1 (by decide +kernel))
    (by decide +kernel)).trans (edge_conj_eq_of_mul_eq (commute_edgeH3_f4Par hK (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).eq)

end Frame

theorem c3ToF4_single_zero_twEdge : c3ToF4 (Pi.single 0 1) = Pi.single 3 1 := by
  decide +kernel

theorem c3ToF4_single_one_twEdge : c3ToF4 (Pi.single 1 1) = Pi.single 2 1 := by
  decide +kernel

theorem c3ToF4_root021_twEdge : c3ToF4 ![0, 2, 1] = v0120 := by
  decide +kernel

end CFSG.SeitzReduction.F4Pilot
