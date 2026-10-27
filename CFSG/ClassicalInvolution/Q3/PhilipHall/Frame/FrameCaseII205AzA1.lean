module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205AzTri
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameSimple
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51D4A
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement MatrixGroups

section Member

variable {G : Type} [Group G] [Finite G]

theorem tightCore_eq_self_of_hyp {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) : tightCore K = K := by
  rcases hΩ.omega2 K hK with h1 | hne
  · exact h1
  · exfalso
    obtain ⟨e⟩ := hne
    have h3 : IsPGroup 2 SL(2, ZMod 3) := h2.of_equiv e
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h3
    rw [natCard_sl2Three] at hk
    have h3dvd : 3 ∣ 2 ^ k := by
      rw [← hk]
      norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)

theorem secCoreHyp_of_member {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) {K : Subgroup G}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K))
    (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) {M : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass K) {z : G} (hz : IsUniqueInvolution M z) {P : Subgroup G}
    (hPs : IsSylow2In P M) (hq : Nonempty (↥P ≃* QuaternionGroup 2)) :
    tightCore M = M ∧ ∃ S : Sylow 2 ↥M, AzTri.SecCoreHyp n M S z := by
  have h2M : IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass h2 M hM
  have hMc : tightCore M = M := tightCore_eq_self_of_hyp hΩ hM h2M
  refine ⟨hMc, ?_⟩
  obtain ⟨S, hS⟩ := exists_sylow_map_eq hPs
  have hqS : Nonempty (↥(S : Subgroup ↥M) ≃* QuaternionGroup 2) :=
    ⟨((Subgroup.equivMapOfInjective (S : Subgroup ↥M) M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hS)).trans hq.some⟩
  have hcard : Nat.card ↥P = 8 := by
    rw [Nat.card_congr hq.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hzP : z ∈ P := mem_of_isPGroup hz hPs.1 hPs.2.1 (by omega)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hΩM : HypOmegaGen (CoreAssembly.conjClass (tightCore M)) := by
    rw [hMc, TwinVtx.conjClass_eq_of_mem hM]
    exact hΩ
  refine ⟨S, hP.twin rfl |>.toHasLift |> fun tw => ?_⟩
  exact ⟨TL4.tightBelow_of_plus hP, tw, ⟨⟨3, le_rfl, hqS⟩, by rw [hS]; exact hzP, hz2,
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_isUniqueInvolution hz, h2M⟩,
    hqS, hΩM⟩

end Member

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
