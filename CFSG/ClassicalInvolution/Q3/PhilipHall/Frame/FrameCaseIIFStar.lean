module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrLE8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar.LemmaG
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar.N3
import CFSG.ClassicalInvolution.Q3.TL4Thm5Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3

section FrameCore

variable {T : Type} [Group T] [Finite T]

theorem frameCore_of_fstar (hF : Thm3Step.FStarSimple T)
    (hO : classicalInvolutionOddCore T = ⊥) : FrameCore T where
  center _ := TL4.center_eq_bot_of_fstar_simple hF.1 hF.2
  oddNormal _ N hN hodd := by
    have h : N ≤ classicalInvolutionOddCore T := le_sSup ⟨hN, hodd⟩
    rw [hO] at h
    exact le_bot_iff.mp h

end FrameCore

@[expose] def Frame206ClosedF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t → Concl20_8 S K' R →
      Concl20_3 K K' V z → ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) →
        h⁻¹ * z * h ∈ Subgroup.closure ({t, z} : Set G)

section Defs


@[expose] def FrameCaseIITF : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Thm3Step.FStarSimple T → classicalInvolutionOddCore T = ⊥ →
    Thm3A.Thm3RBelowG (Nat.card T) → (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
    TL4.TightBelowRPlus 3 (Nat.card T) →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ a g : T),
        AViol (CoreAssembly.conjClass R) R J zK zJ →
        a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
        conjSub g R = conjSub a J → g * zK * g⁻¹ = zK →
        aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R → False

end Defs

section Assembly


theorem Std20Frame.noIndexTwo_of_not_concl203 {G : Type} [Group G] [Finite G] [FrameCore G]
    {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
    (d : Std20Frame K K' J S R R' W V z t) (h3 : ¬ Concl20_3 K K' V z) :
    ∀ H : Subgroup G, H.index ≠ 2 := by
  obtain ⟨y, hy⟩ := FStar.exists_psiK_fpf frame203Cent_holds frame203Outer d h3
  intro H hH
  have hKH : K ≤ H := FStar.le_of_index_eq_two_of_psiK_fpf y
    (fun I => by rw [← Out.psiK_apply]; exact hy I) hH
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hH
  have htop : (⊤ : Subgroup G) ≤ H := by
    rw [← d.gen]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨x, rfl⟩ := hM
    intro m hm
    rw [mem_conjSub_iff] at hm
    have := hHn.conj_mem _ (hKH hm) x
    simpa [mul_assoc] using this
  rw [eq_top_iff.mpr htop, Subgroup.index_top] at hH
  exact absurd hH (by decide)

theorem frameCaseIITF_of_closed (hcl : Frame206ClosedF) : FrameCaseIITF := by
  intro T _ _ hF hO hB hnab hcit hP R t hdat J zK zJ a g hv ha hac hne hg hgK hs
  haveI : FrameCore T := frameCore_of_fstar hF hO
  haveI := hF.1
  have h := frameIIHyp_of_datum hnab hdat hv ha hac hne hg hgK hs
  have h202 := frameNbrTwinSG_of_hyp51L frameHyp51L_holds T hB hcit hP R J zK zJ a g h
  obtain ⟨K', S, R₁, R₁', W, V, d⟩ := std20Frame_of_nbrTwin h h202
  by_cases h3 : Concl20_3 R K' V zK
  · have c4 := frameC204 T _ K' J S R₁ R₁' W V zK zJ d
    have c5 := frameC205CTG_of_steps (frame20ACentX'_of_cent frame203Cent_holds)
      (frameHyp51BG_holds_of g2ModelInnerOddFree_holds) frameXCover_holds T _ K' J S R₁ R₁' W V zK zJ
      d hB hcit hP c4
    have c8 := frameC208 T _ K' J S R₁ R₁' W V zK zJ d (concl20_7_of_cent frame203Cent_holds d c5)
    exact FStar.frameC206_fstar hF.2 hO d (hcl T R K' J S R₁ R₁' W V zK zJ d c8 h3)
  · haveI : FrameSimple T := FrameSimple.of_frameCore fun _ => d.noIndexTwo_of_not_concl203 h3
    exact frameCaseIITGSN_of_namedG (frameNbrTwinSG_of_hyp51L frameHyp51L_holds)
      frame203Cent_holds (frameHyp51BG_holds_of g2ModelInnerOddFree_holds) frameXCover_holds T hB
      hnab hcit hP R t hdat J zK zJ a g hv ha hac hne hg hgK hs

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
