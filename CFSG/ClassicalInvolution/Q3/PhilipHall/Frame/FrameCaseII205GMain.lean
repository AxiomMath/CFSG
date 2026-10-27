module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GBar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205QMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

section Defs


@[expose] def FrameHyp51AG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G) (d : Std20Frame K K' J S R R' W V z t) (a : G),
      Thm3A.Thm3RBelowG (Nat.card G) → CIT3Below (Nat.card G) →
      TL4.TightBelowRPlus 3 (Nat.card G) → Frame205Data d a →
        Hyp51At (Subgroup.closure ({z, t, a} : Set G)) a

@[expose] def FrameHyp51AzG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G) (d : Std20Frame K K' J S R R' W V z t) (a : G),
      Thm3A.Thm3RBelowG (Nat.card G) → CIT3Below (Nat.card G) →
      TL4.TightBelowRPlus 3 (Nat.card G) → Frame205Data d a →
        Hyp51At (Subgroup.closure ({z, t, a} : Set G)) (a * z)

@[expose] def FrameHyp51BG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G) (d : Std20Frame K K' J S R R' W V z t) (a : G),
      Thm3A.Thm3RBelowG (Nat.card G) → CIT3Below (Nat.card G) →
      TL4.TightBelowRPlus 3 (Nat.card G) → Frame205Data d a →
        Hyp51 (Subgroup.closure ({z, t, a} : Set G))

end Defs


section Vertex

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
  {a c : G} {d : Std20Frame K K' J S R R' W V z t}

theorem hyp51At_of_vertexG (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hT4 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n)
    (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree)
    (hB : Thm3A.Thm3RBelowG (Nat.card G)) (hcit : CIT3Below (Nat.card G))
    (hP : TL4.TightBelowRPlus 3 (Nat.card G)) (hd : Frame205Data d a) (hv : Vertex205 d a c) :
    Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := by
  by_cases h1 : AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
      (Subgroup.centralizer ({c} : Set G))))
        ((frameKa K c).map (oqMk ↥(Subgroup.centralizer ({c} : Set G))))
  · by_cases h2 : AEmpty (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
          ((frameKa K' c).map (oqMk ↥(Subgroup.centralizer ({c} : Set G))))
    · exact hyp51At_of_quotEmpty hSp hD4 hM12 hT4 hcit hP hd hv h1 h2
    · exact hyp51At_of_quotViolG hU hM12 hM12fin hM12nab hG2 hd hv hB (Or.inr h2)
  · exact hyp51At_of_quotViolG hU hM12 hM12fin hM12nab hG2 hd hv hB (Or.inl h1)

end Vertex

theorem frameHyp51AG_of_models (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hT4 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n)
    (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree) :
    FrameHyp51AG := by
  intro G _ _ _ K K' J S R R' W V z t d a hB hcit hP hd
  exact hyp51At_of_vertexG hSp hD4 hM12 hT4 hU hM12fin hM12nab hG2 hB hcit hP hd
    (vertex205_a d hd)

theorem frameHyp51AzG_of_models (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hT4 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n)
    (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    (hG2 : G2ModelInnerOddFree) :
    FrameHyp51AzG := by
  intro G _ _ _ K K' J S R R' W V z t d a hB hcit hP hd
  exact hyp51At_of_vertexG hSp hD4 hM12 hT4 hU hM12fin hM12nab hG2 hB hcit hP hd
    (vertex205_az d hd)

theorem frameHyp51BG_of_vertices (hA : FrameHyp51AG) (hAz : FrameHyp51AzG) : FrameHyp51BG := by
  intro G _ _ _ K K' J S R R' W V z t d a hT hcit hP hd
  exact d.s_hyp51_of_at hd.conf (hA G K K' J S R R' W V z t d a hT hcit hP hd)
    (hAz G K K' J S R R' W V z t d a hT hcit hP hd)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
