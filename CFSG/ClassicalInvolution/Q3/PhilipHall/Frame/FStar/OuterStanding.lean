module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Reduce
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrTSetup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIIFStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

section Datum

variable {Y : Type} [Group Y] [Finite Y]

theorem frameTightDatum_of_typeRHyp {K : Subgroup Y} {z : Y}
    (hΦ : TypeRHyp (CoreAssembly.conjClass K)) (hgen : omegaGen (CoreAssembly.conjClass K) = ⊤)
    (hA : ¬ AEmpty (CoreAssembly.conjClass K) K) (hz : IsUniqueInvolution K z) :
    FrameTightDatum K z := by
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  refine
    { tightCore_eq := tightCore_eq_self_of_typeRHyp hΦ hK
      unique := hz
      quat := hΦ.sylow K hK
      twoGroup := hΦ.twoGroup K hK
      subnormal := QuaternionBridge.CentQ.isSubnormal_centralizer_gen hΦ.hyp hK hz
      hyp := hΦ.hyp
      selfGen := ?_
      twin := ?_ }
  · rw [eq_top_iff, ← hgen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨g, rfl⟩ := hL
    exact le_iSup (fun g : Y => conjSub g K) g
  · obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
    obtain ⟨a, -, -, hmem, hz', hne⟩ := Q3T6D.AViol.exists_twin hΦ.hyp hK hv
    exact ⟨conjSub a J, ⟨hmem, zK, hv.hzK, hz'⟩, hne⟩

end Datum

section Cases

@[expose] def FrameCaseITF : Prop :=
  ∀ (T : Type) [Group T] [Finite T], FStarSimple T → classicalInvolutionOddCore T = ⊥ →
    Thm3RBelowG (Nat.card T) → (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
    TL4.TightBelowRPlus 3 (Nat.card T) →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ : T), AViol (CoreAssembly.conjClass R) R J zK zJ →
        aStar (CoreAssembly.conjClass R) R ≠ CoreAssembly.conjClass R → False

theorem thm3RStdOuter_of_cases (h1 : FrameCaseITF) (h2 : FrameCaseIITF) (m : ℕ) :
    Thm3RStdOuter m := by
  intro Y _ _ Φ K hc _ hF hcl _
  have hcl' : SubClass Φ K ⊤ := fun L hL => by
    obtain ⟨t, -, ht⟩ := hcl L hL
    exact ⟨t, Subgroup.mem_top t, ht⟩
  have hΦ : Φ = CoreAssembly.conjClass K :=
    eq_conjClass_of_subClass hc.hyp.hyp.conjInvariant hc.mem hcl'
  obtain ⟨ih, hY, -, hR, -, hA, hO, hgen⟩ := hc
  subst hΦ
  obtain ⟨z, hz⟩ := (hR.hyp.omega1 K (CoreAssembly.mem_conjClass_self K)).1
  have hD : FrameTightDatum K z := frameTightDatum_of_typeRHyp hR hgen hA hz
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hF.2
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hB : Thm3RBelowG (Nat.card Y) := hY ▸ ih.below
  have hcit : CIT3Below (Nat.card Y) := CIT3Below.mono (hY ▸ Nat.le_succ m) ih.cit
  have hP : TL4.TightBelowRPlus 3 (Nat.card Y) := ih.pkg.mono (hY ▸ Nat.le_succ m)
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  by_cases hs : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K
  · obtain ⟨a, ha, hac, -, -, hne, g, hg, hgK⟩ :=
      Q3T6D.AViol.exists_swap hD.hyp (CoreAssembly.mem_conjClass_self K)
        (fun M hM => by obtain ⟨g, rfl⟩ := hM; exact ⟨g, rfl⟩) hv
    exact h2 Y hF hO hB hnab hcit hP K z hD J zK zJ a g hv ha hac hne hgK hg hs
  · exact h1 Y hF hO hB hnab hcit hP K z hD J zK zJ hv hs

end Cases

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar
