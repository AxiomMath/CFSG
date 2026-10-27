module

public import CFSG.ClassicalInvolution.Q3.TL4Thm5Small
public import CFSG.ClassicalInvolution.Q3.TL4StepDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem thm5StepR_three_of {n : ℕ} (hGH : GH74SectionalModels)
    (hL3 : Thm5SmallLeaf TA3.SmallL3Ne3) (hU3 : Thm5SmallLeaf TA3.SmallU3Ne3)
    (halpha : PlusLeaf TightAlphaLeafR n) (hconn : PlusLeaf TightConnLeafR' n) :
    Thm5StepR 3 n := by
  intro hA hP X _ _ hX Φ hΦ hO hs hnab htr K hK J hJ z t hz ht
  rcases Nat.lt_succ_iff_lt_or_eq.mp hX with hlt | heq
  · exact hP.thm5 X hlt Φ hΦ hO hs hnab htr K hK J hJ z t hz ht
  by_cases hgen : omegaGen Φ = ⊤
  · by_cases hsmall : TwoSubgroupsFourGenerated ↥(genFittingFStar X)
    · exact thm5SmallR_three_of hGH hL3 hU3 hA X heq Φ hΦ hO hs hnab htr hgen hsmall K hK J hJ
        z t hz ht
    have hedge : ¬ Disconnected.DEdgeless Φ := fun hed => hed K hK J hJ.1 (Or.inl hJ)
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
    obtain ⟨hL, hcore, hcl⟩ := tightLargeHypR_of_transitive hA hP.tbelow heq hs hnab hsmall hΦ
      hO hgen htr hedge hK hz S
    have hJ' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore K)) (tightCore K) := by
      rw [hcore, hcl]
      exact hJ
    exact halpha hA hP X K S z hL (hconn hA hP X K S z hL) J hJ' t ht
  · exact thm5OuterR_three_of hA hP X heq Φ hΦ hO hs hnab htr hgen K hK J hJ z t hz ht

end CFSG.ClassicalInvolution.Q3.TL4
