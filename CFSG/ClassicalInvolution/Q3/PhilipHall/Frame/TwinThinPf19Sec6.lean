module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6D
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6E2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Nbr

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem secYu_of {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    (hE4 : E4SplitModel) (hG : Nat.card G ≤ n) (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {m : ℕ} (hm : 6 ≤ m) (hAut : TwinThinPf8.AEAut m) (htw : S.TwinLab m)
    (hβ : betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'})
    (J : AEIdent (fam K (conjSub g (piGen π))) m) : SecYu K₀ K K' z π g := by
  intro u hu
  have hnb := S.nbrPiTwin_of_beta hβ
  have hX := S.pairInv_commute hu
  have hF7 := S.f7Cent h4 hG hS hnab hm J hodd
  have hO := S.oddCore_centLayer_eq_bot hm J hodd hu.2.1 hX
  have horb := S.singleOrbit hF7 hβ hu
  have hE2 := S.e2_Yu hP hE4 hG hS hnab (by omega) hAut htw J hodd hu hO horb hnb.2
  refine ⟨?_, hE2, S.d2_Yu hP hG hS hnab (by omega) J hu hO horb hnb.2 hE2⟩
  intro L hL L' hL'
  obtain ⟨a, ha, rfl⟩ := horb L hL
  obtain ⟨b, hb, rfl⟩ := horb L' hL'
  refine ⟨b * a⁻¹, (centLayer (CoreAssembly.conjClass K₀) u).mul_mem hb
    ((centLayer (CoreAssembly.conjClass K₀) u).inv_mem ha), ?_⟩
  rw [conjSub_mul, conjSub_inv_conjSub]

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
