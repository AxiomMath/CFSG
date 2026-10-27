module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfLift

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.AE

set_option linter.unusedSectionVars false

namespace TwinThin

@[expose] def ThinZInT (IH : Prop) (m : ℕ) (𝒜 : Set (Finset (Fin m))) (H : Subgroup (AEQ m)) :
    Prop :=
  IH → ∀ (G : Type) [Group G] [Finite G] (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G))
    (g : G), Setting K₀ K K' z π g → IsSimpleGroup ↥(genFittingFStar G) →
    (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
    ∀ (_ : AEIdentOn (fam K (conjSub g (piGen π))) m 𝒜 H)
      (zS : ↥(pSpan (fam K (conjSub g (piGen π))))), (zS : G) = z →
      ∀ (L : Subgroup G) (hL : L ∈ fam K (conjSub g (piGen π))) (u : G)
        (hu : IsUniqueInvolution L u),
        (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) ∈ Subgroup.closure
          {w : ↥(pSpan (fam K (conjSub g (piGen π)))) | w * zS = zS * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1}

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

theorem thinZInT_of_ker {IH : Prop} {m : ℕ} {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AEQ m)}
    (hm : 5 ≤ m) (hCl : TwinThinPf.OddClosure H 𝒜) (hKer : ThinKerOdd IH m 𝒜 H) :
    ThinZInT IH m 𝒜 H := by
  intro hIH G _ _ K₀ K K' z π g S hS hnab I zS hzS L hL u hu
  have hP : pSpan (fam K (conjSub g (piGen π))) = conjSub g (piGen π) := S.fam_gen
  have hO : classicalInvolutionOddCore ↥(pSpan (fam K (conjSub g (piGen π)))) = ⊥ := by
    rw [hP]; exact S.hO
  have hc8 : ∀ L ∈ fam K (conjSub g (piGen π)), Nat.card L = 8 := fun L hL =>
    S.card8 L (fam_subset S.hos.graph S.hK hL)
  obtain ⟨t, htT, hker⟩ := TwinThinPf.exists_mem_threeClosure hm I hCl hO hc8 S.mem_fam_self S.hz hL hu
  have hzSeq : zS = ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ := Subtype.ext hzS
  subst hzSeq
  have hkT := hKer hIH G K₀ K K' z π g S hS hnab I ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ rfl _ hker
  unfold TwinThinPf.threeGens at htT
  have := (Subgroup.closure _).mul_mem htT hkT
  simpa using this

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
