module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf4Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Z

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.AE

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem false_of_model_z_e29 (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (I : AEIdentOn (fam K (conjSub g (piGen π))) 8 AE.e29Sets AE.e29Sub)
    (hZ : ∀ (zS : ↥(pSpan (fam K (conjSub g (piGen π))))), (zS : G) = z →
      ∀ (L : Subgroup G) (hL : L ∈ fam K (conjSub g (piGen π))) (u : G)
        (hu : IsUniqueInvolution L u),
        (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) ∈ Subgroup.closure
          {w : ↥(pSpan (fam K (conjSub g (piGen π)))) | w * zS = zS * w ∧
            ∃ a : ℕ, w ^ 3 ^ a = 1}) : False := by
  have hP : pSpan (fam K (conjSub g (piGen π))) = conjSub g (piGen π) := S.fam_gen
  have hzS : z ∈ pSpan (fam K (conjSub g (piGen π))) := le_pSpan S.mem_fam_self S.hz.mem
  set zS : ↥(pSpan (fam K (conjSub g (piGen π)))) := ⟨z, hzS⟩ with hzSdef
  let T : Subgroup ↥(pSpan (fam K (conjSub g (piGen π)))) := Subgroup.closure
    {w | w * zS = zS * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1}
  have hTc : ∀ w ∈ T, ∀ x ∈ piGen π, x * (w : G) = (w : G) * x := by
    intro w hw
    have hle : T ≤ (Subgroup.centralizer (piGen π : Set G)).comap
        (pSpan (fam K (conjSub g (piGen π)))).subtype := by
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro w ⟨hwz, a, hwa⟩
      have hwX : (w : G) ∈ conjSub g (piGen π) := by
        exact (SetLike.ext_iff.mp hP (w : G)).mp w.2
      have hwz' : (w : G) * z = z * (w : G) := congrArg Subtype.val hwz
      have := S.centralizes_of_three_e29 hS hnab I hwX hwz' ⟨a, by
        have := congrArg Subtype.val hwa
        simpa using this⟩
      intro x hx
      exact (this x hx).symm
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hw) x hx
  refine S.false_of_cent fun L hL u hu x hx => ?_
  exact hTc _ (hZ zS rfl L hL u hu) x hx

end Setting

theorem thinE29_of_pair {IH : Prop} (hZ : ThinZInT IH 8 AE.e29Sets AE.e29Sub) : ThinE29 IH :=
  fun hIH G _ _ K₀ K K' z π g S hS hnab ⟨I⟩ =>
    S.false_of_model_z_e29 hS hnab I (hZ hIH G K₀ K K' z π g S hS hnab I)

theorem thinE29_of_pair_ker {IH : Prop} (hCl : TwinThinPf.OddClosure AE.e29Sub AE.e29Sets)
    (hKer : ThinKerOdd IH 8 AE.e29Sets AE.e29Sub) : ThinE29 IH :=
  thinE29_of_pair (thinZInT_of_ker (by norm_num) hCl hKer)

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
