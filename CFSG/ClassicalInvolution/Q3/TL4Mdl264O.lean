module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl264OA
public import CFSG.ClassicalInvolution.Q3.TL4Mdl264OB
public import CFSG.ClassicalInvolution.Q3.TL4Mdl264U
public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Blueprint CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap

namespace O264

theorem threeOver2Om3_of_frame {K V S : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Group S] [Finite S] {Q : QuadraticForm K V}
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    (θ : ↥(orthDerived Q) →* S) (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) : ThreeOver2Om3 S := by
  intro A B r hA _ _
  obtain ⟨F, rfl, -⟩ := exists_frame_of_quatTwinDatum hK hQ hn θ hθ hker hA
  obtain ⟨F₃, hinv, P, hP, c₁, c₂, c₃⟩ := exists_three_frames hK hQ hn θ hker F
  have hu : ∀ G : Frame Q, IsUniqueInvolution (frameMember θ G) (frameInv θ G) :=
    isUniqueInvolution_frameMember hK (by omega) θ hker
  refine ⟨frameMember θ F, CoreAssembly.mem_conjClass_self _, frameMember θ F.swap,
    frameMember_mem_conjClass_frameMember hK hQ hn θ F F.swap, frameMember θ F₃,
    frameMember_mem_conjClass_frameMember hK hQ hn θ F F₃,
    (frameMember_swap_ne hK hQ (by omega) θ hker F).symm, fun h => ?_, fun h => ?_, P, hP,
    c₁, c₂, c₃⟩
  · exact hinv ((hu F).eq (by rw [h]; exact hu F₃)).symm
  · have h1 := (hu F.swap).eq (by rw [h]; exact hu F₃)
    rw [frameInv_swap] at h1
    exact hinv h1.symm

end O264

theorem threeOver2Om3_of_orthBad3 :
    ∀ (S : Type) [Group S] [Finite S] (t : Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
      OrthBad3 t n → LieModel S t n 3 1 → ThreeOver2Om3 S := by
  intro S _ _ t n ht hS
  obtain ⟨K, _, _, d, Q, θ, hK, hQ, hd, hθ, hker⟩ := O264.exists_orthModel ht hS
  exact O264.threeOver2Om3_of_frame hK hQ (by rw [Module.finrank_fin_fun]; exact hd) θ hθ hker

section Proved


theorem model264Rank3_proved : Model264Rank3 :=
  model264Rank3_of threeOver2Om3_of_psu43 threeOver2Om3_of_orthBad3

end Proved

end CFSG.ClassicalInvolution.Q3.TL4
