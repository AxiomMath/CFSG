module

public import CFSG.LieType.Chevalley.E7Three.Frames
public import CFSG.LieType.Chevalley.E7Three.FrameWords

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Product

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.PartOne.KA5L CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Chevalley.E7Three.Frames
  CFSG.LieType.Chevalley.E7Three.FrameWords

open scoped MatrixGroups


structure NativeFrame (K : Type) [Field K] [CharP K 2] where
  rho : Fin 3 → SL(3, K) →* ModGL .E7 K
  diag : Fin 3 → Fin 3 → Kˣ
  isFrame : ∀ r, IsA2Frame (rho r) (nativeA2Roots r)
  block0 : ∀ r,
    ((rho r).comp (conjDiag3Hom (diag r))).comp (blockSL K 3 2 0 (by omega)) =
      rootSL2 .E7 K (e7ExtVec (nativePairs r).1)
  block1 : ∀ r,
    ((rho r).comp (conjDiag3Hom (diag r))).comp (blockSL K 3 2 1 (by omega)) =
      rootSL2 .E7 K (e7ExtVec (nativePairs r).2)
  pairwise_commute : Pairwise fun r s => ∀ A B,
    Commute (rho r (conjDiag3 (diag r) A)) (rho s (conjDiag3 (diag s) B))

variable {K : Type} [Field K] [CharP K 2]

theorem nativeFrame_exists : Nonempty (NativeFrame K) := by
  obtain ⟨rho, diag, hF, hb, hc⟩ := exists_three_pinned_frames (K := K)
  refine ⟨{
    rho := rho
    diag := diag
    isFrame := hF
    block0 := ?_
    block1 := ?_
    pairwise_commute := ?_
  }⟩
  · intro r
    simpa only [kacE7_extRoot] using (hb r).1
  · intro r
    simpa only [kacE7_extRoot] using (hb r).2
  · intro r s hrs A B
    exact hc r s hrs A B

@[expose] def theta (w : NativeFrame K) (r : Fin 3) : SL(3, K) →* ModGL .E7 K :=
  (w.rho r).comp (conjDiag3Hom (w.diag r))

@[expose] def prodHom (w : NativeFrame K) : (Fin 3 → SL(3, K)) →* ModGL .E7 K :=
  MonoidHom.noncommPiCoprod (theta w) (by
    intro r s hrs A B
    exact w.pairwise_commute hrs A B)

theorem prodHom_apply (w : NativeFrame K) (f : Fin 3 → SL(3, K)) :
    prodHom w f = theta w 0 (f 0) * theta w 1 (f 1) * theta w 2 (f 2) := by
  have hf : f = Pi.mulSingle 0 (f 0) * Pi.mulSingle 1 (f 1) * Pi.mulSingle 2 (f 2) := by
    funext r
    fin_cases r <;> simp
  calc
    prodHom w f = prodHom w
        (Pi.mulSingle 0 (f 0) * Pi.mulSingle 1 (f 1) * Pi.mulSingle 2 (f 2)) :=
      congrArg (prodHom w) hf
    _ = theta w 0 (f 0) * theta w 1 (f 1) * theta w 2 (f 2) := by
      rw [(prodHom w).map_mul, (prodHom w).map_mul]
      simp only [prodHom, MonoidHom.noncommPiCoprod_mulSingle]

theorem theta_mem_adjointGroup (w : NativeFrame K) (r : Fin 3) (A : SL(3, K)) :
    theta w r A ∈ adjointGroup .E7 K := by
  exact frame_mem_adjointGroup (w.rho r) (nativeA2Roots r) (w.isFrame r)
    (conjDiag3 (w.diag r) A)

theorem prodHom_mem_adjointGroup (w : NativeFrame K) (f : Fin 3 → SL(3, K)) :
    prodHom w f ∈ adjointGroup .E7 K := by
  rw [prodHom_apply]
  exact (adjointGroup .E7 K).mul_mem
    ((adjointGroup .E7 K).mul_mem (theta_mem_adjointGroup w 0 (f 0))
      (theta_mem_adjointGroup w 1 (f 1)))
    (theta_mem_adjointGroup w 2 (f 2))

@[expose] def adjProdHom (w : NativeFrame K) :
    (Fin 3 → SL(3, K)) →* adjointGroup .E7 K :=
  (prodHom w).codRestrict (adjointGroup .E7 K) (prodHom_mem_adjointGroup w)

end CFSG.LieType.Chevalley.E7Three.Product
