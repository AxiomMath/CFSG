module

public import CFSG.RankThree.PartOne.KE.E7FourStabBase
public import CFSG.LieType.Chevalley.E7Three.Cube
public import CFSG.LieType.Chevalley.E7Three.Product

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Cycle

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Chevalley.E7Three.Frames CFSG.LieType.Chevalley.E7Three.FrameWords
  CFSG.LieType.Chevalley.E7Three.Product CFSG.LieType.Chevalley.E7Three.PauliWords
  CFSG.LieType.Chevalley.E7Three.Cube CFSG.LieType.Chevalley.E7Three.Weyl

open scoped MatrixGroups

theorem nativeA2Roots_zero_one (r : Fin 3) :
    nativeA2Roots r 0 1 = e7ExtVec (nativePairs r).1 := by
  simp [nativeA2Roots, nativeWeights]

theorem nativeA2Roots_one_two (r : Fin 3) :
    nativeA2Roots r 1 2 = e7ExtVec (nativePairs r).2 := by
  change -e7ExtVec (nativePairs r).1 -
    (-(e7ExtVec (nativePairs r).1 + e7ExtVec (nativePairs r).2)) = _
  abel

variable {K : Type} [Field K] [CharP K 2]

theorem theta_cycle_image (w : NativeFrame K) (r : Fin 3) :
    theta w r (cycleWord (K := K)) =
      canonicalRep (coxeterSystem .E7) K (rootReflection (e7ExtVec (nativePairs r).1)) *
        canonicalRep (coxeterSystem .E7) K (rootReflection (e7ExtVec (nativePairs r).2)) := by
  have h0 : IsRoot .E7 (e7ExtVec (nativePairs r).1) := by
    rw [← nativeA2Roots_zero_one]
    exact (w.isFrame r).isRoot 0 1 (by decide)
  have h1 : IsRoot .E7 (e7ExtVec (nativePairs r).2) := by
    rw [← nativeA2Roots_one_two]
    exact (w.isFrame r).isRoot 1 2 (by decide)
  exact cycleWord_image (theta w r) _ _ h0 h1 (w.block0 r) (w.block1 r)

theorem prodHom_cycle (w : NativeFrame K) :
    prodHom w ![cycleWord, cycleWord, cycleWord ^ 2] = (cyclic (K := K) : ModGL .E7 K) := by
  rw [prodHom_apply]
  change theta w 0 cycleWord * theta w 1 cycleWord * theta w 2 (cycleWord ^ 2) = _
  rw [(theta w 2).map_pow, theta_cycle_image w 0, theta_cycle_image w 1,
    theta_cycle_image w 2]
  let N : WeylGroup .E7 →* ModGL .E7 K :=
    (adjointGroup .E7 K).subtype.comp (CFSG.SectionRank.LargeRee.nrepHom .E7 K)
  change (N (rootReflection (e7ExtVec (nativePairs 0).1)) *
      N (rootReflection (e7ExtVec (nativePairs 0).2))) *
    (N (rootReflection (e7ExtVec (nativePairs 1).1)) *
      N (rootReflection (e7ExtVec (nativePairs 1).2))) *
    (N (rootReflection (e7ExtVec (nativePairs 2).1)) *
      N (rootReflection (e7ExtVec (nativePairs 2).2))) ^ 2 = N gamma
  simp only [← N.map_mul, ← N.map_pow]
  congr 1
  simp [gamma, nativePairs, e7ExtVec, ← simple_eq_rootReflection_single,
    CoxeterSystem.wordProd, kacE7_extRoot, mul_assoc]
  simp [simple, e7Index]
  rfl

end CFSG.LieType.Chevalley.E7Three.Cycle
