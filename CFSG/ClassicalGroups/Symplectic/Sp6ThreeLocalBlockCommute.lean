module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalDefs

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem commute_block_mulSingle_c₀ {s : SL(2, K)} (hs : IsCubeRootBlock s) {i : Fin 3}
    (g : SL(2, K)) (v : Multiplicative (Fin 3 → ZMod 3)) (hv : Multiplicative.toAdd v i = 0) :
    Commute (block (Pi.mulSingle i g)) (c₀ hs v) := by
  rw [c₀_apply]
  refine Commute.map (f := (block : (Fin 3 → SL(2, K)) →* StatedSp 3 K)) ?_
  unfold Commute SemiconjBy
  funext j
  by_cases h : j = i
  · subst h
    simp [hv]
  · simp [Pi.mulSingle_eq_of_ne h]

theorem commute_block_mulSingle_c₀_of_commute {s : SL(2, K)} (hs : IsCubeRootBlock s)
    {z : SL(2, K)} (hz : Commute (z : Matrix (Fin 2) (Fin 2) K) (s : Matrix (Fin 2) (Fin 2) K))
    (i : Fin 3) (v : Multiplicative (Fin 3 → ZMod 3)) :
    Commute (block (Pi.mulSingle i z)) (c₀ hs v) := by
  rw [c₀_apply]
  refine Commute.map (f := (block : (Fin 3 → SL(2, K)) →* StatedSp 3 K)) ?_
  unfold Commute SemiconjBy
  funext j
  by_cases h : j = i
  · subst h
    have hzs : Commute z s := by
      unfold Commute SemiconjBy
      apply Subtype.ext
      simpa using hz.eq
    simpa using (hzs.pow_right (Multiplicative.toAdd v j).val).eq
  · simp [Pi.mulSingle_eq_of_ne h]

theorem orderOf_block_mulSingle (i : Fin 3) (g : SL(2, K)) :
    orderOf (block (Pi.mulSingle i g)) = orderOf g := by
  have hinj : Function.Injective
      ((block : (Fin 3 → SL(2, K)) →* StatedSp 3 K).comp (MonoidHom.mulSingle _ i)) :=
    fun a b h => Pi.mulSingle_injective i (block_injective h)
  exact orderOf_injective _ hinj g

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
