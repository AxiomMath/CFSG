module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.QuasithinUnique.Ch1.AltSix
open Equiv Equiv.Perm CFSG.QuasithinUnique

@[expose, irreducible] def totalZero : Finset (Perm (Fin 6)) :=
  {swap 5 0 * swap 1 4 * swap 2 3, swap 5 1 * swap 2 0 * swap 3 4, swap 5 2 * swap 3 1 * swap 4 0,
    swap 5 3 * swap 4 2 * swap 0 1, swap 5 4 * swap 0 3 * swap 1 2}

@[expose, irreducible] def act (σ : Perm (Fin 6)) (t : Finset (Perm (Fin 6))) : Finset (Perm (Fin 6)) :=
  t.image fun m => σ * m * σ⁻¹

theorem act_mul (σ τ : Perm (Fin 6)) (t : Finset (Perm (Fin 6))) :
    act (σ * τ) t = act σ (act τ t) := by
  unfold act
  rw [Finset.image_image]
  refine Finset.image_congr fun m _ => ?_
  simp only [Function.comp_apply]
  group

theorem act_one (t : Finset (Perm (Fin 6))) : act 1 t = t := by
  unfold act
  simp

@[expose, irreducible] def total (i : Fin 6) : Finset (Perm (Fin 6)) := act (swap 0 i) totalZero

end CFSG.QuasithinUnique.Ch1.AltSix
