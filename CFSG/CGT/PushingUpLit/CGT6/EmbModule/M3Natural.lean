module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cAFun

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.GH74.GLS.Stage4.Rest

section Natural

variable {F : Type} [Field F]

@[expose] def natPair (u : Fin 2 → F) : (Fin 2 → F) → F := fun v => u 0 * v 1 - u 1 * v 0

theorem natPair_add (u u' : Fin 2 → F) : natPair (u + u') = natPair u + natPair u' := by
  funext v
  simp only [natPair, Pi.add_apply]
  ring

theorem natPair_funRep (g : SLm F) (u : Fin 2 → F) :
    funRep F F g (natPair u) = natPair ((g : Matrix (Fin 2) (Fin 2) F).mulVec u) := by
  funext v
  rw [funRep_apply]
  simp only [natPair]
  rw [inv_mulVec_zero, inv_mulVec_one]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem natPair_mem (u : Fin 2 → F) :
    natPair u ∈ steinbergSub F F 1 := by
  have h : natPair u = u 0 • monoFun F F 0 1 - u 1 • monoFun F F 1 0 := by
    funext v
    simp [natPair, monoFun]
  rw [h]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (monoFun_y_mem 1))
    (Submodule.smul_mem _ _ (monoFun_x_mem 1))

@[expose] noncomputable def natHom : (Fin 2 → F) →+ ↥(steinbergSub F F 1) :=
  AddMonoidHom.mk' (fun u => ⟨natPair u, natPair_mem u⟩) (fun u u' =>
    Subtype.ext (natPair_add u u'))

theorem natHom_equivariant (g : SLm F) (u : Fin 2 → F) :
    natHom ((g : Matrix (Fin 2) (Fin 2) F).mulVec u) = steinbergRep F F 1 g (natHom u) :=
  Subtype.ext (natPair_funRep g u).symm

theorem natHom_ne_zero : natHom (F := F) ≠ 0 := by
  intro h
  have h1 := congrArg Subtype.val (DFunLike.congr_fun h (Pi.single 0 1))
  have h2 := congrFun h1 (Pi.single 1 1)
  simp [natHom, natPair] at h2

end Natural

end CFSG.CGT.PushingUpLit.CGT6
