module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LieType.BorelTits

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {K : Type v} [Field K]

@[expose] noncomputable def natRep (H : Subgroup (GL ι K)) : H →* Module.End K (ι → K) :=
  ((Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toMonoidHom).comp
    ((Units.coeHom (Matrix ι ι K)).comp H.subtype)

@[simp] theorem natRep_apply (H : Subgroup (GL ι K)) (h : H) (v : ι → K) :
    natRep H h v = Matrix.mulVec ((h : GL ι K) : Matrix ι ι K) v := by
  simp [natRep, Matrix.toLinAlgEquiv'_apply]

theorem natRep_injective (H : Subgroup (GL ι K)) : Function.Injective (natRep H) := by
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  have : ((a : GL ι K) : Matrix ι ι K).toLin' = ((b : GL ι K) : Matrix ι ι K).toLin' := by
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun f : Module.End K (ι → K) => f v) hab
    simpa using this
  exact Matrix.toLin'.injective this

end CFSG.LieType.BorelTits
