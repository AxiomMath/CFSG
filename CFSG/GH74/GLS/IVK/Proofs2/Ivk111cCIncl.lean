module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct

section Incl

variable (F k : Type) [Field F] [Field k] [Algebra F k]

@[expose] def steinbergInclFun : ((Fin 2 → F) → F) →ₗ[F] ((Fin 2 → F) → k) :=
  LinearMap.compLeft (Algebra.linearMap F k) (Fin 2 → F)

theorem steinbergInclFun_apply (f : (Fin 2 → F) → F) (v : Fin 2 → F) :
    steinbergInclFun F k f v = algebraMap F k (f v) := rfl

theorem steinbergInclFun_funRep (g : SLm F) (f : (Fin 2 → F) → F) :
    steinbergInclFun F k (funRep F F g f) = funRep F k g (steinbergInclFun F k f) := rfl

theorem steinbergInclFun_monoFun (A : ℕ) : steinbergInclFun F k (monoFun F F A 0) = monoFun F k A 0 := by
  funext v
  simp [steinbergInclFun_apply, monoFun]

theorem steinbergInclFun_injective : Function.Injective (steinbergInclFun F k) := by
  intro f g h
  funext v
  exact (algebraMap F k).injective (congrFun h v)

theorem steinbergInclFun_mem (A : ℕ) {f : (Fin 2 → F) → F} (hf : f ∈ steinbergSub F F A) :
    steinbergInclFun F k f ∈ steinbergSub F k A := by
  unfold steinbergSub at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [steinbergInclFun_funRep, steinbergInclFun_monoFun]
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ c hx

@[expose] noncomputable def steinbergInclSub (A : ℕ) : steinbergSub F F A →ₗ[F] steinbergSub F k A where
  toFun x := ⟨steinbergInclFun F k x, steinbergInclFun_mem F k A x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (by simp)

theorem steinbergInclSub_injective (A : ℕ) : Function.Injective (steinbergInclSub F k A) := by
  intro x y h
  apply Subtype.ext
  exact steinbergInclFun_injective F k (congrArg Subtype.val h)

theorem steinbergInclSub_rep (A : ℕ) (g : SLm F) (x : steinbergSub F F A) :
    steinbergInclSub F k A (steinbergRep F F A g x) = steinbergRep F k A g (steinbergInclSub F k A x) := rfl

@[expose] noncomputable def steinbergMulSub (A : ℕ) : k ⊗[F] steinbergSub F F A →ₗ[k] steinbergSub F k A :=
  (steinbergInclSub F k A).liftBaseChange k

theorem steinbergMulSub_tmul (A : ℕ) (c : k) (x : steinbergSub F F A) :
    steinbergMulSub F k A (c ⊗ₜ[F] x) = c • steinbergInclSub F k A x := rfl

theorem steinbergMulSub_rep (A : ℕ) (g : SLm F) (x : k ⊗[F] steinbergSub F F A) :
    steinbergMulSub F k A ((CFSG.Theory.Representation.extendScalars k (steinbergRep F F A) g) x) =
      steinbergRep F k A g (steinbergMulSub F k A x) := by
  induction x with
  | tmul c x =>
    rw [CFSG.Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul, steinbergMulSub_tmul,
      steinbergMulSub_tmul, steinbergInclSub_rep, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Incl

end CFSG.GH74.GLS.Stage4.Rest
