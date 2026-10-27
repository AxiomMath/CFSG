module

public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
import CFSG.FeitThompson.Representations.CyclicTIIsometryUnique
import CFSG.FeitThompson.Representations.ConjugatePairsDisjointBlocksCoherence
import CFSG.FeitThompson.Representations.OddNormalInducedBlocksConjPairs
import CFSG.FeitThompson.Representations.CoherentExtensionNonrealConjPairs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

theorem star_mem_virtualChars {X : Type*} [Group X] [Finite X] {f : X → ℂ}
    (hf : f ∈ virtualChars X) : star f ∈ virtualChars X := by
  rw [virtualChars_eq_span_Irr] at hf ⊢
  exact star_mem_span_of_star_mem (fun _ hχ => star_mem_Irr hχ) hf

variable {X Y : Type*} [Group X] [Group Y]

def classFun.starₗ (X : Type*) [Group X] : classFun X →ₗ⋆[ℂ] classFun X where
  toFun f := ⟨star (f : X → ℂ), star_mem_classFun f.2⟩
  map_add' f g := Subtype.ext (star_add (f : X → ℂ) g)
  map_smul' c f := Subtype.ext (star_smul c (f : X → ℂ))

@[simp]
theorem classFun.coe_starₗ (f : classFun X) :
    (classFun.starₗ X f : X → ℂ) = star (f : X → ℂ) := (rfl)

theorem classFun.starₗ_apply_apply (f : classFun X) (x : X) :
    (classFun.starₗ X f : X → ℂ) x = conj ((f : X → ℂ) x) := (rfl)

@[simp]
theorem classFun.starₗ_starₗ (f : classFun X) :
    classFun.starₗ X (classFun.starₗ X f) = f := Subtype.ext (star_star _)

@[simp]
theorem classFun.starₗ_principalClassFun :
    classFun.starₗ X (principalClassFun X) = principalClassFun X := Subtype.ext (by simp)

theorem classFun.cfInner_starₗ_starₗ [Fintype X] (f h : classFun X) :
    cfInner (classFun.starₗ X f : X → ℂ) (classFun.starₗ X h : X → ℂ)
      = conj (cfInner (f : X → ℂ) (h : X → ℂ)) := by
  simp [cfInner_star_star]

def classFun.starConj (σ : classFun X →ₗ[ℂ] classFun Y) : classFun X →ₗ[ℂ] classFun Y where
  toFun f := classFun.starₗ Y (σ (classFun.starₗ X f))
  map_add' f g := by simp
  map_smul' c f := by simp

@[simp]
theorem classFun.starConj_apply (σ : classFun X →ₗ[ℂ] classFun Y) (f : classFun X) :
    classFun.starConj σ f = classFun.starₗ Y (σ (classFun.starₗ X f)) := (rfl)

theorem classFun.coe_starConj_apply (σ : classFun X →ₗ[ℂ] classFun Y) (f : classFun X) :
    (classFun.starConj σ f : Y → ℂ) = star (σ (classFun.starₗ X f) : Y → ℂ) := (rfl)

@[simp]
theorem classFun.starConj_starConj (σ : classFun X →ₗ[ℂ] classFun Y) :
    classFun.starConj (classFun.starConj σ) = σ := by
  ext f x
  simp

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIIsometry

theorem starConj (hσ : IsCyclicTIIsometry W W1 W2 σ) :
    IsCyclicTIIsometry W W1 W2 (classFun.starConj σ) where
  inner_eq f h := by
    simp only [classFun.starConj_apply, classFun.coe_starₗ, cfInner_star_star, hσ.inner_eq,
      Complex.conj_conj]
  map_virtualChars f hf := by
    simp only [classFun.starConj_apply, classFun.coe_starₗ]
    exact star_mem_virtualChars (hσ.map_virtualChars _ (by
      simpa [classFun.coe_starₗ] using star_mem_virtualChars hf))
  map_principalClassFun := by simp [hσ.map_principalClassFun]
  eq_indClassFun f hf := by
    have hstar : (σ (classFun.starₗ ↥W f) : G → ℂ) = indClassFun W (star (f : ↥W → ℂ)) :=
      hσ.eq_indClassFun _ fun x hx => by simp [hf x hx]
    simp only [classFun.starConj_apply, classFun.coe_starₗ, hstar]
    rw [show (star (indClassFun W (star (f : ↥W → ℂ))) : G → ℂ)
        = fun y => conj (indClassFun W (star (f : ↥W → ℂ)) y) from rfl, conj_indClassFun]
    simp

theorem starConj_eq_self (h : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ) :
    classFun.starConj σ = σ :=
  eq_of_isCyclicTIIsometry h hσ.starConj hσ

theorem map_starₗ (h : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (f : classFun ↥W) : σ (classFun.starₗ ↥W f) = classFun.starₗ G (σ f) := by
  have hf := congrArg (fun u : classFun ↥W →ₗ[ℂ] classFun G => u f) (hσ.starConj_eq_self h)
  simp only [classFun.starConj_apply] at hf
  rw [← hf, classFun.starₗ_starₗ]

theorem apply_starₗ_apply (h : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ)
    (f : classFun ↥W) (g : G) :
    (σ (classFun.starₗ ↥W f) : G → ℂ) g = conj ((σ f : G → ℂ) g) := by
  rw [hσ.map_starₗ h f, classFun.starₗ_apply_apply]

end IsCyclicTIIsometry

end CFSG.FeitThompson

end
