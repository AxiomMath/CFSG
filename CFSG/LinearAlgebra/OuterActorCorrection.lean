module

public import Mathlib.LinearAlgebra.Prod

public section

namespace CFSG.LinearAlgebra

variable {R I A T : Type*} [CommRing R]
  [AddCommGroup I] [Module R I] [AddCommGroup A] [Module R A]
  [AddCommGroup T] [Module R T]

theorem outer_actor_correction (ι : I →ₗ[R] A) (φ : A →ₗ[R] T)
    (f g : T →ₗ[R] R) (χ : A →ₗ[R] R) (hχι : χ.comp ι = 0)
    (hsurj : Function.Surjective
      ((f.comp (φ.comp ι)).prod (g.comp (φ.comp ι)))) (a : A) :
    ∃ i : I, f (φ (a + ι i)) = 0 ∧ g (φ (a + ι i)) = 0 ∧
      χ (a + ι i) = χ a := by
  obtain ⟨i, hi⟩ := hsurj (-f (φ a), -g (φ a))
  have hf : f (φ (ι i)) = -f (φ a) := congrArg Prod.fst hi
  have hg : g (φ (ι i)) = -g (φ a) := congrArg Prod.snd hi
  have hχ : χ (ι i) = 0 := DFunLike.congr_fun hχι i
  exact ⟨i, by rw [map_add, map_add, hf, add_neg_cancel],
    by rw [map_add, map_add, hg, add_neg_cancel],
    by rw [map_add, hχ, add_zero]⟩

end CFSG.LinearAlgebra
