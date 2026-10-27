module


public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.IntegralDomain

public section

namespace CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic

open Representation

theorem isCyclic_of_fixedFree {F : Type*} [Field F] {A : Type*} [Group A] [Finite A]
    [IsMulCommutative A] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Nontrivial V] (ρ : Representation F A V)
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : V, ρ a v = v → v = 0) : IsCyclic A := by
  letI : CommGroup A := { ‹Group A› with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  let φ : MonoidAlgebra F A →ₐ[F] Module.End F V := asAlgebraHom ρ
  let R := MonoidAlgebra F A ⧸ RingHom.ker φ
  let ψ : R →ₐ[F] Module.End F V := Ideal.kerLiftAlg φ
  have hψ : Function.Injective ψ := Ideal.kerLiftAlg_injective φ
  have hfin : FiniteDimensional F R := inferInstance
  haveI : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg ψ h
    simp at this
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let g : A →* R := (Ideal.Quotient.mk (RingHom.ker φ) : _ →+* R).toMonoidHom.comp
    (MonoidAlgebra.of F A)
  let χ : A →* (R ⧸ m) := (Ideal.Quotient.mk m : R →+* (R ⧸ m)).toMonoidHom.comp g
  have hψg : ∀ a : A, ψ (g a) = ρ a := by
    intro a
    show ψ (Ideal.Quotient.mk (RingHom.ker φ) (MonoidAlgebra.of F A a)) = ρ a
    rw [show ψ (Ideal.Quotient.mk (RingHom.ker φ) (MonoidAlgebra.of F A a))
      = φ (MonoidAlgebra.of F A a) from Ideal.kerLiftAlg_mk φ _]
    simp [φ, MonoidAlgebra.of_apply, asAlgebraHom_single_one]
  haveI : Ideal.IsMaximal m := hm
  haveI : m.IsPrime := hm.isPrime
  haveI : IsArtinianRing R := IsArtinianRing.of_finite F R
  refine isCyclic_of_injective_ringHom (R := R ⧸ m) χ ?_
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  have hunit : IsUnit (g a - 1) := by
    apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff]
    have key : ∀ x : R, x * (g a - 1) = 0 → x = 0 := by
      intro x hx
      apply hψ
      rw [map_zero]
      apply LinearMap.ext
      intro v
      have h1 : ψ (x * (g a - 1)) = 0 := by rw [hx, map_zero]
      rw [map_mul, map_sub, map_one, hψg] at h1
      have hinj : Function.Injective (ρ a - 1 : Module.End F V) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro w hw
        apply hfree a hne w
        have : ρ a w - w = 0 := by simpa using hw
        exact sub_eq_zero.mp this
      obtain ⟨w, rfl⟩ := LinearMap.injective_iff_surjective.mp hinj v
      have h2 := LinearMap.congr_fun h1 w
      simpa using h2
    exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩
  have hmem : g a - 1 ∈ m := by
    have h : Ideal.Quotient.mk m (g a) = 1 := ha
    exact (Ideal.Quotient.eq (I := m)).mp (h.trans (Ideal.Quotient.mk m).map_one.symm)
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hmem hunit)

end CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic
