module


public import Mathlib.Algebra.Central.End
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleRepresentationMatrixSpan

public section

namespace CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter

theorem exists_character {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    {E : Type*} [Group E] [Finite E] (σ : Representation F E V)
    (hfaith : Function.Injective σ) (hirr : σ.IsIrreducible) :
    ∃ χ : Subgroup.center E →* Fˣ, Function.Injective χ ∧
      ∀ z : Subgroup.center E, σ (z : E) = (χ z : F) • (LinearMap.id : V →ₗ[F] V) := by
  classical
  have hspan := IrreducibleRepresentationMatrixSpan.span_eq_top σ hirr
  have hex : ∀ z : Subgroup.center E, ∃ c : F, σ (z : E) = c • (LinearMap.id : V →ₗ[F] V) := by
    intro z
    have hcent : σ (z : E) ∈ Subsemiring.center (Module.End F V) := by
      rw [Subsemiring.mem_center_iff]
      intro T
      have hT : T ∈ Submodule.span F (Set.range σ) := by rw [hspan]; trivial
      induction hT using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 z.2 g)]
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
      | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]
    obtain ⟨α, h1, hα⟩ := Module.End.mem_subsemiringCenter_iff.1 hcent
    refine ⟨α, ?_⟩
    rw [hα]
    ext v
    simp [Module.End.smulLeft]
  choose s hs using hex
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hinj : ∀ a b : F, a • (LinearMap.id : V →ₗ[F] V) = b • LinearMap.id → a = b := by
    intro a b h
    have := congrArg (fun f : V →ₗ[F] V => f v) h
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
    exact smul_left_injective F hv this
  let m : Subgroup.center E →* F :=
    { toFun := s
      map_one' := by
        apply hinj
        rw [← hs, one_smul]
        exact map_one σ
      map_mul' := by
        intro x y
        apply hinj
        rw [← hs]
        have : σ ((x * y : Subgroup.center E) : E) = σ (x : E) * σ (y : E) := by
          rw [← map_mul]; rfl
        rw [this, hs x, hs y]
        ext w
        simp [mul_smul, smul_comm (s y)] }
  refine ⟨m.toHomUnits, ?_, ?_⟩
  · intro x y h
    have h' : s x = s y := by simpa [m] using congrArg Units.val h
    apply Subtype.ext
    apply hfaith
    rw [hs x, hs y, h']
  · intro z
    exact hs z

end CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter
