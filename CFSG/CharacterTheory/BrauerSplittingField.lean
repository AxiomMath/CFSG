module

public import CFSG.ThirdParty.BrauerInduction.Main
public import CFSG.CharacterTheory.BrauerSplittingField.CyclotomicLift
public import CFSG.CharacterTheory.BrauerSplittingField.Assembly

public section

namespace CFSG

open scoped TensorProduct
open BigOperators

namespace BrauerSplittingField

theorem brauer_splitting_field (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ (φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ)
      (W : Type) (_ : AddCommGroup W)
      (_ : Module (CyclotomicField (Monoid.exponent G) ℚ) W)
      (σ : Representation (CyclotomicField (Monoid.exponent G) ℚ) G W),
      letI : Algebra (CyclotomicField (Monoid.exponent G) ℚ) ℂ := φ.toAlgebra
      ∃ (f : (ℂ ⊗[CyclotomicField (Monoid.exponent G) ℚ] W) ≃ₗ[ℂ] V),
        ∀ (g : G) (x : ℂ ⊗[CyclotomicField (Monoid.exponent G) ℚ] W),
          f ((σ g).baseChange ℂ x) = ρ g (f x) := by
  let φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ :=
    Classical.choice inferInstance
  refine ⟨φ, ?_⟩
  let : Algebra (CyclotomicField (Monoid.exponent G) ℚ) ℂ := φ.toAlgebra
  obtain ⟨ι, instι, ns, Hs, ψs, -, hBrauer⟩ :=
    BrauerInduction.character_eq_sum_induced_linear (FDRep.of ρ)
  let : Fintype ι := instι
  let S : ι → FDRep (CyclotomicField (Monoid.exponent G) ℚ) G :=
    fun i => FDRep.indLin (Hs i) (descendLinearChar φ (Hs i) (ψs i))
  have hS (i : ι) :
      (FDRep.baseChange (A := ℂ) (S i)).character =
        (FDRep.indLin (Hs i) (ψs i)).character := by
    dsimp only [S]
    exact baseChange_indLin_character φ (Hs i) (ψs i)
  have hchar :
      (FDRep.of ρ).character =
        ∑ i, ns i • (FDRep.baseChange (A := ℂ) (S i)).character := by
    rw [hBrauer]
    apply Finset.sum_congr rfl
    intro i _
    rw [hS i]
  obtain ⟨W, ⟨e⟩⟩ :=
    Helpers.exists_baseChange_iso_of_integral_character (FDRep.of ρ) S ns hchar
  refine ⟨W, inferInstance, inferInstance, W.ρ, ?_⟩
  exact Helpers.exists_linearEquiv_of_baseChange_iso ρ W e

end BrauerSplittingField

end CFSG
