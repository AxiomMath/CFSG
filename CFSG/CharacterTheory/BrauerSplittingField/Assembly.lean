module

public import CFSG.CharacterTheory.BrauerSplittingField.Virtual
public import CFSG.CharacterTheory.BrauerSplittingField.Complement

public section

namespace CFSG

open CategoryTheory CategoryTheory.Limits BigOperators
open scoped TensorProduct

namespace BrauerSplittingField.Helpers

noncomputable section

universe u

theorem exists_baseChange_iso_of_integral_character
    {K L G : Type u}
    [Field K] [Field L] [Algebra K L]
    [Infinite K] [CharZero K] [CharZero L] [IsAlgClosed L]
    [Group G] [Fintype G]
    {ι : Type} [Fintype ι]
    (V : FDRep L G) (S : ι → FDRep K G) (n : ι → ℤ)
    (hchar : V.character =
      ∑ i, n i • (FDRep.baseChange (A := L) (S i)).character) :
    ∃ W : FDRep K G, Nonempty (FDRep.baseChange (A := L) W ≅ V) := by
  let SC : ι → FDRep L G := fun i => FDRep.baseChange (A := L) (S i)
  let N : FDRep K G := BrauerSplittingField.Virtual.negativeRep S n
  let P : FDRep K G := BrauerSplittingField.Virtual.positiveRep S n
  have hvirtualSC :
      (V ⊞ BrauerSplittingField.Virtual.negativeRep SC n).character =
        (BrauerSplittingField.Virtual.positiveRep SC n).character :=
    BrauerSplittingField.Virtual.character_biprod_negative_eq_positive V SC n hchar
  have hN :
      (FDRep.baseChange (A := L) N).character =
        (BrauerSplittingField.Virtual.negativeRep SC n).character := by
    exact BrauerSplittingField.Virtual.character_baseChange_negativeRep S n
  have hP :
      (FDRep.baseChange (A := L) P).character =
        (BrauerSplittingField.Virtual.positiveRep SC n).character := by
    exact BrauerSplittingField.Virtual.character_baseChange_positiveRep S n
  have hvirtual :
      (V ⊞ FDRep.baseChange (A := L) N).character =
        (FDRep.baseChange (A := L) P).character := by
    calc
      (V ⊞ FDRep.baseChange (A := L) N).character =
          V.character + (FDRep.baseChange (A := L) N).character :=
        FDRep.char_biprod_eq_add _ _
      _ = V.character +
          (BrauerSplittingField.Virtual.negativeRep SC n).character := by rw [hN]
      _ = (V ⊞ BrauerSplittingField.Virtual.negativeRep SC n).character :=
        (FDRep.char_biprod_eq_add _ _).symm
      _ = (BrauerSplittingField.Virtual.positiveRep SC n).character := hvirtualSC
      _ = (FDRep.baseChange (A := L) P).character := hP.symm
  let e : V ⊞ FDRep.baseChange (A := L) N ≅
      FDRep.baseChange (A := L) P := FDRep.iso_of_char_eq hvirtual
  let j : FDRep.baseChange (A := L) N ⟶
      FDRep.baseChange (A := L) P := biprod.inr ≫ e.hom
  have : Mono j := by
    dsimp only [j]
    infer_instance
  have hj : Function.Injective (FDRep.homToLinearMap j) :=
    (FDRep.mono_iff_injective j).1 inferInstance
  obtain ⟨q, hq⟩ := exists_injective_fdrep_hom_of_baseChange N P j hj
  obtain ⟨W, hW⟩ := exists_character_complement N P q hq
  exact ⟨W, ⟨baseChangeComplementIso V N P W hvirtual hW⟩⟩

lemma exists_linearEquiv_of_baseChange_iso
    {K L G V : Type u}
    [Field K] [Field L] [Algebra K L]
    [Group G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) (W : FDRep K G)
    (e : FDRep.baseChange (A := L) W ≅ FDRep.of ρ) :
    ∃ (f : (L ⊗[K] W) ≃ₗ[L] V),
      ∀ (g : G) (x : L ⊗[K] W),
        f ((W.ρ g).baseChange L x) = ρ g (f x) := by
  let f : (L ⊗[K] W) ≃ₗ[L] V := FDRep.isoToLinearEquiv e
  refine ⟨f, ?_⟩
  intro g x
  exact FDRep.homToLinearMap_comm e.hom g x

end

end BrauerSplittingField.Helpers

end CFSG
