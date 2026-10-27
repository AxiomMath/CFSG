module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem conjSL_injective {K : Type} [Field K] (P : GL (Fin 2) K) :
    Function.Injective (conjSL P) := fun A B h => by
  have := congrArg (conjSL P⁻¹) h
  rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at this

theorem card_eq_card_comap_of_injective {A B : Type*} [Group A] [Group B] (ρ : A →* B)
    (hρ : Function.Injective ρ) (Y : Subgroup B) (hY : Y ≤ ρ.range) :
    Nat.card Y = Nat.card (Y.comap ρ) := by
  have h := Subgroup.map_comap_eq_self hY
  conv_lhs => rw [← h]
  exact Subgroup.card_map_of_injective hρ

theorem dvd_card_of_comap_eq_conj {τ : Tag} {K K₂ : Type} [Field K] [Finite K] [Field K₂]
    [Algebra K K₂] {β : Fin τ.rank → ℤ} (hρ : Function.Injective (rootSL2 τ K₂ β))
    {Y : Subgroup (ModGL τ K₂)} (hY : Y ≤ rootRankOneGroup τ K₂ β) (P : GL (Fin 2) K₂)
    (hP : Y.comap (rootSL2 τ K₂ β) =
      (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P)) {p : ℕ}
    (hpq : p ∣ Nat.card K + 1) : p ∣ Nat.card Y := by
  have h1 := card_eq_card_comap_of_injective (rootSL2 τ K₂ β) hρ Y hY
  rw [hP, Subgroup.card_map_of_injective (conjSL_injective P),
    Nat.card_congr (MonoidHom.ofInjective (f := Matrix.SpecialLinearGroup.map (algebraMap K K₂))
      (fun A B h => by
        ext i j
        have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K₂ =>
          (M : Matrix (Fin 2) (Fin 2) K₂) i j) h
        simpa using (algebraMap K K₂).injective this)).toEquiv.symm,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1
  rw [h1]
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hsq : Nat.card K + 1 ∣ Nat.card K ^ 2 - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    zify [hq, Nat.one_le_pow 2 _ hq]
    ring
  exact Dvd.dvd.mul_left (hpq.trans hsq) _

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
