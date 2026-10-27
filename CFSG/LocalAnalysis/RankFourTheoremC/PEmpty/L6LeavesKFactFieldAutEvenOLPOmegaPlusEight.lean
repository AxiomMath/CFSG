module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLFlagEmbed
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPOEightArith
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj StatedOmega
  StatedQuadPlus)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.LieType.BorelTits (quadPlusForm)
open Matrix

namespace OLEight

theorem statedOmega_preserves_polar (n : ℕ) (F : Type) [Field F] :
    ∀ A ∈ StatedOmega (StatedQuadPlus n F), ∀ u v : Fin n ⊕ Fin n → F,
      (quadPlusForm n F).polar.β ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ u)
        ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
        (quadPlusForm n F).polar.β u v := fun A hA u v =>
  (quadPlusForm n F).polar_map_of_Q
    (g := Matrix.toLin' ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)))
    (fun w => CFSG.LieType.BorelTits.orthGroup_preserves (StatedQuadPlus n F)
      (CFSG.LieType.BorelTits.statedOmega_le_orthGroup _ hA) w) u v

end OLEight

theorem twoLocalWhen_POmegaPlus_eight : TwoLocalWhen .POmegaPlus (fun n f₀ => n = 4 ∧ f₀ = 1) := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  obtain ⟨rfl, rfl⟩ := hP
  have hcl0 : StatedClassicalModel K .POmegaPlus 4 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hfp : f = p := by rw [hf, mul_one]
  have hp6 := OLThreeAdic.prime_mod_six hp hp5
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ := hcl0
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  have hq : Nat.card F = 2 ^ p := by rw [hFcard, hfp]
  have hcard : Fintype.card (Fin 4 ⊕ Fin 4) = 8 := by simp
  refine ⟨3, Nat.prime_three, fun R hR2 hR1 => ?_⟩
  have hle := OLFlag.padicValNat_three_card_normalizer_le_of_isometries_of_equiv e
    (quadPlusForm 4 F).polar (OLEight.statedOmega_preserves_polar 4 F) 4
    (fun k hk1 hk2 => by
      rw [hcard] at hk2 ⊢
      exact OLEight.levi_bound_eight hq hp6 k hk1 hk2) R hR2 hR1
  have hd := OLEight.lieOrderDivisor_POmegaPlus_four
  have h5 := OLEight.five_le_padicValNat_numerator_POmegaPlus_four
  rw [hd, padicValNat.one]
  omega

theorem overgroupLocalWhen_POmegaPlus_eight (hOver : CFSG.Quasithin.AsLieTwoOvergroups) :
    OvergroupLocalWhen .POmegaPlus (fun n f₀ => n = 4 ∧ f₀ = 1) :=
  overgroupLocalWhen_of_twoLocalWhen hOver twoLocalWhen_POmegaPlus_eight

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
