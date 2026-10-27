module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpInner
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpClause
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem oddA6Shape_PSp (hO : LieOrderFormulasInput) (hgls : GLS3OddFamilyInput .PSp) :
    OddA6Shape .PSp := by
  apply oddA6Shape_of_concrete
  intro S _ _ n p f hp hp2 hadm hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel' hadm hm
  refine ⟨StatedProj (StatedSp n K), inferInstance, inferInstance, e, ?_⟩
  intro σ D hσ hD
  have hn : 2 ≤ n := hadm.2.2.1
  have hf : 1 ≤ f := hadm.2.1
  have hmX : LieModel (StatedProj (StatedSp n K)) .PSp n p f :=
    Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hp3 : p = 3 := hD.char_three hO hgls hp hp2 hadm hmX hσ
  subst hp3
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have hβ2 : σ * σ = 1 := by
    have h2 := pow_orderOf_eq_one σ
    rw [hσ] at h2
    rw [← pow_two]
    exact h2
  have hβ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨A, τ, hAτ, hτ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar hn).2.2 σ hβ2 hβ1
  by_cases hτ : τ = 1
  · subst hτ
    rw [map_one, mul_one] at hAτ
    subst hAτ
    haveI : NeZero n := ⟨by omega⟩
    rcases inner_dichotomy_sp hO hn hf hK A hσ with hbig | ⟨hn2, hf1 | ⟨hf2, c, hAA, hJ, hP⟩⟩
    · exact (hD.false_of_perfectBig3 (by omega) hbig).elim
    · subst hn2
      subst hf1
      exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))),
        fun _ _ h => absurd h (by norm_num)⟩
    · subst hn2
      subst hf2
      refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))),
        fun _ _ _ => ?_⟩
      have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
      have : Fintype K := Fintype.ofFinite K
      have hi : IsSquare (-1 : K) := by
        rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK9]
        norm_num
      exact clause_psp hf hK hi (by omega) hσ hAA hJ hP hD
  · exact (a6_field_false hn hf hK A τ hAτ hτ2 hτ d hd hD).elim

end CFSG.ComponentClassification.CatFC
