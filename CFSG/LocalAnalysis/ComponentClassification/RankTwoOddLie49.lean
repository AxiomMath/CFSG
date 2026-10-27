module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieCover
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieL2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieRee
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

variable {H : Type} [Group H] {B T X : Subgroup H}

@[expose] def ModelHighestRootData : Prop :=
  ∀ (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime), p ≠ 2 → IsFundTag t →
    StatedLieAdmissible t n p e → (t, n) ≠ (.PSL, 2) →
    ∀ (G : Type) [Group G] [Finite G], Open.IsQuasisimple G → IsPGroup 2 (center G) →
    ∀ φ : (modelUniv t n p e hp).K →* G, Function.Surjective φ →
      φ.ker ≤ center (modelUniv t n p e hp).K → Nonempty (HighestRootData G)

theorem Hyp46.as76b_4_9 [Finite H] (hI : OddLieInputs) (hHRD : ModelHighestRootData)
    (h : Hyp46 B T X) (hB : Open.IsQuasisimple B) (hZ : IsPGroup 2 (center B))
    (hL : OddLieType (B ⧸ center B)) :
    ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧
      Nonempty (B ≃* PSL(2, GaloisField p f)) ∧ T ≤ B ⊔ centralizer (B : Set H) ∧
      (p ^ f ≠ 5 → T ≤ B) := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hLM⟩ := hL
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  by_cases hG : t = .twistedG2
  · subst hG
    exfalso
    have hR := reeTitsModel_of_lieModel hLM
    have hp3 : p = 3 := hR.1.2.2.2.1
    subst hp3
    have hZ1 : center B = ⊥ := hI.ree B hB hZ ⟨f, hR⟩
    have eZ : B ≃* B ⧸ center B :=
      ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm
    exact h.false_of_smallRee hB (CFSG.SectionRank.reeTitsModel_of_mulEquiv eZ hR)
  have hFT := isFundTag_of_admissible hadm hp2 hG
  obtain ⟨φ, hφs, hφk⟩ := exists_surjective_of_lieModel hB hZ hp hp2 hFT hadm hLM
  by_cases hPSL : (t, n) = (.PSL, 2)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPSL
    have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have hF : Odd (Nat.card (GaloisField p f)) := by
      rw [hK]; exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    have h5 : 5 ≤ p ^ f := by
      obtain ⟨-, -, -, h22, h23⟩ := hadm
      have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
      have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      by_contra hcon
      push Not at hcon
      have : p ^ f = 3 ∨ p ^ f = 4 := by omega
      rcases this with h3 | h4
      · exact h23 (by rw [h3])
      · have := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow (n := f)
        rw [h4] at this
        exact absurd this (by decide)
    rcases sl2_or_psl2_of_surjective (F := GaloisField p f) φ hφs hφk with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact (h.false_of_sl2 e hF).elim
    · obtain ⟨hq, hin, hT⟩ := h.as76b_4_10_psl2 hp2 hf h5 e
      exact ⟨p, f, inferInstance, hp2, hf, hq, ⟨e⟩, hin, hT⟩
  · obtain ⟨D⟩ := hHRD t n p f hp hp2 hFT hadm hPSL B hB hZ φ hφs hφk
    exact (h.false_of_highestRootData hB D).elim

end CFSG.ComponentClassification.RankTwoOddLie
