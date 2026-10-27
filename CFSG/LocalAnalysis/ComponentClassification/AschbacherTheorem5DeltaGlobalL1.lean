module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSplit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSB

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

@[expose] def Lemma613L1 : Prop :=
  SectionSixGlobalInputs → SectionSixLocalResults →
  ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ {a : Fin r} (d d' : DeltaDatum D Abar a), d'.g = d.g⁻¹ →
    IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) →
    IsSylowOf 2 (d'.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d'.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d'.g : Set G)) →
    (∀ x : G, rightConjugate (Subgroup.normalizer (D : Set G)) x ∈
        deltaConjugates (Subgroup.normalizer (D : Set G)) →
        sylowExp D Abar a x ≤ sylowExp D Abar a d.g) →
    IsMulCommutative d.T →
    IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G) →
    ¬ d.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d.g →
    ¬ d'.S ≤ rightConjugate (Subgroup.normalizer (D : Set G)) d'.g →
    Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) →
    AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a →
    (∃ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T ∧
      ¬ rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a) →
    Nat.card d.T < Nat.card (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G) →
    ∀ {P : Subgroup G}, IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g) →
    d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G) →
    IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G))
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g ⊓ Subgroup.normalizer (D : Set G)) →
    P ⊓ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) = d.T →
    ¬ P ≤ Subgroup.normalizer (D : Set G) →
    (∀ z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g,
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) →
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne (d.S ⊓
          Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) →
    (∃ z ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g,
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≤
        P ⊔ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ∧
      rightConjugate (AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) z ≠
        AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
          (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) →
    False

theorem lemma613Residual_of_L1 (hL1 : Lemma613L1) : Lemma613Residual := by
  intro hin hloc G _ _ D r Abar hC a d d' hgg hW hW' hmax hTab hWab hS hS' heq hVZ hnotZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : r = 2 := hloc.lemma_6_9 hC ⟨_, datum_mem_delta d⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate A d.g with hLdef
  set W := d.S ⊓ Subgroup.normalizer (L : Set G) with hWdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  obtain ⟨c₂, -, hc₂⟩ := swap_W d d' hgg hW'
  have hTW : Nat.card d.T ≤ Nat.card W := by
    have h1 : Nat.card d.T = Nat.card (d'.S ⊓ Subgroup.normalizer
        (rightConjugate A d'.g : Set G) : Subgroup G) := by rw [hc₂, rightConjugate_card]
    rw [h1, hW'.card_eq, hW.card_eq]
    exact Nat.pow_le_pow_right (by norm_num) (hmax d'.g (datum_mem_delta d'))
  obtain ⟨y, hy, hyN⟩ := exists_not_normalizer_of_card_le hloc hC (datum_mem_delta d) a
    d.sylowT hW hTW
  have hLH : ¬ L ⊓ H ≤ Subgroup.normalizer (A : Set G) := fun h => hyN (h hy)
  obtain ⟨P, hP, hTP, hWP, hPH, hPN⟩ := exists_sylow_L hC d
  have hPT : P ⊓ Subgroup.normalizer (A : Set G) = d.T :=
    le_antisymm hPN (le_inf hTP (d.sylowT.le.trans inf_le_right))
  by_cases hPle : P ≤ H
  · exact false_of_sylow_le hin hloc hC hr d hW hTab hWab hS heq hP hWP hPH hPT hPle
  have hnot : ∃ c ∈ A, rightConjugate U c ≤ d.S ⊔ U ∧ ¬ rightConjugate U c ≤ U ⊔ V := by
    obtain ⟨c, hc, hcS, hcZ⟩ := hnotZ
    exact ⟨c, hc, hcS, fun h => hcZ (h.trans (sup_le_sup_left hVZ U))⟩
  by_cases hL2 : ∃ z ∈ L, rightConjugate V z ≤ P ⊔ V ∧ ¬ rightConjugate V z ≤ U ⊔ V
  · obtain ⟨z, hz, hzP, hzK⟩ := hL2
    exact false_of_two_roots hloc hC hr d hW hLH hTab hWab heq hS hVZ hP hWP hPH hPT hPle hz hzP
      hzK hnot
  push Not at hL2
  by_cases hL0 : ∀ z ∈ L, rightConjugate V z ≤ P ⊔ V → rightConjugate V z = V
  · exact false_of_L_weaklyClosed hloc hC d hW hP hWP hPH hL0
  push Not at hL0
  rcases lt_or_eq_of_le hTW with hlt | heqTW
  · exact hL1 hin hloc hC d d' hgg hW hW' hmax hTab hWab hS hS' heq hVZ hnotZ hlt hP hWP hPH hPT
      hPle hL2 hL0
  · exact false_of_L_wcl hin hloc hC hr d hW hTab hWab heq heqTW.ge hP hWP hPH hPT hPle hL2

end DeltaGlobal

theorem theorem_6_4_of_L1 (hin : SectionSixGlobalInputs) (hloc : SectionSixLocalResults)
    (hL1 : DeltaGlobal.Lemma613L1) {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hC : Counterexample G D r Abar) :
    deltaConjugates (Subgroup.normalizer (D : Set G)) = ∅ :=
  theorem_6_4_of_residual hin hloc (DeltaGlobal.lemma613Residual_of_L1 hL1) hC

end CFSG.ComponentClassification.AschbacherTheorem5
