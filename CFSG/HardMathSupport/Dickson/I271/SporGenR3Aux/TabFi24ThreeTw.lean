module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24TwinFacts
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Twin
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeFix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (PConstrainedShape)
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false

section Constrained


theorem isPGroup_of_fixFacts {w : List ℕ} {y : ℕ} (hF : FixFacts w y)
    (hbound : ∀ H : Subgroup CFSG.Sporadic.Fi24.J, (∀ g ∈ H, (∀ t < 3, idx 306936 g chainBase[t]! = chainBase[t]!) ∧
      idx 306936 g y = y) → Nat.card H ∣ 3 ^ 12) (H : Subgroup CFSG.Sporadic.Fi24.J)
    (hH : ∀ g ∈ H, g * wordElt w = wordElt w * g ∧
      ∀ f : Fin 306936, wordElt w • f = f → g • f = f) : IsPGroup 3 H := by
  have hdvd : Nat.card H ∣ 3 ^ 12 := by
    refine hbound H fun g hg => ⟨fun t ht => ?_, ?_⟩
    · have hlt := CFSG.Sporadic.Fi24.chainBase_get_lt
        (show t < chainBase.size by rw [CFSG.Sporadic.Fi24.chainBase_size]; omega)
      have hs : wordElt w • (⟨chainBase[t]!, hlt⟩ : Fin 306936) = ⟨chainBase[t]!, hlt⟩ := by
        apply Fin.ext
        rw [← idx_of_lt _ hlt]
        exact hF.fix0 t ht
      have := (hH g hg).2 _ hs
      rw [idx_of_lt _ hlt, this]
    · have hs : wordElt w • (⟨y, hF.y_lt⟩ : Fin 306936) = ⟨y, hF.y_lt⟩ := by
        apply Fin.ext
        rw [← idx_of_lt _ hF.y_lt]
        exact hF.fixy
      have := (hH g hg).2 _ hs
      rw [idx_of_lt _ hF.y_lt, this]
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  exact IsPGroup.of_card hn

theorem pConstrainedShape_of_twinFacts {w : List ℕ} {y : ℕ} (hF : FixFacts w y)
    (hbound : ∀ H : Subgroup CFSG.Sporadic.Fi24.J, (∀ g ∈ H, (∀ t < 3, idx 306936 g chainBase[t]! = chainBase[t]!) ∧
      idx 306936 g y = y) → Nat.card H ∣ 3 ^ 12) (htw : TwinFacts w) :
    PConstrainedShape 3 (Subgroup.centralizer ({wordElt w} : Set CFSG.Sporadic.Fi24.J)) := by
  have hfix : ∀ a : Fin 306936, jR (wordElt w) • a = a ↔ wordElt w • a = a := fun a => by
    rw [CFSG.Sporadic.Fi24.jR_smul]
  refine pConstrainedShape_of_twins (R := R) (ι := Fin 306936) jR cls (wordElt w)
    (fun g i => CFSG.Sporadic.Fi24.jR_smul g i) CFSG.Sporadic.Fi24.jR_injective
    (fun r i => CFSG.Sporadic.Fi24.cls_smul_R r i) ?_ htw.hK2 ?_ ?_ ?_ ?_
  · intro a ha
    exact htw.hK1 a ((hfix a).2 ha)
  · intro a b hab
    exact exists_jR_cls_mul_cls ((hfix a).1 hab.1) ((hfix b).1 hab.2.1)
  · intro a b hab
    rw [pow_three']
    exact cls_cube hab.2.2.2.1
  · intro a₁ b₁ a₂ b₂ a₃ b₃ h₁ h₂ h₃ f hf
    exact htw.hK3 a₁ b₁ a₂ b₂ a₃ b₃ h₁ h₂ h₃ f ((hfix f).2 hf)
  · intro H hH
    exact isPGroup_of_fixFacts hF hbound H hH

end Constrained

end CFSG.HardMathSupport.Dickson.I271.TabFi24
