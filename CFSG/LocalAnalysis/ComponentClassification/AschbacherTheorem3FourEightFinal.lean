module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTypes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open FourEight

theorem theorem48_step (h46 : Lemma46Statement) (hin : Theorem48Inputs)
    (X : Type) [Group X] [Finite X] (G T S Q H : Subgroup X)
    (IH : Theorem48Below (Nat.card (G ⊔ T : Subgroup X))) (h : SylowFrame G T S)
    (h43 : Hyp43 G T Q H) (hsize : T.relIndex (S ⊓ H) ≤ Nat.card T)
    (hO : CFSG.oddCore G = ⊥) (hm : 1 < CFSG.Open.pRank 2 T) : Conclusion48 G T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS := h.le
  have hS2 := h.sylow.isPGroup
  have hSGT := h.sylow.le
  by_cases hW : relativeWeakClosure G T S = T
  ·
    left
    have hwc : ∀ g ∈ G, rightConjugate T g ≤ S → rightConjugate T g = T := by
      intro g hg hle
      have h1 := rightConjugate_le_relativeWeakClosure hg hle
      rw [hW] at h1
      exact Subgroup.eq_of_le_of_card_ge h1 (by rw [rightConjugate_card])
    have hc := lemma_4_2 h hwc hO
    rw [hW]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (Subgroup.centralizer_le_normalizer _)
  have hT : T ≠ ⊥ := by
    rintro rfl
    exact hW (relativeWeakClosure_bot G S)
  obtain ⟨g, hg, hgN, hne⟩ := exists_conj_le_normalizer h.toFrame hS2 hSGT hTS hW
  have hNH : S ⊓ Subgroup.normalizer (T : Set X) ≤ H :=
    (inf_le_inf_right _ hSGT).trans (h43.normalizer_le h.toFrame hT)
  have hgSH : rightConjugate T g ≤ S ⊓ H := le_inf (hgN.trans inf_le_left) (hgN.trans hNH)
  obtain ⟨-, hinf, -, -⟩ := lemma_4_4_two h.toFrame h43 hS2 hTS hg hgSH hne
  have hKN : rightConjugate T g ≤ Subgroup.normalizer (T : Set X) := hgN.trans inf_le_right
  have hcardM : Nat.card (T ⊔ rightConjugate T g : Subgroup X) = Nat.card T * Nat.card T := by
    rw [card_sup_of_le_normalizer hKN hinf, rightConjugate_card]
  have hMle : T ⊔ rightConjugate T g ≤ H ⊓ S :=
    le_inf (sup_le h43.le_H (hgSH.trans inf_le_right)) (sup_le hTS (hgSH.trans inf_le_left))
  have hcardHS : Nat.card (H ⊓ S : Subgroup X) ≤ Nat.card T * Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card T (S ⊓ H)
    rw [inf_eq_left.mpr (le_inf hTS h43.le_H)] at h1
    rw [inf_comm, ← h1]
    exact Nat.mul_le_mul_right _ hsize
  have hHS : H ⊓ S = T ⊔ rightConjugate T g :=
    (Subgroup.eq_of_le_of_card_ge hMle (hcardHS.trans hcardM.ge)).symm
  have h45 : Hyp45 G T S Q H g :=
    { sylowFrame := h
      hyp43 := h43
      mem := hg
      ne := hne
      weakClosure := le_antisymm (by rw [← hHS]; exact relative_weak_closure_le _ _ _)
        (sup_le (subgroup_le_relative_weak_closure _ _ _ (hHS ▸ le_sup_left))
          (rightConjugate_le_relativeWeakClosure hg (hHS ▸ le_sup_right))) }
  by_cases hWM : relativeWeakClosure G T S = T ⊔ rightConjugate T g
  ·
    rcases h46 X G T S Q H g h h43 hT hO hg hWM hKN with h1 | h1 | h1
    · omega
    · exact Or.inl (le_sup_left.trans h1)
    · obtain ⟨n, hK, hEL, hcomm, hel, hcard, hB⟩ := h1
      exact Or.inr (bender_case h h43 h45 hHS hWM hK hEL hcomm hel hcard hB)
  have hMeq : relativeWeakClosure G T (T ⊔ rightConjugate T g) = T ⊔ rightConjugate T g :=
    le_antisymm (relative_weak_closure_le _ _ _)
      (sup_le (subgroup_le_relative_weak_closure _ _ _ le_sup_left)
        (rightConjugate_le_relativeWeakClosure hg le_sup_right))
  obtain ⟨y, hy, hyN, hyM⟩ : ∃ y ∈ G, rightConjugate T y ≤
      S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) ∧
      ¬ rightConjugate T y ≤ T ⊔ rightConjugate T g := by
    by_contra hcon
    push Not at hcon
    apply hWM
    refine le_antisymm (relativeWeakClosure_le_of_normalizer h.toFrame hS2 hSGT
      (hMle.trans inf_le_right) hMeq fun c hc hle => hcon c hc hle) ?_
    exact sup_le (subgroup_le_relative_weak_closure _ _ _ hTS)
      (rightConjugate_le_relativeWeakClosure hg (hgSH.trans inf_le_left))
  by_contra hcon
  exact (ElemCtx.false_of_inputs ⟨⟨h45, hHS, hm, hy, hyN, hyM⟩, hsize, hO, IH,
    fun h' => hcon (Or.inl h')⟩ hin)

theorem theorem_4_8_of_inputs (h46 : Lemma46Statement) (hin : Theorem48Inputs) :
    Theorem48Statement :=
  theorem48_of_step fun X _ _ G T S Q H IH h h43 hsize hO hm =>
    theorem48_step h46 hin X G T S Q H IH h h43 hsize hO hm

theorem theorem_4_8_of_F2 (hG : CFSG.Goldschmidt.TopStatement)
    (hF2 : ∀ (K : Type) [Group K] [Finite K] (Z₀ : Subgroup K) [Z₀.Normal],
      CFSG.Open.IsQuasisimple K → Z₀ ≤ Subgroup.center K → IsPGroup 2 Z₀ →
      ∀ P : Sylow 2 (K ⧸ Z₀), IsMulCommutative (P : Subgroup (K ⧸ Z₀)) →
        Nat.card Z₀ ≤ 2 ∧ (8 ≤ Nat.card P → Z₀ = ⊥))
    (h46 : Lemma46Statement) : Theorem48Statement :=
  theorem_4_8_of_inputs h46
    { goldschmidt_theorem_four := GoldschmidtFour.goldschmidt_theorem_four_holds
      walter_schur_two_part := hF2
      goldschmidt := hG }

end CFSG.ComponentClassification.AschbacherTheorem3
