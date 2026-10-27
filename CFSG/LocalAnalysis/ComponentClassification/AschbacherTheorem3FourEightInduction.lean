module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightBenderCase
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport2

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups Pointwise

variable {X : Type} [Group X]

@[expose] def Conclusion48 (G T S : Subgroup X) : Prop :=
  G ≤ Subgroup.normalizer (relativeWeakClosure G T S : Set X) ∨
    (∃ n : ℕ, 2 ≤ n ∧
      oTwoPrime (G ⊔ T) = pCoreOf 2 (G ⊔ T) ⊔ ⁅T, G⁆ ∧
      pCoreOf 2 (G ⊔ T) ⊓ ⁅T, G⁆ = ⊥ ∧ ⁅pCoreOf 2 (G ⊔ T), ⁅T, G⁆⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (G ⊔ T)) ∧ Nat.card (pCoreOf 2 (G ⊔ T)) = 2 ^ n ∧
      Nonempty ((⁅T, G⁆ : Subgroup X) ≃* PSL(2, GaloisField 2 n)))

@[expose] def Theorem48Below (N : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (G T S Q H : Subgroup X),
    Nat.card (G ⊔ T : Subgroup X) < N → SylowFrame G T S → Hyp43 G T Q H →
    T.relIndex (S ⊓ H) ≤ Nat.card T → CFSG.oddCore G = ⊥ → 1 < pRank 2 T →
    Conclusion48 G T S

theorem Theorem48Below.mono {N N' : ℕ} (h : Theorem48Below N) (hle : N' ≤ N) :
    Theorem48Below N' :=
  fun X _ _ G T S Q H hlt => h X G T S Q H (lt_of_lt_of_le hlt hle)

theorem theorem48_of_step
    (hstep : ∀ (X : Type) [Group X] [Finite X] (G T S Q H : Subgroup X),
      Theorem48Below (Nat.card (G ⊔ T : Subgroup X)) → SylowFrame G T S → Hyp43 G T Q H →
      T.relIndex (S ⊓ H) ≤ Nat.card T → CFSG.oddCore G = ⊥ → 1 < pRank 2 T →
      Conclusion48 G T S) :
    Theorem48Statement := by
  have hall : ∀ N, Theorem48Below N := by
    intro N
    induction N with
    | zero => exact fun X _ _ G T S Q H hlt => absurd hlt (Nat.not_lt_zero _)
    | succ N ih =>
        intro X _ _ G T S Q H hlt
        exact hstep X G T S Q H (ih.mono (Nat.lt_succ_iff.mp hlt))
  intro X _ _ G T S Q H h h43 hidx hO hm
  exact hall _ X G T S Q H (Nat.lt_succ_self _) h h43 hidx hO hm

theorem oddCore_eq_bot_of_le_normalizer [Finite X] {G G₁ : Subgroup X}
    (hO : CFSG.oddCore G = ⊥) (hG₁ : G₁ ≤ G) (hN : G ≤ Subgroup.normalizer (G₁ : Set X)) :
    CFSG.oddCore G₁ = ⊥ := by
  have : (CFSG.oddCore G₁).Characteristic := OddCore.characteristic G₁
  have hOG : (CFSG.oddCore G₁).map G₁.subtype ≤ G := (Subgroup.map_subtype_le _).trans hG₁
  have hGO : G ≤ Subgroup.normalizer (((CFSG.oddCore G₁).map G₁.subtype : Subgroup X) : Set X) :=
    fun g hg => mem_normalizer_map_of_characteristic (CFSG.oddCore G₁) (hN hg)
  have hodd : Odd (Nat.card ((CFSG.oddCore G₁).map G₁.subtype)) := by
    rw [Subgroup.card_map_of_injective G₁.subtype_injective]
    exact odd_card_oddCore G₁
  have hle := le_map_oddCore hOG hGO hodd
  rw [hO, Subgroup.map_bot, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ G₁.subtype_injective).mp hle

theorem isMulCommutative_of_psl_case [Finite X] {G T S : Subgroup X} (hF : Frame G T)
    (hS : IsSylowOf 2 S (G ⊔ T))
    (h : ∃ n : ℕ, 2 ≤ n ∧
      oTwoPrime (G ⊔ T) = pCoreOf 2 (G ⊔ T) ⊔ ⁅T, G⁆ ∧
      pCoreOf 2 (G ⊔ T) ⊓ ⁅T, G⁆ = ⊥ ∧ ⁅pCoreOf 2 (G ⊔ T), ⁅T, G⁆⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (G ⊔ T)) ∧ Nat.card (pCoreOf 2 (G ⊔ T)) = 2 ^ n ∧
      Nonempty ((⁅T, G⁆ : Subgroup X) ≃* PSL(2, GaloisField 2 n))) :
    IsMulCommutative S := by
  obtain ⟨n, hn, h2, -, hcomm, hel, -, ⟨e⟩⟩ := h
  exact isMulCommutative_of_psl hF hn hS h2 hcomm hel e

theorem conclusion_of_normal [Finite X] {G T S Q H G₁ : Subgroup X}
    (IH : Theorem48Below (Nat.card (G ⊔ T : Subgroup X))) (h : SylowFrame G T S)
    (h43 : Hyp43 G T Q H) (hidx : T.relIndex (S ⊓ H) ≤ Nat.card T) (hO : CFSG.oddCore G = ⊥)
    (hm : 1 < pRank 2 T) (hG₁ : G₁ ≤ G) (hn : G ⊔ T ≤ Subgroup.normalizer (G₁ : Set X))
    (hne : G₁ ≠ G) :
    Conclusion48 G₁ T (S ⊓ (G₁ ⊔ T)) := by
  have hlt : Nat.card (G₁ ⊔ T : Subgroup X) < Nat.card (G ⊔ T : Subgroup X) :=
    card_sup_lt h.toFrame (lt_of_le_of_ne hG₁ hne) (le_sup_right.trans hn)
  refine IH X G₁ T (S ⊓ (G₁ ⊔ T)) (Q ⊓ (G₁ ⊔ T)) (H ⊓ (G₁ ⊔ T)) hlt (h.restrict hG₁ hn)
    (h43.restrict hG₁) ?_ (oddCore_eq_bot_of_le_normalizer hO hG₁ (le_sup_left.trans hn)) hm
  have hTle : T ≤ S ⊓ (G₁ ⊔ T) ⊓ (H ⊓ (G₁ ⊔ T)) :=
    le_inf (le_inf h.le le_sup_right) (le_inf h43.le_H le_sup_right)
  refine le_trans ?_ hidx
  apply Subgroup.relIndex_le_of_le_right _ (Elem47.relIndex_ne_zero_of_finite _ _)
  exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)

theorem le_pCoreOf_of_normal [Finite X] {G T K Y : Subgroup X} (hKGT : K ≤ G ⊔ T)
    (hKN : G ⊔ T ≤ Subgroup.normalizer (K : Set X)) (hYK : Y ≤ K)
    (hYN : K ≤ Subgroup.normalizer (Y : Set X)) (hY : IsPGroup 2 Y) :
    Y ≤ pCoreOf 2 (G ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Y ≤ pCoreOf 2 K := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYK hYN hY
  have h2 : pCoreOf 2 K ≤ pCoreOf 2 (G ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K).trans hKGT)
      (hKN.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact h1.trans h2

theorem le_normalizer_of_le_pCoreOf [Finite X] {G T S : Subgroup X} (h : SylowFrame G T S)
    (hT : T ≤ pCoreOf 2 (G ⊔ T)) :
    G ≤ Subgroup.normalizer (relativeWeakClosure G T S : Set X) := by
  have hF := h.toFrame
  have hO2S : pCoreOf 2 (G ⊔ T) ≤ S := pCoreOf_le_of_isSylowOf h.sylow
  have hO2N : G ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (G ⊔ T) : Set X) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (G ⊔ T)
  have hconj : ∀ x ∈ G, rightConjugate T x ≤ S := by
    intro x hx
    have h1 := rightConjugate_le_rightConjugate hT x
    rw [(rightConjugate_eq_self_iff _ x).mpr (hO2N (Subgroup.mem_sup_left hx))] at h1
    exact h1.trans hO2S
  have hW : relativeWeakClosure G T S = conjugateClosure G T := by
    apply le_antisymm
    · rw [relativeWeakClosure_le_iff]
      intro x hx _
      unfold conjugateClosure
      exact le_iSup (fun c : G => rightConjugate T c) ⟨x, hx⟩
    · unfold conjugateClosure
      exact iSup_le fun c => rightConjugate_le_relativeWeakClosure c.2 (hconj c c.2)
  rw [hW]
  exact le_sup_left.trans (sup_le_normalizer_conjugateClosure hF)

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
