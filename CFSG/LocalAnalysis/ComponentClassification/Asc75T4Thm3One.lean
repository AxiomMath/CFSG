module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Assembly

public section

namespace CFSG.ComponentClassification.Asc75T4

open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise MatrixGroups commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def Thm3RankOne (Q T S : Subgroup X) : Prop :=
  IsCyclic T ∧
    (IsCyclic (S ⊓ Q : Subgroup X) ∨ IsQuaternionTwoGroup (S ⊓ Q) ∨
      IsDihedralTwoGroup (S ⊓ Q)) ∧
    ((Nat.card T = 2 ∧ (IsDihedralTwoGroup S ∨ IsSemidihedralTwoGroup S)) ∨
      (2 < Nat.card T ∧ IsWreathedTwoGroup S))

theorem theorem_3_rankOne {Q T P S : Subgroup X} (h : Hyp3 Q T P S) (hm1 : pRank 2 T ≤ 1) :
    Thm3RankOne Q T S ∨ Q ⊔ T ≤ Subgroup.normalizer (T : Set X) := by
  have hm : ¬ 1 < pRank 2 T := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := (Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X) with hHdef
  have h43 := h.hyp43
  have hsf := h.sylowFrame
  have hF := hsf.toFrame
  have hT := h.ne_bot
  have hO := h.oddCore_eq_bot
  have hTS := hsf.le
  have hS2 := hsf.sylow.isPGroup
  have hSGT := hsf.sylow.le
  have hsize : T.relIndex (S ⊓ H) ≤ Nat.card T := by
    rw [h.inf_H]
    exact h.index_le
  by_cases hW : relativeWeakClosure Q T S = T
  ·
    right
    have hwc : ∀ g ∈ Q, rightConjugate T g ≤ S → rightConjugate T g = T := by
      intro g hg hle
      have h1 := rightConjugate_le_relativeWeakClosure hg hle
      rw [hW] at h1
      exact Subgroup.eq_of_le_of_card_ge h1 (rightConjugate_card T g).ge
    refine sup_le ?_ Subgroup.le_normalizer
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (lemma_4_2 hsf hwc hO)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨g, hg, hgN, hne⟩ := exists_conj_le_normalizer hF hS2 hSGT hTS hW
  have hNH : S ⊓ Subgroup.normalizer (T : Set X) ≤ H :=
    (inf_le_inf_right _ hSGT).trans (h43.normalizer_le hF hT)
  have hgSH : rightConjugate T g ≤ S ⊓ H := le_inf (hgN.trans inf_le_left) (hgN.trans hNH)
  obtain ⟨-, hinf, hcomm, habel⟩ := lemma_4_4_two hF h43 hS2 hTS hg hgSH hne
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
  have h45 : Hyp45 Q T S P H g :=
    { sylowFrame := hsf
      hyp43 := h43
      mem := hg
      ne := hne
      weakClosure := le_antisymm (by rw [← hHS]; exact relative_weak_closure_le _ _ _)
        (sup_le (subgroup_le_relative_weak_closure _ _ _ (hHS ▸ le_sup_left))
          (rightConjugate_le_relativeWeakClosure hg (hHS ▸ le_sup_right))) }
  have hTab : IsMulCommutative T := isMulCommutative_of_le le_sup_left habel
  left
  have hcyc : IsCyclic T := isCyclic_of_pRank_le_one hsf.isPGroup hTab hm
  by_cases hT2 : Nat.card T = 2
  ·
    obtain ⟨t₀, ht₀, ht₀2, -⟩ := exists_center_involution hsf.isPGroup hT
    have ht₀1 : t₀ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht₀2
      omega
    have hsqT : ∀ t ∈ T, t ^ 2 = 1 := by
      intro t ht
      have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
      rw [hT2] at h1
      exact congrArg Subtype.val h1
    have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _)
    have hsqM : ∀ w ∈ T ⊔ rightConjugate T g, w ^ 2 = 1 := by
      intro w hw
      have hwmem : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
        exact hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hwmem
      have hab : a * b = b * a :=
        (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
      have hb2 : b ^ 2 = 1 := by
        have hb' : g * b * g⁻¹ ∈ T := (mem_rightConjugate_iff T g b).mp hb
        rw [show b ^ 2 = g⁻¹ * (g * b * g⁻¹) ^ 2 * g by simp only [pow_two]; group,
          hsqT _ hb']
        group
      calc (a * b) ^ 2 = a * (b * a) * b := by simp only [pow_two, mul_assoc]
        _ = a * (a * b) * b := by rw [hab]
        _ = a ^ 2 * b ^ 2 := by simp only [pow_two, mul_assoc]
        _ = 1 := by rw [hsqT a ha, hb2, one_mul]
    have hC := lemma_4_5_one h45 ht₀ ht₀1
    have hcardC : Nat.card (Subgroup.centralizer ({⟨t₀, hTS ht₀⟩} : Set S)) = 4 := by
      rw [card_centralizer_subtype, ← hC, hHS, hcardM, hT2]
    have hexpC : ∀ x ∈ Subgroup.centralizer ({⟨t₀, hTS ht₀⟩} : Set S), x ^ 2 = 1 := by
      intro x hx
      have hxC : (x : X) ∈ S ⊓ Subgroup.centralizer {t₀} := by
        refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        exact congrArg Subtype.val hx
      rw [← hC, hHS] at hxC
      exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsqM _ hxC)
    have hSQ : IsCyclic (S ⊓ Q : Subgroup X) ∨ IsQuaternionTwoGroup (S ⊓ Q) ∨
        IsDihedralTwoGroup (S ⊓ Q) := by
      apply shape_of_index_two hS2 inf_le_left _ (hTS ht₀) _ ht₀2
      · have heq : (S ⊓ Q) ⊓ Subgroup.centralizer {t₀} = (T ⊔ rightConjugate T g) ⊓ Q := by
          rw [← hHS, hC, inf_right_comm]
        rw [heq, h45.card_W_inf_G, hT2]
      · have h1 := hF.card_eq_mul hSGT hTS
        have h2 := Subgroup.relIndex_mul_card (S ⊓ Q) S
        rw [inf_eq_left.mpr inf_le_left, h1, hT2] at h2
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
      · intro hmem
        have hmem' : t₀ ∈ T ⊓ Q := ⟨ht₀, hmem.2⟩
        rw [hF.inf_eq_bot, Subgroup.mem_bot] at hmem'
        exact ht₀1 hmem'
    refine ⟨hcyc, hSQ, Or.inl ⟨hT2, ?_⟩⟩
    rcases AschbacherToolkit.suzuki_two_group (P := S) hS2 hcardC hexpC with hD | hSD
    · exact Or.inl hD
    · exact Or.inr hSD
  ·
    have hWM : relativeWeakClosure Q T S = T ⊔ rightConjugate T g := by
      by_contra hWM
      obtain ⟨y, hy, hyN, hyM⟩ := h45.exists_conj_not_le hHS hWM
      exact hT2 (card_eq_two_of_pRank_le_one h45 hm hy hyN hyM)
    have hT4 : 2 < Nat.card T := by
      have h1 : Nat.card T ≠ 1 := fun h1 => hT (Subgroup.card_eq_one.mp h1)
      have h0 : 0 < Nat.card T := Nat.card_pos
      omega
    obtain ⟨hwr, hshape⟩ := h45.wreathed_case hHS hWM hcyc hT4 hO
    exact ⟨hcyc, hshape, Or.inr ⟨hT4, hwr⟩⟩

end CFSG.ComponentClassification.Asc75T4
