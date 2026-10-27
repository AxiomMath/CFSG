module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndexElementary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem relativeWeakClosure_bot (G S : Subgroup X) :
    relativeWeakClosure G ⊥ S = ⊥ := by
  apply le_antisymm _ bot_le
  refine iSup_le fun c => iSup_le fun _ => ?_
  rw [conjugateSubgroup, Subgroup.map_bot]

omit [Finite X] in
theorem card_centralizer_subtype {S : Subgroup X} {t : X} (ht : t ∈ S) :
    Nat.card (Subgroup.centralizer ({⟨t, ht⟩} : Set S)) =
      Nat.card (S ⊓ Subgroup.centralizer {t} : Subgroup X) := by
  have hmap : (Subgroup.centralizer ({⟨t, ht⟩} : Set S)).map S.subtype =
      S ⊓ Subgroup.centralizer {t} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y * ⟨t, ht⟩ = ⟨t, ht⟩ * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      exact Subgroup.mem_inf.mpr
        ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy')⟩
    · rintro ⟨hxS, hxC⟩
      have hxC' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
      exact ⟨⟨x, hxS⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxC'), rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective S.subtype_injective]

theorem lemma_4_7 {G T S Q H : Subgroup X} (h : SylowFrame G T S) (h43 : Hyp43 G T Q H)
    (hsize : T.relIndex (S ⊓ H) ≤ Nat.card T) : Lemma47Conclusion G T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Lemma47Conclusion
  by_cases hW : relativeWeakClosure G T S = T
  · exact Or.inl hW
  right
  have hT : T ≠ ⊥ := by
    rintro rfl
    exact hW (relativeWeakClosure_bot G S)
  have hTS := h.le
  have hS2 := h.sylow.isPGroup
  have hSGT := h.sylow.le
  obtain ⟨g, hg, hgN, hne⟩ := exists_conj_le_normalizer h.toFrame hS2 hSGT hTS hW
  have hNH : S ⊓ Subgroup.normalizer (T : Set X) ≤ H :=
    (inf_le_inf_right _ hSGT).trans (h43.normalizer_le h.toFrame hT)
  have hgSH : rightConjugate T g ≤ S ⊓ H := le_inf (hgN.trans inf_le_left) (hgN.trans hNH)
  obtain ⟨-, hinf, hcomm, habel⟩ := lemma_4_4_two h.toFrame h43 hS2 hTS hg hgSH hne
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
  · exact Or.inr (Or.inl ⟨g, hg, hWM, hinf, hcomm, hWM ▸ habel⟩)
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
  by_cases hm : 1 < pRank 2 T
  · exact Or.inr (Or.inr (Elem47.conclusion ⟨h45, hHS, hm, hy, hyN, hyM⟩))
  left
  have hT2 := card_eq_two_of_pRank_le_one h45 hm hy hyN hyM
  refine ⟨isCyclic_of_prime_card hT2, ?_⟩
  obtain ⟨t₀, ht₀, ht₀2, -⟩ := exists_center_involution h.isPGroup hT
  have ht₀1 : t₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht₀2
    omega
  have hsqT : ∀ t ∈ T, t ^ 2 = 1 := by
    intro t ht
    have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    rw [hT2] at h1
    exact congrArg Subtype.val h1
  have hsqM : ∀ w ∈ T ⊔ rightConjugate T g, w ^ 2 = 1 := by
    have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _)
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
      rw [show b ^ 2 = g⁻¹ * (g * b * g⁻¹) ^ 2 * g by simp only [pow_two]; group, hsqT _ hb']
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
  rcases CFSG.ComponentClassification.AschbacherToolkit.suzuki_two_group (P := S) hS2 hcardC
      hexpC with hD | hSD
  · exact Or.inr (Or.inl hD)
  · exact Or.inr (Or.inr hSD)

theorem lemma_4_7_statement :
    ∀ (X : Type) [Group X] [Finite X] (G T S Q H : Subgroup X),
      SylowFrame G T S → Hyp43 G T Q H → T.relIndex (S ⊓ H) ≤ Nat.card T →
      Lemma47Conclusion G T S :=
  fun _ _ _ _ _ _ _ _ h h43 hsize => lemma_4_7 h h43 hsize

end CFSG.ComponentClassification.AschbacherTheorem3
