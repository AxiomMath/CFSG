module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageCore
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageFactors
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.Mathlib.GroupTheory.PermCenter
import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] {L U P D M : Subgroup G} {ℳ : Set (Subgroup G)}

theorem IsGomiLeviPackage.existsUnique_factor (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) (hDB : D ≤ L ⊓ normalizer (U : Set G)) {A : Subgroup G}
    (hA : IsGomiAtom L U A) (hAP : A ≤ P) :
    ∃ K ∈ (fun M => D ⊔ M) '' ℳ, ¬ A ⊓ K ≤ L ⊓ normalizer (U : Set G) ∧
      ∀ K' ∈ (fun M => D ⊔ M) '' ℳ, ¬ A ⊓ K' ≤ L ⊓ normalizer (U : Set G) → K' = K := by
  set B : Subgroup G := L ⊓ normalizer (U : Set G) with hB
  have hBA : B ≤ A := hA.1.le
  have hDB' : D ≤ B := hDB
  have hBmin : ∀ Q : Subgroup G, B < Q → Q ≤ A → Q = A := hA.2.2
  obtain ⟨M, hM, hA_le, huniq⟩ := h.atom A hA hAP
  refine ⟨D ⊔ M, ⟨M, hM, rfl⟩, ?_, ?_⟩
  · rintro hle
    have hAB : A ≤ B := by
      intro a ha
      have hBN : B ≤ normalizer (D ⊔ M : Subgroup G) :=
        (hBA.trans hAP).trans (h.le_normalizer_sup hD hM)
      have hA_le' : A ≤ B ⊔ (D ⊔ M) := hA_le.trans (sup_le_sup le_rfl le_sup_right)
      have hset := coe_mul_of_left_le_normalizer_right B (D ⊔ M) hBN
      have ha' : a ∈ (↑(B ⊔ (D ⊔ M)) : Set G) := hA_le' ha
      rw [hset] at ha'
      obtain ⟨b, hb, k, hk, hbk⟩ := ha'
      have hkA : k ∈ A := by
        have : k = b⁻¹ * a := by rw [← hbk]; group
        rw [this]; exact mul_mem (inv_mem (hBA hb)) ha
      have hkB : k ∈ B := hle (Subgroup.mem_inf.mpr ⟨hkA, hk⟩)
      rw [hbk.symm]; exact mul_mem hb hkB
    exact (ne_of_lt hA.1) (le_antisymm hBA hAB)
  · rintro K' ⟨M', hM', rfl⟩ hK'
    have hA_le' : A ≤ B ⊔ M' := by
      have hlt : B < B ⊔ (A ⊓ (D ⊔ M')) :=
        lt_of_le_of_ne le_sup_left fun hEq => hK' (hEq.symm ▸ le_sup_right)
      have hQ_le : B ⊔ (A ⊓ (D ⊔ M')) ≤ A := sup_le hBA inf_le_left
      have hQ_eq : B ⊔ (A ⊓ (D ⊔ M')) = A := hBmin _ hlt hQ_le
      calc A = B ⊔ (A ⊓ (D ⊔ M')) := hQ_eq.symm
        _ ≤ B ⊔ (D ⊔ M') := sup_le_sup le_rfl inf_le_right
        _ = B ⊔ M' := by rw [← sup_assoc, sup_eq_left.mpr hDB']
    rw [huniq M' hM' hA_le']

theorem IsGomiLeviPackage.nonempty_mulEquiv_quotient (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) (hM : M ∈ ℳ) [(D.subgroupOf (D ⊔ M)).Normal] :
    Nonempty ((↥(D ⊔ M) ⧸ D.subgroupOf (D ⊔ M)) ≃* (↥M ⧸ center ↥M)) := by
  have hMD : M ≤ normalizer (D : Set G) := (h.le_parabolic M hM).trans hD.le_normalizer
  have hDM : D.subgroupOf M = center ↥M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, h.inf_eq_center hD hM]
  let eSup : ↥(D ⊔ M) ≃* ↥(M ⊔ D) := MulEquiv.subgroupCongr (sup_comm D M)
  have he : (D.subgroupOf (D ⊔ M)).map eSup = D.subgroupOf (M ⊔ D) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hval : (eSup y : G) = (y : G) :=
        MulEquiv.subgroupCongr_apply (sup_comm D M) y
      rw [← hyx]
      exact Subgroup.mem_subgroupOf.mpr (hval.symm ▸ Subgroup.mem_subgroupOf.mp hy)
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨(x : G), ?_⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), ?_⟩
      · rw [sup_comm]; exact x.2
      · exact Subtype.ext (MulEquiv.subgroupCongr_apply (sup_comm D M) _)
  let e := by
    letI : (D.subgroupOf (M ⊔ D)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hMD le_normalizer)
    letI : (D.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hMD
    exact (QuotientGroup.congr (D.subgroupOf (D ⊔ M)) (D.subgroupOf (M ⊔ D)) eSup he).trans
      ((QuotientGroup.quotientInfEquivProdNormalizerQuotient M D hMD).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hDM))
  exact ⟨e⟩

theorem IsGomiLeviPackage.factor_sup [Finite G] (h : IsGomiLeviPackage L U P ℳ)
    (hD : IsGomiLeviCore P D) (hDB : D ≤ L ⊓ normalizer (U : Set G)) (hM : M ∈ ℳ)
    [(D.subgroupOf (D ⊔ M)).Normal] :
    IsGomiChevTwo (↥(D ⊔ M) ⧸ D.subgroupOf (D ⊔ M)) ∨
      Nonempty ((↥(D ⊔ M) ⧸ D.subgroupOf (D ⊔ M)) ≃* Equiv.Perm (Fin 6)) ∨
      ∀ Q : Subgroup G, L ⊓ normalizer (U : Set G) ⊓ (D ⊔ M) < Q → Q ≤ D ⊔ M → Q = D ⊔ M := by
  set B : Subgroup G := L ⊓ normalizer (U : Set G) with hB
  obtain ⟨e⟩ := h.nonempty_mulEquiv_quotient hD hM
  rcases h.factor M hM with hChev | hPerm | hCov
  · exact Or.inl (IsGomiChevTwo.of_mulEquiv e.symm (IsGomiChevTwo.quotient_center hChev))
  · obtain ⟨f⟩ := hPerm
    have hcenter : center (Equiv.Perm (Fin 6)) = ⊥ := center_perm_eq_bot_of_three_le_card (by simp)
    have g : ↥M ⧸ center ↥M ≃* Equiv.Perm (Fin 6) :=
      (QuotientGroup.congr (center ↥M) (center (Equiv.Perm (Fin 6))) f
        (Subgroup.map_center_eq f)).trans
        ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)
    exact Or.inr (Or.inl ⟨e.trans g⟩)
  · right; right
    have hDB' : D ≤ B := hDB
    have hCov' : B ⊓ M ⋖ M := hCov
    intro Q hQ hQle
    have hDQ : D ≤ Q := le_trans (le_inf hDB' le_sup_left) hQ.le
    have hBMle : B ⊓ M ≤ Q ⊓ M :=
      le_inf (le_trans (inf_le_inf_left B le_sup_right) hQ.le) inf_le_right
    have hMD : M ≤ normalizer (D : Set G) := (h.le_parabolic M hM).trans hD.le_normalizer
    have hQ1 : (Q ⊓ M) ⊔ D = Q := by
      rw [Subgroup.inf_sup_assoc_of_le hMD hDQ, sup_comm M D, inf_eq_left.mpr hQle]
    have hB1 : (B ⊓ M) ⊔ D = B ⊓ (D ⊔ M) := by
      rw [Subgroup.inf_sup_assoc_of_le hMD hDB', sup_comm M D]
    have hne : Q ⊓ M ≠ B ⊓ M := by
      intro heq
      have hQeq : Q = B ⊓ (D ⊔ M) := by rw [← hQ1, heq, hB1]
      exact ne_of_lt hQ hQeq.symm
    have hQinfM : Q ⊓ M = M := by
      rcases hCov'.eq_or_eq hBMle inf_le_right with h' | h'
      · exact absurd h' hne
      · exact h'
    exact le_antisymm hQle (sup_le hDQ (hQinfM ▸ inf_le_left))

end CFSG.GroupTheory
