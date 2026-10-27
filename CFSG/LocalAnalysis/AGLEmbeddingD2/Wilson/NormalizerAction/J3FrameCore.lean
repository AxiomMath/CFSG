module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3ClassFrame
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3A6Classes

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint CFSG.SectionRank.Native
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.RankThree.Asc83Table
open scoped commutatorElement

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem frame_core_eq_F1 {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3) {F : Subgroup X}
    (hF : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (center X))))
    (hZF : center X ≤ F) (hF81 : Nat.card F = 81)
    (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    ∃ F₁ : Subgroup X, center X ≤ F₁ ∧ F₁ ≤ F ∧ Nat.card F₁ = 27 ∧
      (∀ y ∈ normalizer (F : Set X), ∀ s ∈ F₁, y * s * y⁻¹ ∈ F₁) ∧
      (∀ a ∈ F, a ∉ center X →
        5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3)) → a ∉ F₁) ∧
      ∀ a ∈ F, a ∉ F₁ → ∃ I : Subgroup X, I ≤ centralizer ({a} : Set X) ∧ ⁅I, I⁆ = I ∧
        Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧
        (∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ I) ∧
        (F ⊓ I) ⊔ center X = F₁ := by
  obtain ⟨F₁, hZF₁, hF₁F, hF₁27, hF₁inv, hnot, h3A, -⟩ := exists_F1_of_class hZ3 e hF hZF hF81
  refine ⟨F₁, hZF₁, hF₁F, hF₁27, hF₁inv, hnot, fun a haF haF₁ => ?_⟩
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπ
  have hker : π.ker = center X := QuotientGroup.ker_mk' _
  have hπker : ∀ w : X, π w = 1 ↔ w ∈ center X := fun w => QuotientGroup.eq_one_iff w
  have hEA := isElementaryAbelian_iff.1 hF
  have hF3 : ∀ w ∈ F, w ^ 3 ∈ center X := fun w hw => by
    rw [← hπker, map_pow]; exact hEA.2 _ ⟨w, hw, rfl⟩
  have ha : a ∉ center X := fun h => haF₁ (hZF₁ h)
  have h5 := h3A a haF haF₁
  have ha3 := hF3 a haF
  obtain ⟨I, hIC, hIperf, heI, hImax, hFeq, hDI, hFcard⟩ :=
    frame_inf_perfect_core hX hZ3 e ha ha3 h5 (F := F)
      (sup_le (by rw [zpowers_le]; exact haF) hZF)
      (fun y hy => mem_centralizer_singleton_iff.2 (hFab a haF y hy).symm)
  refine ⟨I, hIC, hIperf, heI, hImax, ?_⟩
  have hx3 : (a : X ⧸ center X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 ha3
  have hx1 : (a : X ⧸ center X) ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff a).1 h)
  have hcQ : Nat.card (centralizer ({(a : X ⧸ center X)} : Set (X ⧸ center X))) = 1080 :=
    card_centralizer_of_equiv_J3 e hx3 hx1 h5
  have hle : F ⊓ I ≤ F₁ := by
    intro b hb
    by_contra hbF₁
    have hbF := hb.1
    have hbI := hb.2
    have hb5 := h3A b hbF hbF₁
    have hbz : b ∉ center X := fun h => hbF₁ (hZF₁ h)
    have hb1 : (b : X ⧸ center X) ≠ 1 := fun h => hbz ((QuotientGroup.eq_one_iff b).1 h)
    have hb3 : (b : X ⧸ center X) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 (hF3 b hbF)
    have hIC' : I.map π ≤ centralizer ({(a : X ⧸ center X)} : Set (X ⧸ center X)) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 (hIC hw)
      show π w * π a = π a * π w
      rw [← map_mul, ← map_mul, this]
    have hperf' : ⁅I.map π, I.map π⁆ = I.map π := by
      rw [← Subgroup.map_commutator, hIperf]
    have := j3_a6_threeElements_class e hx3 hx1 hcQ (I.map π) hIC' hperf' (b : X ⧸ center X)
      ⟨b, hbI, rfl⟩ hb1 hb3
    rw [← card_cent_J3_eq e] at this
    have h5' : 5 ∣ Nat.card (centralizer ({e (b : X ⧸ center X)} : Set NativeSporadic.J3)) := hb5
    rw [this] at h5'
    omega
  apply le_antisymm
  · exact sup_le hle hZF₁
  ·
    have hdisj : Disjoint (F ⊓ I) (center X) := by
      exact (hDI.mono_left le_sup_right).symm.mono_left inf_le_right
    have hle2 : Nat.card (F ⊓ I : Subgroup X) * Nat.card (center X : Subgroup X) ≤
        Nat.card ↥((F ⊓ I) ⊔ center X) := card_mul_le_card_sup_of_disjoint _ _ hdisj
    have hcardI : Nat.card (F ⊓ I : Subgroup X) = 9 := by omega
    rw [hcardI, hZ3] at hle2
    exact eq_of_le_of_card_ge (sup_le hle hZF₁) (by rw [hF₁27]; omega) |>.ge
end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
