module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerStructure

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

theorem mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {z : G} :
    z ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, x * y = z := by
  constructor
  · intro hz
    rw [Subgroup.sup_eq_closure] at hz
    induction hz using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, mul_one y⟩
      · exact ⟨1, H.one_mem, y, hy, one_mul y⟩
    | one => exact ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
    | mul a b _ _ ha hb =>
      obtain ⟨x1, hx1, y1, hy1, rfl⟩ := ha
      obtain ⟨x2, hx2, y2, hy2, rfl⟩ := hb
      refine ⟨x1 * x2, H.mul_mem hx1 hx2, y1 * y2, K.mul_mem hy1 hy2, ?_⟩
      have := h x2 hx2 y1 hy1
      calc x1 * x2 * (y1 * y2) = x1 * (x2 * y1) * y2 := by group
        _ = x1 * (y1 * x2) * y2 := by rw [this]
        _ = x1 * y1 * (x2 * y2) := by group
    | inv a _ ha =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ha
      refine ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, ?_⟩
      have := h x hx y hy
      calc x⁻¹ * y⁻¹ = (y * x)⁻¹ := by group
        _ = (x * y)⁻¹ := by rw [← this]
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

theorem card_eq_mul_card_inf_of_le {G : Type*} [Group G] [Finite G] {D I F : Subgroup G}
    (hcomm : ∀ x ∈ D, ∀ y ∈ I, x * y = y * x) (hDI : Disjoint D I) (hDF : D ≤ F)
    (hFDI : F ≤ D ⊔ I) :
    F = D ⊔ (F ⊓ I) ∧ Nat.card F = Nat.card D * Nat.card ↥(F ⊓ I) := by
  have hFeq : F = D ⊔ (F ⊓ I) := by
    apply le_antisymm
    · intro f hf
      obtain ⟨d, hd, i, hi, rfl⟩ := (mem_sup_of_commute hcomm).1 (hFDI hf)
      have hiF : i ∈ F := by
        have := F.mul_mem (F.inv_mem (hDF hd)) hf
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right ⟨hiF, hi⟩)
    · exact sup_le hDF inf_le_left
  refine ⟨hFeq, ?_⟩
  have hdis : Disjoint D (F ⊓ I) := hDI.mono_right inf_le_right
  have hle := card_mul_le_card_sup_of_disjoint D (F ⊓ I) hdis
  have hge : Nat.card ↥(D ⊔ (F ⊓ I)) ≤ Nat.card D * Nat.card ↥(F ⊓ I) := by
    classical
    let f : D × ↥(F ⊓ I) → ↥(D ⊔ (F ⊓ I)) := fun p =>
      ⟨(p.1 : G) * (p.2 : G),
        Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨d, hd, i, hi, rfl⟩ := (mem_sup_of_commute (H := D) (K := F ⊓ I)
        (fun x hx y (hy : y ∈ F ⊓ I) => hcomm x hx y hy.2)).1 hx
      exact ⟨(⟨d, hd⟩, ⟨i, hi⟩), rfl⟩
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod] at this
  have : Nat.card F = Nat.card ↥(D ⊔ (F ⊓ I)) := by rw [← hFeq]
  omega

section Main


set_option linter.unusedSectionVars false
set_option maxRecDepth 20000 in
theorem frame_inf_perfect_core {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3) {a : X} (ha : a ∉ center X)
    (ha3 : a ^ 3 ∈ center X)
    (h5 : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3)))
    {F : Subgroup X} (hDF : zpowers a ⊔ center X ≤ F) (hFC : F ≤ centralizer ({a} : Set X)) :
    ∃ I : Subgroup X, I ≤ centralizer ({a} : Set X) ∧ ⁅I, I⁆ = I ∧
      Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧
      (∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ I) ∧
      F = (zpowers a ⊔ center X) ⊔ (F ⊓ I) ∧ Disjoint (zpowers a ⊔ center X) I ∧
      Nat.card F = 9 * Nat.card ↥(F ⊓ I) := by
  obtain ⟨I, hIC, hIperf, heI, hImax, -, hD9, hDI, hDcomm, hCeq⟩ :=
    centralizer_structure_J3Cover hX hZ3 e ha ha3 h5
  have hFDI : F ≤ (zpowers a ⊔ center X) ⊔ I := hCeq ▸ hFC
  have hcomm : ∀ x ∈ zpowers a ⊔ center X, ∀ y ∈ I, x * y = y * x :=
    fun x hx y hy => hDcomm x hx y (hIC hy)
  obtain ⟨hFeq, hcard⟩ := card_eq_mul_card_inf_of_le hcomm hDI hDF hFDI
  exact ⟨I, hIC, hIperf, heI, hImax, hFeq, hDI, by rw [hcard, hD9]⟩

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
