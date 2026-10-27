module

public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.SolvablePerfectTrivial
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem commutator_normal_of_sup_eq_top {H K : Subgroup X} (h : H ⊔ K = ⊤) :
    (⁅H, K⁆ : Subgroup X).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h, sup_le_iff]
  exact ⟨Subgroup.normalizer_commutator_ge_left H K, Subgroup.normalizer_commutator_ge_right H K⟩

theorem sup_eq_top_iff_mul_eq_univ (H K : Subgroup X) [H.Normal] :
    H ⊔ K = ⊤ ↔ (H : Set X) * (K : Set X) = Set.univ := by
  rw [← Subgroup.normal_mul H K, ← Subgroup.coe_top, SetLike.coe_set_eq]

theorem commutatorElement_mul_mul_of_forall_commute {A B : Subgroup X}
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {a₁ a₂ b₁ b₂ : X}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) :
    ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  have c₁ : Commute a₂ b₁ := hc _ ha₂ _ hb₁
  have c₂ : Commute a₁⁻¹ (b₁ * b₂ * b₁⁻¹) :=
    hc _ (A.inv_mem ha₁) _ (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁))
  have c₃ : Commute a₂⁻¹ (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) :=
    hc _ (A.inv_mem ha₂) _
      (B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂))
  simp only [commutatorElement_def]
  calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
      = a₁ * (b₁ * a₂) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * a₂ * ((b₁ * b₂ * b₁⁻¹) * a₁⁻¹) * b₂⁻¹ * a₂⁻¹ := by rw [← c₁.eq]; group
    _ = a₁ * a₂ * a₁⁻¹ * ((b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * a₂⁻¹) := by rw [← c₂.eq]; group
    _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by rw [← c₃.eq]; group

theorem commutator_le_sup_commutator_commutator {A B : Subgroup X} [A.Normal]
    (hsup : A ⊔ B = ⊤) (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) :
    _root_.commutator X ≤ ⁅A, A⁆ ⊔ ⁅B, B⁆ := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.1 (hsup ▸ Subgroup.mem_top x)
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.1 (hsup ▸ Subgroup.mem_top y)
  rw [commutatorElement_mul_mul_of_forall_commute hc ha₁ ha₂ hb₁ hb₂]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha₁ ha₂))
    (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hb₁ hb₂))

theorem le_commutator_self_of_le_commutator {A B : Subgroup X} [A.Normal]
    (hsup : A ⊔ B = ⊤) (hinf : A ⊓ B = ⊥) (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hA : A ≤ _root_.commutator X) : A ≤ ⁅A, A⁆ := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.1 (commutator_le_sup_commutator_commutator hsup hc (hA hx))
  have hbA : b ∈ A := by
    have : a⁻¹ * (a * b) ∈ A := A.mul_mem (A.inv_mem (Subgroup.commutator_le_self A ha)) hx
    simpa using this
  have hb1 : b = 1 := by
    have hbi : b ∈ A ⊓ B := ⟨hbA, Subgroup.commutator_le_self B hb⟩
    rw [hinf] at hbi
    simpa using hbi
  simpa [hb1] using ha

theorem eq_bot_of_isSolvable_of_le_commutator_self (A : Subgroup X) [Group.IsSolvable A]
    (h : A ≤ ⁅A, A⁆) : A = ⊥ := by
  have hcomm : _root_.commutator A = ⊤ := by
    refine Subgroup.map_injective A.subtype_injective ?_
    rw [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact le_antisymm (Subgroup.commutator_le_self A) h
  have := subsingleton_of_isSolvable_of_commutator_eq_top A hcomm
  exact Subgroup.eq_bot_of_subsingleton A

theorem eq_commutator_of_isSolvable_of_le_commutator
    (H K : Subgroup X) [H.Normal] [Group.IsSolvable H]
    (hsup : H ⊔ K = ⊤) (hinf : H ⊓ K = ⊥) (hH : H ≤ _root_.commutator X) :
    H = ⁅H, K⁆ := by
  set R : Subgroup X := ⁅H, K⁆ with hR
  have hRnormal : R.Normal := commutator_normal_of_sup_eq_top hsup
  have hRH : R ≤ H := Subgroup.commutator_le_left H K
  set f : X →* X ⧸ R := QuotientGroup.mk' R with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective R
  set A := H.map f with hA
  set B := K.map f with hB
  have hAnormal : A.Normal := ‹H.Normal›.map f hfsurj
  have hsup' : A ⊔ B = ⊤ := by
    rw [hA, hB, ← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective f hfsurj]
  have hinf' : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨h, hh, rfl⟩, ⟨k, hk, hxk⟩⟩
    have hqk : h⁻¹ * k ∈ R := by rw [← QuotientGroup.eq]; exact hxk.symm
    have hkH : k ∈ H := by
      have := H.mul_mem hh (hRH hqk)
      simpa using this
    have hk1 : k ∈ H ⊓ K := ⟨hkH, hk⟩
    rw [hinf] at hk1
    rw [← hxk, Subgroup.mem_bot.1 hk1]
    simp
  have hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    rintro a ⟨h, hh, rfl⟩ b ⟨k, hk, rfl⟩
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hf,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.commutator_mem_commutator hh hk
  have hAle : A ≤ _root_.commutator (X ⧸ R) := by
    calc A ≤ (_root_.commutator X).map f := Subgroup.map_mono hH
      _ = _root_.commutator (X ⧸ R) := by
          rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective f hfsurj,
            ← _root_.commutator_def]
  have : Group.IsSolvable A := isSolvable_map f H
  have hAbot : A = ⊥ :=
    eq_bot_of_isSolvable_of_le_commutator_self A
      (le_commutator_self_of_le_commutator hsup' hinf' hc hAle)
  refine le_antisymm ?_ hRH
  rw [hA, Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk'] at hAbot
  exact hAbot

theorem eq_commutator_of_isSolvable_of_le_commutator'
    (H K : Subgroup X) [H.Normal] [Group.IsSolvable H]
    (hmul : (H : Set X) * (K : Set X) = Set.univ) (hinf : H ⊓ K = ⊥)
    (hH : H ≤ _root_.commutator X) : H = ⁅H, K⁆ :=
  eq_commutator_of_isSolvable_of_le_commutator H K
    ((sup_eq_top_iff_mul_eq_univ H K).2 hmul) hinf hH

theorem eq_closure_setOf_inv_mul_inv_mul_mul_of_isSolvable_of_le_commutator
    (H K : Subgroup X) [H.Normal] [Group.IsSolvable H]
    (hsup : H ⊔ K = ⊤) (hinf : H ⊓ K = ⊥) (hH : H ≤ _root_.commutator X) :
    H = Subgroup.closure {x : X | ∃ u ∈ H, ∃ v ∈ K, u⁻¹ * v⁻¹ * u * v = x} := by
  rw [closure_setOf_inv_mul_inv_mul_mul]
  exact eq_commutator_of_isSolvable_of_le_commutator H K hsup hinf hH

end CFSG.FeitThompson
