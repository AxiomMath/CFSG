module

public import CFSG.Walter.W67.Section6.Util

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CentCore

open Subgroup CFSG.Walter.W67.Sec6
open scoped commutatorElement

variable {G : Type*} [Group G]

omit [Group G] in
theorem card_sup_mul_card_inf_of_normal {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem exists_conj_mem_normalizes [Finite G] {X F : Subgroup G}
    (hF : F ≤ normalizer (X : Set G)) (hcop : Nat.Coprime (Nat.card F) (Nat.card X)) {j : G}
    (hj : ∀ f ∈ F, ⁅j, f⁆ ∈ X) : ∃ c ∈ X, ∀ f ∈ F, c⁻¹ * (j * f * j⁻¹) * c ∈ F := by
  have hcop' : Nat.Coprime (Nat.card X) (Nat.card F) := hcop.symm
  set M : Subgroup G := X ⊔ F with hM
  have hXM : X ≤ M := le_sup_left
  have hFM : F ≤ M := le_sup_right
  have hMN : M ≤ normalizer (X : Set G) := sup_le Subgroup.le_normalizer hF
  have hXF : X ⊓ F = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop').eq_bot
  have hcardM : Nat.card M = Nat.card X * Nat.card F := by
    have h := card_sup_mul_card_inf_of_le_normalizer hF
    rw [hXF, Subgroup.card_bot, mul_one] at h
    exact h
  have hrel : X.relIndex M = Nat.card F := by
    have h := Subgroup.relIndex_mul_card X M
    rw [inf_of_le_left hXM, hcardM] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (mul_comm _ _))
  have hFj : cj j F ≤ M := by
    intro x hx
    rw [mem_cj] at hx
    have hx' : x = ⁅j, j⁻¹ * x * j⁆ * (j⁻¹ * x * j) := by
      simp only [commutatorElement_def]
      group
    rw [hx']
    exact M.mul_mem (hXM (hj _ hx)) (hFM hx)
  have hXFj : X ⊓ cj j F = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [card_cj]
    exact hcop'
  have hsup : X ⊔ cj j F = M := by
    refine le_antisymm (sup_le hXM hFj) (sup_le le_sup_left ?_)
    intro f hf
    have hjf : j * f * j⁻¹ ∈ cj j F := conj_mem_cj hf
    have hX : ⁅f, j⁆ ∈ X := by
      rw [← commutatorElement_inv]
      exact X.inv_mem (hj f hf)
    have hf' : f = ⁅f, j⁆ * (j * f * j⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hf']
    exact (X ⊔ cj j F).mul_mem (Subgroup.mem_sup_left hX) (Subgroup.mem_sup_right hjf)
  obtain ⟨c, hcX, hceq⟩ := exists_conj_complement_in hXM hMN (by rw [hrel]; exact hcop') hFM hFj hXF rfl
    hXFj hsup
  refine ⟨c, hcX, fun f hf => ?_⟩
  have hjf : j * f * j⁻¹ ∈ cj j F := conj_mem_cj hf
  rw [hceq, mem_cj] at hjf
  exact hjf

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CentCore
