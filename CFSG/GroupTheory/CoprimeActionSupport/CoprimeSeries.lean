module

public import Mathlib.GroupTheory.PGroup

import CFSG.GroupTheory.CommutatorCentralizerIn
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.GroupTheory.CoprimeActionSupport

variable {G : Type*} [Group G]

open Subgroup
open CFSG.GroupTheory (commutatorCentralizerIn mem_commutatorCentralizerIn)

private lemma exists_pow_eq_mul_pow {C : Subgroup G} {c y : G} (hc : c ∈ C)
    (hy : y ∈ normalizer (C : Set G)) (k : ℕ) : ∃ d ∈ C, (c * y) ^ k = d * y ^ k := by
  induction k with
  | zero => exact ⟨1, C.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, hdk⟩ := ih
    have hyk : y ^ k ∈ normalizer (C : Set G) := (normalizer (C : Set G)).pow_mem hy k
    have hconj : y ^ k * c * (y ^ k)⁻¹ ∈ C :=
      (Subgroup.le_normalizer_iff (H := normalizer (C : Set G)) (K := C)).mp le_rfl
        (y ^ k) hyk c hc
    refine ⟨d * (y ^ k * c * (y ^ k)⁻¹), C.mul_mem hd hconj, ?_⟩
    calc (c * y) ^ (k + 1) = (d * y ^ k) * (c * y) := by rw [pow_succ, hdk]
      _ = d * (y ^ k * c * (y ^ k)⁻¹) * (y ^ k * y) := by group
      _ = d * (y ^ k * c * (y ^ k)⁻¹) * y ^ (k + 1) := by rw [pow_succ]

theorem commutator_mem_of_coprime_of_le_sup [Finite G] {p : ℕ} [Fact p.Prime]
    {L A B P X₁ X₂ : Subgroup G} (hP : IsPGroup p P) (hPL : P ≤ L) (hX₁ : X₁ ≤ L)
    (hX₂ : X₂ ≤ L) (hLA : L ≤ normalizer (A : Set G)) (hLB : L ≤ normalizer (B : Set G))
    (h₁ : ∀ x ∈ X₁, ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ B)
    (h₂ : ∀ x ∈ X₂, ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ B) (hgen : L ≤ X₁ ⊔ X₂ ⊔ P) {l : G}
    (hl : l ∈ L) (hcop : (orderOf l).Coprime p) : ∀ a ∈ A, l * a * l⁻¹ * a⁻¹ ∈ B := by
  classical
  have hnormA : ∀ g ∈ L, ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun g hg => (Subgroup.le_normalizer_iff (H := L) (K := A)).mp hLA g hg
  have hnormB : ∀ g ∈ L, ∀ b ∈ B, g * b * g⁻¹ ∈ B :=
    fun g hg => (Subgroup.le_normalizer_iff (H := L) (K := B)).mp hLB g hg
  have hX : X₁ ⊔ X₂ ≤ commutatorCentralizerIn L B A hLB :=
    sup_le (fun x hx => (mem_commutatorCentralizerIn hLB).mpr ⟨hX₁ hx, h₁ x hx⟩)
      (fun x hx => (mem_commutatorCentralizerIn hLB).mpr ⟨hX₂ hx, h₂ x hx⟩)
  have hPK : P ≤ normalizer ((commutatorCentralizerIn L B A hLB : Subgroup G) : Set G) := by
    refine (Subgroup.le_normalizer_iff (H := P) (K := commutatorCentralizerIn L B A hLB)).mpr
      fun x hx k hk => ?_
    have hxL : x ∈ L := hPL hx
    refine (mem_commutatorCentralizerIn hLB).mpr
      ⟨L.mul_mem (L.mul_mem hxL ((mem_commutatorCentralizerIn hLB).mp hk).1) (L.inv_mem hxL),
        fun a ha => ?_⟩
    have hka : x⁻¹ * a * x ∈ A := by simpa using hnormA x⁻¹ (L.inv_mem hxL) a ha
    have h1 : k * (x⁻¹ * a * x) * k⁻¹ * (x⁻¹ * a * x)⁻¹ ∈ B :=
      ((mem_commutatorCentralizerIn hLB).mp hk).2 _ hka
    have h2 : x * (k * (x⁻¹ * a * x) * k⁻¹ * (x⁻¹ * a * x)⁻¹) * x⁻¹ ∈ B := hnormB x hxL _ h1
    show x * k * x⁻¹ * a * (x * k * x⁻¹)⁻¹ * a⁻¹ ∈ B
    have hid : x * k * x⁻¹ * a * (x * k * x⁻¹)⁻¹ * a⁻¹
        = x * (k * (x⁻¹ * a * x) * k⁻¹ * (x⁻¹ * a * x)⁻¹) * x⁻¹ := by group
    rw [hid]
    exact h2
  have hlKP : l ∈ commutatorCentralizerIn L B A hLB ⊔ P := sup_le_sup_right hX P (hgen hl)
  exact ((mem_commutatorCentralizerIn hLB).mp
    (CFSG.RankThree.PartTwo.Sec14.mem_left_of_coprime_of_isPGroup Fact.out hPK hP hlKP hcop)).2

theorem commutator_mem_of_coprime_of_commutator_mem {p : ℕ} [Fact p.Prime] {P W Z : Subgroup G}
    (hW : IsPGroup p W) (hWZ : W ≤ normalizer (Z : Set G)) {l : G}
    (hcop : (orderOf l).Coprime p) (hlZ : l ∈ normalizer (Z : Set G))
    (h₁ : ∀ x ∈ P, l * x * l⁻¹ * x⁻¹ ∈ W) (h₂ : ∀ w ∈ W, l * w * l⁻¹ * w⁻¹ ∈ Z) :
    ∀ x ∈ P, l * x * l⁻¹ * x⁻¹ ∈ Z := by
  intro x hx
  set w : G := l * x * l⁻¹ * x⁻¹ with hwdef
  have hw : w ∈ W := h₁ x hx
  have hwN : w ∈ normalizer (Z : Set G) := hWZ hw
  have hxw : l * x * l⁻¹ = w * x := by rw [hwdef]; group
  have hz : l * w * l⁻¹ * w⁻¹ ∈ Z := h₂ w hw
  have hzw : l * w * l⁻¹ = (l * w * l⁻¹ * w⁻¹) * w := by group
  have hmain : ∀ k : ℕ, ∃ u ∈ Z, l ^ k * x * (l ^ k)⁻¹ = u * w ^ k * x := by
    intro k
    induction k with
    | zero => exact ⟨1, Z.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, huk⟩ := ih
      have hlu : l * u * l⁻¹ ∈ Z :=
        (Subgroup.le_normalizer_iff (H := normalizer (Z : Set G)) (K := Z)).mp le_rfl l hlZ u hu
      obtain ⟨u', hu', hu'k⟩ := exists_pow_eq_mul_pow hz hwN k
      have hconjpow : (l * w * l⁻¹) ^ k = u' * w ^ k := by rw [hzw, hu'k]
      refine ⟨(l * u * l⁻¹) * u', Z.mul_mem hlu hu', ?_⟩
      calc l ^ (k + 1) * x * (l ^ (k + 1))⁻¹
          = l * (l ^ k * x * (l ^ k)⁻¹) * l⁻¹ := by rw [pow_succ']; group
        _ = l * (u * w ^ k * x) * l⁻¹ := by rw [huk]
        _ = l * u * l⁻¹ * (l * w ^ k * l⁻¹) * (l * x * l⁻¹) := by group
        _ = l * u * l⁻¹ * (u' * w ^ k) * (w * x) := by
              rw [← conj_pow (a := l) (b := w) (i := k), hconjpow, hxw]
        _ = ((l * u * l⁻¹) * u') * w ^ (k + 1) * x := by rw [pow_succ]; group
  obtain ⟨u, hu, huk⟩ := hmain (orderOf l)
  rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at huk
  have h2 : u * w ^ orderOf l = 1 :=
    mul_right_cancel (b := x) (by rw [huk.symm, one_mul])
  have hwk : w ^ orderOf l ∈ Z := (inv_eq_of_mul_eq_one_right h2).symm ▸ Z.inv_mem hu
  have hcpy : (orderOf l).Coprime (orderOf w) := by
    have h3 : (orderOf (⟨w, hw⟩ : W)).Coprime (orderOf l) := hW.orderOf_coprime hcop.symm ⟨w, hw⟩
    simpa using h3.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := w) (n := orderOf l) hcpy
  rw [← hm]
  exact Z.pow_mem hwk m

end CFSG.GroupTheory.CoprimeActionSupport

end
