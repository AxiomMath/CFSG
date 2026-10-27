module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

private theorem conj_mem_of_le_of_commutator_le {G : Type} [Group G] {Q K : Subgroup G}
    (hKQ : K ≤ Q) (hQK : ⁅Q, Q⁆ ≤ K) {g k : G} (hg : g ∈ Q) (hk : k ∈ K) :
    g * k * g⁻¹ ∈ K := by
  have hk' : k⁻¹ ∈ Q := inv_mem (hKQ hk)
  have hc : ⁅k⁻¹, g⁆ ∈ K := hQK (Subgroup.commutator_mem_commutator hk' hg)
  have he : g * k * g⁻¹ = k * ⁅k⁻¹, g⁆ := by
    rw [commutatorElement_def]
    group
  rw [he]
  exact mul_mem hk hc

private theorem le_normalizer_of_commutator_le {G : Type} [Group G] {Q K : Subgroup G}
    (hKQ : K ≤ Q) (hQK : ⁅Q, Q⁆ ≤ K) : Q ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have hn' : n ∈ K := hn
    exact conj_mem_of_le_of_commutator_le hKQ hQK hg hn'
  · intro hn
    have hn' : g * n * g⁻¹ ∈ K := hn
    have h := conj_mem_of_le_of_commutator_le hKQ hQK (inv_mem hg) hn'
    have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
    rw [e] at h
    exact h

private theorem commutator_zpowers_le_of_normalizer {G : Type} [Group G] {V : Subgroup G}
    {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) : ⁅V, Subgroup.zpowers x⁆ ≤ V := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hx
  rw [Subgroup.commutator_le]
  intro v hv y hy
  have hy' : ∀ n : G, n ∈ (V : Set G) ↔ y * n * y⁻¹ ∈ (V : Set G) :=
    Subgroup.mem_normalizer_iff.mp (hle hy)
  have h1 : y * v⁻¹ * y⁻¹ ∈ V := (hy' v⁻¹).mp (inv_mem hv)
  have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hv h1

private theorem card_sup_mul_card_inf_of_normalizes {G : Type} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAP : A ≤ A ⊔ B := le_sup_left
  have hBP : B ≤ A ⊔ B := le_sup_right
  have hN : A ⊔ B ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hB
  haveI : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr hN
  have hsup : B.subgroupOf (A ⊔ B) ⊔ A.subgroupOf (A ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBP hAP, sup_comm B A, Subgroup.subgroupOf_self]
  have hrel : A.relIndex (A ⊔ B) = (A ⊓ B).relIndex B := by
    have h1 := Subgroup.relIndex_sup_right (B.subgroupOf (A ⊔ B)) (A.subgroupOf (A ⊔ B))
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBP,
      ← Subgroup.inf_relIndex_right A B] at h1
    exact h1
  have h2 := Subgroup.relIndex_mul_card A (A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card (A ⊓ B) B
  rw [inf_eq_left.mpr hAP, hrel] at h2
  rw [inf_eq_left.mpr (inf_le_right : A ⊓ B ≤ B)] at h3
  rw [← h2, ← h3]
  ring

theorem card_comm_zpowers_sup_mul_card {G : Type} [Group G] {Q V₁ V₂ Z : Subgroup G}
    (hQ : V₁ ⊔ V₂ = Q) (hI : V₁ ⊓ V₂ = Z) (hZ₁ : Z ≤ V₁) (hZ₂ : Z ≤ V₂) (hQQ : ⁅Q, Q⁆ ≤ Z)
    {x : G} (hx₁ : x ∈ Subgroup.normalizer (V₁ : Set G))
    (hx₂ : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    Nat.card ↥(⁅Q, Subgroup.zpowers x⁆ ⊔ Z) * Nat.card Z =
      Nat.card ↥(⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) * Nat.card ↥(⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) := by
  have hV₁Q : V₁ ≤ Q := by
    rw [← hQ]
    exact le_sup_left
  have hV₂Q : V₂ ≤ Q := by
    rw [← hQ]
    exact le_sup_right
  have hV₁N : V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    hV₁Q.trans (le_normalizer_of_commutator_le hV₂Q (hQQ.trans hZ₂))
  have hC₁ : ⁅V₁, Subgroup.zpowers x⁆ ≤ V₁ := commutator_zpowers_le_of_normalizer hx₁
  have hC₂ : ⁅V₂, Subgroup.zpowers x⁆ ≤ V₂ := commutator_zpowers_le_of_normalizer hx₂
  have hH₁V : ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z ≤ V₁ := sup_le hC₁ hZ₁
  have hH₂V : ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z ≤ V₂ := sup_le hC₂ hZ₂
  have hH₁Q : ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z ≤ Q := hH₁V.trans hV₁Q
  have hH₂Q : ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z ≤ Q := hH₂V.trans hV₂Q
  have hQH₁ : ⁅Q, Q⁆ ≤ ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z := hQQ.trans le_sup_right
  have hQH₂ : ⁅Q, Q⁆ ≤ ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z := hQQ.trans le_sup_right
  have hN : ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z ≤
      Subgroup.normalizer ((⁅V₁, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) : Set G) :=
    hH₂Q.trans (le_normalizer_of_commutator_le hH₁Q hQH₁)
  have hinf : (⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) ⊓ (⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) = Z := by
    apply le_antisymm
    · exact le_of_le_of_eq (le_inf (inf_le_left.trans hH₁V) (inf_le_right.trans hH₂V)) hI
    · exact le_inf le_sup_right le_sup_right
  have hsup : (⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) ⊔ (⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) =
      ⁅Q, Subgroup.zpowers x⁆ ⊔ Z := by
    apply le_antisymm
    · exact sup_le (sup_le_sup_right (Subgroup.commutator_mono hV₁Q le_rfl) Z)
        (sup_le_sup_right (Subgroup.commutator_mono hV₂Q le_rfl) Z)
    · apply sup_le
      · rw [Subgroup.commutator_le]
        intro q hq y hy
        have hqV : q ∈ (↑(V₁ ⊔ V₂) : Set G) := by
          rw [hQ]
          exact hq
        rw [Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ hV₁N, Set.mem_mul] at hqV
        obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hqV
        have hv₁' : v₁ ∈ V₁ := hv₁
        have hv₂' : v₂ ∈ V₂ := hv₂
        have e : ⁅v₁ * v₂, y⁆ = (v₁ * ⁅v₂, y⁆ * v₁⁻¹) * ⁅v₁, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have hk₂ : ⁅v₂, y⁆ ∈ ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z :=
          Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv₂' hy)
        have hcj : v₁ * ⁅v₂, y⁆ * v₁⁻¹ ∈ ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z :=
          conj_mem_of_le_of_commutator_le hH₂Q hQH₂ (hV₁Q hv₁') hk₂
        have hc₁ : ⁅v₁, y⁆ ∈ ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z :=
          Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv₁' hy)
        exact mul_mem (Subgroup.mem_sup_right hcj) (Subgroup.mem_sup_left hc₁)
      · exact (le_sup_right : Z ≤ ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z).trans le_sup_left
  have hkey := card_sup_mul_card_inf_of_normalizes
    (A := ⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) (B := ⁅V₂, Subgroup.zpowers x⁆ ⊔ Z) hN
  rw [hsup, hinf] at hkey
  exact hkey

end CFSG.GroupTheory

end
