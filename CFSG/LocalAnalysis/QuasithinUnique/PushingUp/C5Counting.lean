module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.QuasithinUnique.C5

open Subgroup

variable {G : Type*} [Group G]

theorem relIndex_sup_eq_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

theorem card_eq_card_mul_relIndex [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card K = Nat.card H * H.relIndex K := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact (Subgroup.card_mul_index _).symm

theorem card_sup_mul_card_inf_of_le_normalizer [Finite G] {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := card_eq_card_mul_relIndex (le_sup_right : B ≤ A ⊔ B)
  have h2 := card_eq_card_mul_relIndex (inf_le_left : A ⊓ B ≤ A)
  have h3 : (A ⊓ B).relIndex A = B.relIndex A := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  rw [h1, h2, relIndex_sup_eq_of_le_normalizer h, h3]
  ring

theorem relIndex_inf_eq_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) : (A ⊓ B).relIndex A = B.relIndex (A ⊔ B) := by
  rw [relIndex_sup_eq_of_le_normalizer h, inf_comm]
  exact Subgroup.inf_relIndex_right B A

theorem eq_of_relIndex_eq {H X K : Subgroup G} (hHX : H ≤ X) (hXK : X ≤ K)
    (h : H.relIndex X = H.relIndex K) (hfin : H.relIndex K ≠ 0) : X = K := by
  have h1 := Subgroup.relIndex_mul_relIndex H X K hHX hXK
  rw [h] at h1
  have h2 : X.relIndex K = 1 := by
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hfin) (h1.trans (mul_one _).symm)
    exact this
  exact le_antisymm hXK (Subgroup.relIndex_eq_one.mp h2)

theorem relIndex_le_of_le [Finite G] {H X K : Subgroup G} (h1 : H ≤ X) (h2 : X ≤ K) :
    H.relIndex X ≤ H.relIndex K := by
  have := Subgroup.relIndex_mul_relIndex H X K h1 h2
  have hpos : 0 < X.relIndex K :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := X.subgroupOf K))
  calc H.relIndex X = H.relIndex X * 1 := (mul_one _).symm
    _ ≤ H.relIndex X * X.relIndex K := Nat.mul_le_mul_left _ hpos
    _ = H.relIndex K := this

theorem relIndex_le_of_le_left [Finite G] {H C : Subgroup G} (h : H ≤ C) (Q : Subgroup G) :
    C.relIndex Q ≤ H.relIndex Q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf Q)))
    (Subgroup.relIndex_dvd_of_le_left Q h)

theorem le_normalizer_centralizer_self (K : Subgroup G) :
    K ≤ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : g * y = y * g := Subgroup.mem_centralizer_iff.mp hy g hg
    have h2 : g * y * g⁻¹ = y := by rw [h1]; group
    rw [h2]; exact hy
  · intro hy
    have h1 := Subgroup.mem_centralizer_iff.mp hy g hg
    have e : g * (g * y * g⁻¹) = g * y := by rw [h1]; group
    have h2 : g * y * g⁻¹ = y := mul_left_cancel e
    rw [h2] at hy; exact hy

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  simp only [Subgroup.mem_inf]
  rw [hA y, hB y]

theorem exists_max_card [Finite G] (P : Subgroup G → Prop) (hP : P ⊥) :
    ∃ A : Subgroup G, P A ∧ ∀ B : Subgroup G, P B → Nat.card B ≤ Nat.card A := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P)
    (fun A : Subgroup G => Nat.card A) ⟨⊥, by simp [hP]⟩
  exact ⟨A, (Finset.mem_filter.mp hA).2, fun B hB => hmax B (by simp [hB])⟩

end CFSG.QuasithinUnique.C5
