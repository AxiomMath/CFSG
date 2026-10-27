module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma inv_mul_mem_of_index_le_two {A : Type*} [Group A] [Finite A] {K : Subgroup A}
    (hidx : K.index ≤ 2) {x y : A} (hx : x ∉ K) (hy : y ∉ K) : x⁻¹ * y ∈ K := by
  have h2 : K.index = 2 := by
    have h0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : K.index ≠ 1 := by
      intro h1
      have htop : K = ⊤ := Subgroup.index_eq_one.mp h1
      exact hx (by rw [htop]; exact Subgroup.mem_top x)
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp h2
  have hx' : a * x ∈ K := (xor_iff_iff_not.mp (ha x)).2 hx
  have hy' : a * y ∈ K := (xor_iff_iff_not.mp (ha y)).2 hy
  have hm : (a * x)⁻¹ * (a * y) ∈ K := K.mul_mem (K.inv_mem hx') hy'
  have he : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group
  rwa [he] at hm

private lemma inv_mul_mem_of_relIndex_le_two [Finite G] {I N : Subgroup G}
    (hidx : I.relIndex N ≤ 2) {x y : G} (hx : x ∈ N) (hy : y ∈ N) (hxI : x ∉ I)
    (hyI : y ∉ I) : x⁻¹ * y ∈ I := by
  have hxI' : (⟨x, hx⟩ : N) ∉ I.subgroupOf N := by
    simpa only [Subgroup.mem_subgroupOf] using hxI
  have hyI' : (⟨y, hy⟩ : N) ∉ I.subgroupOf N := by
    simpa only [Subgroup.mem_subgroupOf] using hyI
  have hK : (I.subgroupOf N).index ≤ 2 := hidx
  have h := inv_mul_mem_of_index_le_two (A := N) (K := I.subgroupOf N) hK
    (x := (⟨x, hx⟩ : N)) (y := (⟨y, hy⟩ : N)) hxI' hyI'
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h

private lemma comm_mem_of_mem_inf {t : G} {L S : Subgroup G}
    (hSN : S ≤ normalizer (L : Set G))
    (hU : S ⊓ (L ⊔ centralizer (L : Set G)) ≤ (S ⊓ L) ⊔ zpowers t)
    (hc : ∀ s ∈ S, s * t = t * s)
    {u s : G} (hu : u ∈ S ⊓ (L ⊔ centralizer (L : Set G))) (hs : s ∈ S) :
    u * s * u⁻¹ * s⁻¹ ∈ L := by
  have hcB : ∀ b ∈ S ⊓ L, b * t = t * b := fun b hb => hc b hb.1
  obtain ⟨p, hp, i, hpu⟩ := (mem_sup_zpowers_iff_of_commute hcB).1 (hU hu)
  have hst : t ^ i * s = s * t ^ i :=
    (Commute.zpow_right (show Commute s t from hc s hs) i).symm.eq
  have heq : u * s * u⁻¹ * s⁻¹ = p * (s * p⁻¹ * s⁻¹) := by
    rw [hpu]
    have h1 : (p * t ^ i) * s * (p * t ^ i)⁻¹ * s⁻¹
        = p * (t ^ i * s) * t ^ (-i) * p⁻¹ * s⁻¹ := by group
    rw [h1, hst]
    group
  rw [heq]
  exact L.mul_mem hp.2
    ((Subgroup.mem_normalizer_iff.mp (hSN hs) p⁻¹).1 (L.inv_mem hp.2))

theorem sec10_comm_mem_L [Finite G] {t : G} {L S : Subgroup G}
    (hSN : S ≤ normalizer (L : Set G))
    (hI : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) ≤ 2)
    (hU : S ⊓ (L ⊔ centralizer (L : Set G)) ≤ (S ⊓ L) ⊔ zpowers t)
    (htS : t ∈ S) (hc : ∀ s ∈ S, s * t = t * s) :
    ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ * s₂ * s₁⁻¹ * s₂⁻¹ ∈ L := by
  intro s₁ hs₁ s₂ hs₂
  have hs₁N : s₁ ∈ normalizer (L : Set G) := hSN hs₁
  have hs₂N : s₂ ∈ normalizer (L : Set G) := hSN hs₂
  by_cases hI₁ : s₁ ∈ L ⊔ centralizer (L : Set G)
  · exact comm_mem_of_mem_inf hSN hU hc ⟨hs₁, hI₁⟩ hs₂
  · by_cases hI₂ : s₂ ∈ L ⊔ centralizer (L : Set G)
    · have h := comm_mem_of_mem_inf hSN hU hc (u := s₂) (s := s₁) ⟨hs₂, hI₂⟩ hs₁
      have h2 := L.inv_mem h
      have he : (s₂ * s₁ * s₂⁻¹ * s₁⁻¹)⁻¹ = s₁ * s₂ * s₁⁻¹ * s₂⁻¹ := by group
      rw [he] at h2
      exact h2
    · have huS : s₁⁻¹ * s₂ ∈ S := S.mul_mem (S.inv_mem hs₁) hs₂
      have huI : s₁⁻¹ * s₂ ∈ L ⊔ centralizer (L : Set G) :=
        inv_mul_mem_of_relIndex_le_two hI hs₁N hs₂N hI₁ hI₂
      have hu : s₁⁻¹ * s₂ ∈ S ⊓ (L ⊔ centralizer (L : Set G)) := ⟨huS, huI⟩
      have hm := comm_mem_of_mem_inf hSN hU hc (u := s₁⁻¹ * s₂) (s := s₁) hu hs₁
      have hconj : s₁ * ((s₁⁻¹ * s₂) * s₁ * (s₁⁻¹ * s₂)⁻¹ * s₁⁻¹) * s₁⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hs₁N
          ((s₁⁻¹ * s₂) * s₁ * (s₁⁻¹ * s₂)⁻¹ * s₁⁻¹)).1 hm
      have heq : s₁ * s₂ * s₁⁻¹ * s₂⁻¹ =
          (s₁ * ((s₁⁻¹ * s₂) * s₁ * (s₁⁻¹ * s₂)⁻¹ * s₁⁻¹) * s₁⁻¹)⁻¹ := by group
      rw [heq]
      exact L.inv_mem hconj

end CFSG.OddStandard.SmallF3.Omega
