module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma normalizer_le_normalizer_centralizer {G : Type} [Group G] (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (centralizer (X : Set G) : Set G) := by
  intro x hx
  have hx' : ∀ y, y ∈ X ↔ x * y * x⁻¹ ∈ X := Subgroup.mem_normalizer_iff.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    have hy' : x⁻¹ * y * x ∈ X := (hx' _).mpr (by
      rw [show x * (x⁻¹ * y * x) * x⁻¹ = y by group]; exact hy)
    have h1 := hc (x⁻¹ * y * x) hy'
    calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * y := by group
  · intro hc y hy
    have hy' : x * y * x⁻¹ ∈ X := (hx' _).mp hy
    have h1 := hc (x * y * x⁻¹) hy'
    calc y * c = x⁻¹ * ((x * y * x⁻¹) * (x * c * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * c * x⁻¹) * (x * y * x⁻¹)) * x := by rw [h1]
      _ = c * y := by group

theorem sec8t84_ded {G : Type} [Group G] {S L M : Subgroup G} {t : G}
    (hMS : M ≤ S) (hSN : S ≤ normalizer (L : Set G))
    (hC : S ⊓ centralizer (L : Set G) = zpowers t)
    (h : S ≤ M ⊔ centralizer (L : Set G)) : S = M ⊔ zpowers t := by
  let C : Subgroup G := centralizer (L : Set G)
  have hMC : M ≤ normalizer (C : Set G) :=
    (hMS.trans hSN).trans (normalizer_le_normalizer_centralizer L)
  refine le_antisymm ?_ (sup_le hMS ?_)
  · intro s hs
    have hsMC : s ∈ M ⊔ C := h hs
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right M C hMC,
      Set.mem_mul] at hsMC
    obtain ⟨m, hm, c, hc, hmc⟩ := hsMC
    have hcS : c ∈ S := by
      have : c = m⁻¹ * s := by rw [← hmc]; group
      rw [this]
      exact S.mul_mem (S.inv_mem (hMS hm)) hs
    have hcz : c ∈ zpowers t := by
      rw [← hC]
      exact Subgroup.mem_inf.mpr ⟨hcS, hc⟩
    rw [← hmc]
    exact Subgroup.mul_mem_sup hm hcz
  · rw [← hC]
    exact inf_le_left

end CFSG.OddStandard.SmallF3.Omega
