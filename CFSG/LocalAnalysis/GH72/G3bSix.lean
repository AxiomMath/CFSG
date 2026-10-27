module

public import CFSG.LocalAnalysis.GH72.G3bFive
public import CFSG.LocalAnalysis.GH72.L2Local

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6.TStruct (IsFourIn)

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem lemma_3_6 (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (h₃ : ∃ n : ℕ, ∃ u ∈ normalizer ((𝔖.S : Subgroup G) : Set G), orderOf u = 3 ^ n ∧
      u ∈ normalizer (𝔖.S₁ : Set G) ∧ u ∉ centralizer (𝔖.S₁ : Set G)) :
    ∀ x ∈ (𝔖.S : Subgroup G), ∀ y ∈ (𝔖.S : Subgroup G), x ∉ 𝔖.S₁ → x ∉ 𝔖.S₂ → y ∉ 𝔖.S₁ →
      y ∉ 𝔖.S₂ → orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  classical
  obtain ⟨z₂, hz₂S₂, hz₂ord, hz₂Z⟩ := 𝔖.decomp.dih₂.exists_inf_centralizer_self_eq
  have hz₂1 : z₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₂ord
    norm_num at hz₂ord
  have hz₂2 : z₂ * z₂ = 1 := by
    rw [← pow_two, ← hz₂ord]
    exact pow_orderOf_eq_one z₂
  have hz₂centS₂ : ∀ y ∈ 𝔖.S₂, y * z₂ = z₂ * y := by
    intro y hy
    have hz : z₂ ∈ 𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G) := by
      rw [hz₂Z]
      exact Subgroup.mem_zpowers z₂
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y hy
  obtain ⟨z₁, hz₁S₁, hz₁1⟩ := exists_mem_kleinFour_ne h₁ (one_mem 𝔖.S₁)
  have hz₁1' : z₁ ≠ 1 := hz₁1.1
  have hz₁2 : z₁ * z₁ = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_kleinFour h₁ hz₁S₁
  have key : ∀ v ∈ (𝔖.S : Subgroup G), v ∉ 𝔖.S₁ → v ∉ 𝔖.S₂ → orderOf v = 2 →
      IsConj v (z₁ * z₂) := by
    intro v hvS hvS₁ hvS₂ hvord
    obtain ⟨v₁, hv₁S₁, v₂, hv₂S₂, hv_eq⟩ := 𝔖.decomp.mem_iff.1 hvS
    have hv₁2 : v₁ * v₁ = 1 := by
      rw [← pow_two]
      exact sq_eq_one_of_mem_kleinFour h₁ hv₁S₁
    have hv_sq : v * v = 1 := by
      rw [← pow_two, ← hvord]
      exact pow_orderOf_eq_one v
    have hv₂2 : v₂ * v₂ = 1 := by
      have h := hv_sq
      rw [hv_eq] at h
      exact ((𝔖.decomp.mul_self_iff hv₁S₁ hv₂S₂).mp h).2
    have hv₁1 : v₁ ≠ 1 := by
      intro h
      apply hvS₂
      rw [hv_eq, h, one_mul]
      exact hv₂S₂
    have hv₂1 : v₂ ≠ 1 := by
      intro h
      apply hvS₁
      rw [hv_eq, h, mul_one]
      exact hv₁S₁
    obtain ⟨V₂, hV₂, hv₂V₂⟩ := 𝔖.decomp.isDih₂.exists_four_mem hv₂S₂ hv₂2
    have hz₂V₂ : z₂ ∈ V₂ :=
      𝔖.decomp.isDih₂.mem_four_of_central hV₂ hz₂S₂ hz₂centS₂
    let A : Subgroup G := 𝔖.S₁ ⊔ V₂
    have h₁V : IsFourIn 𝔖.S₁ 𝔖.S₁ := IsDih.isFourIn_self_of_isKleinFour h₁
    have hA : IsE16 A := 𝔖.decomp.isE16_sup h₁V hV₂
    have hAS : A ≤ (𝔖.S : Subgroup G) :=
      sup_le 𝔖.decomp.le_left (hV₂.1.trans 𝔖.decomp.le_right)
    have hvA : v ∈ A := by
      rw [hv_eq]
      exact mul_mem (Subgroup.mem_sup_left hv₁S₁) (Subgroup.mem_sup_right hv₂V₂)
    have hwA : z₁ * z₂ ∈ A :=
      mul_mem (Subgroup.mem_sup_left hz₁S₁) (Subgroup.mem_sup_right hz₂V₂)
    have hw_sq : z₁ * z₂ * (z₁ * z₂) = 1 :=
      (𝔖.decomp.mul_self_iff hz₁S₁ hz₂S₂).mpr ⟨hz₁2, hz₂2⟩
    have hw_notS₁ : z₁ * z₂ ∉ 𝔖.S₁ := by
      rw [𝔖.decomp.mul_mem_left_iff hz₁S₁ hz₂S₂]
      exact hz₂1
    have hw_notS₂ : z₁ * z₂ ∉ 𝔖.S₂ := by
      rw [𝔖.decomp.mul_mem_right_iff hz₁S₁ hz₂S₂]
      exact hz₁1'
    have hw_ne1 : z₁ * z₂ ≠ 1 := fun h => hw_notS₁ (h ▸ Subgroup.one_mem _)
    have hw2 : orderOf (z₁ * z₂) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hw_sq) hw_ne1
    obtain ⟨g, -, hg⟩ :=
      (lemma_3_5 𝔖 h₁ h₂ h₃ A hAS hA).2.2.2 v hvA (z₁ * z₂) hwA hvord hw2
        hvS₁ hvS₂ hw_notS₁ hw_notS₂
    exact isConj_iff.mpr ⟨g, hg⟩
  intro x hx y hy hxS₁ hxS₂ hyS₁ hyS₂ hx2 hy2
  exact (key x hx hxS₁ hxS₂ hx2).trans (key y hy hyS₁ hyS₂ hy2).symm

end Sec3Setting

end CFSG.GH72
