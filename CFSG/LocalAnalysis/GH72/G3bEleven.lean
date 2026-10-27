module

public import CFSG.LocalAnalysis.GH72.G3bTen
public import CFSG.GroupTheory.InvolutionPair

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6.TStruct (IsFourIn)

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem lemma_3_11 (𝔖 : Sec3Setting G) (h₁ : IsDihNonab 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₁, ∀ y ∈ 𝔖.S₁, orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ Subgroup.centralizer ((𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) : Subgroup G) : Set G),
        g * x * g⁻¹ = y)
    (h₃ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ Subgroup.centralizer ((𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G) : Subgroup G) : Set G),
        g * x * g⁻¹ = y) :
    ∀ x ∈ (𝔖.S : Subgroup G), ∀ y ∈ (𝔖.S : Subgroup G), x ∉ 𝔖.S₁ → x ∉ 𝔖.S₂ → y ∉ 𝔖.S₁ →
      y ∉ 𝔖.S₂ → orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₁, hz₁S₁, hz₁ord, hz₁cent⟩ :=
    exists_central_involution 𝔖.S₁ (isDih_of_isDihNonab h₁)
  obtain ⟨z₂, hz₂S₂, hz₂ord, hz₂cent⟩ :=
    exists_central_involution 𝔖.S₂ (isDih_of_isDihNonab 𝔖.decomp.dih₂)
  have hz₁sq : z₁ * z₁ = 1 := by simpa [hz₁ord, pow_two] using pow_orderOf_eq_one z₁
  have hz₂sq : z₂ * z₂ = 1 := by simpa [hz₂ord, pow_two] using pow_orderOf_eq_one z₂
  have hz₁ne1 : z₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₁ord
    omega
  have hz₂ne1 : z₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₂ord
    omega
  have hz₁C : z₁ ∈ Subgroup.centralizer (𝔖.S₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hz₁cent hy)
  have hz₂C : z₂ ∈ Subgroup.centralizer (𝔖.S₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hz₂cent hy)
  have hz₁Z : z₁ ∈ (𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G) : Subgroup G) :=
    Subgroup.mem_inf.mpr ⟨hz₁S₁, hz₁C⟩
  have hz₂Z : z₂ ∈ (𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) : Subgroup G) :=
    Subgroup.mem_inf.mpr ⟨hz₂S₂, hz₂C⟩
  have hz₂_notS₁ : z₂ ∉ 𝔖.S₁ := by
    intro h
    exact hz₂ne1 (Subgroup.mem_bot.mp (by
      rw [← 𝔖.decomp.inf_eq]
      exact ⟨h, hz₂S₂⟩))
  have hz₁_notS₂ : z₁ ∉ 𝔖.S₂ := by
    intro h
    exact hz₁ne1 (Subgroup.mem_bot.mp (by
      rw [← 𝔖.decomp.inf_eq]
      exact ⟨hz₁S₁, h⟩))
  have hcomm₁₂ : z₁ * z₂ = z₂ * z₁ := 𝔖.decomp.comm hz₁S₁ hz₂S₂
  have hzprod_notS₁ : z₁ * z₂ ∉ 𝔖.S₁ := by
    intro h
    have hz₂S₁ : z₂ ∈ 𝔖.S₁ := by
      have hz₂eq : z₂ = z₁ * (z₁ * z₂) := by rw [← mul_assoc, hz₁sq, one_mul]
      rw [hz₂eq]
      exact mul_mem hz₁S₁ h
    exact hz₂_notS₁ hz₂S₁
  have hzprod_notS₂ : z₁ * z₂ ∉ 𝔖.S₂ := by
    intro h
    have hz₁S₂ : z₁ ∈ 𝔖.S₂ := by
      have hz₁eq : z₁ = (z₁ * z₂) * z₂ := by rw [mul_assoc, hz₂sq, mul_one]
      rw [hz₁eq]
      exact mul_mem h hz₂S₂
    exact hz₁_notS₂ hz₁S₂
  have hzprod_sq : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [hcomm₁₂]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [hz₁sq, hz₂sq, one_mul]
  have hzprod_ne1 : z₁ * z₂ ≠ 1 := by
    intro h
    apply hz₂_notS₁
    have hz₂eq : z₂ = z₁ * (z₁ * z₂) := by rw [← mul_assoc, hz₁sq, one_mul]
    rw [hz₂eq, h, mul_one]
    exact hz₁S₁
  have hzprod_ord : orderOf (z₁ * z₂) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hzprod_ne1
  have hmain : ∀ v ∈ (𝔖.S : Subgroup G), v ∉ 𝔖.S₁ → v ∉ 𝔖.S₂ → orderOf v = 2 →
      IsConj v (z₁ * z₂) := by
    intro v hvS hvS1 hvS2 hvord
    have hvsq : v * v = 1 := by simpa [hvord, pow_two] using pow_orderOf_eq_one v
    obtain ⟨v₁, hv₁S₁, v₂, hv₂S₂, hv, hv₁sq, hv₂sq⟩ :=
      𝔖.decomp.exists_of_mul_self hvS hvsq
    have hv₁ne1 : v₁ ≠ 1 := by
      intro h
      apply hvS2
      rw [hv, h, one_mul]
      exact hv₂S₂
    have hv₂ne1 : v₂ ≠ 1 := by
      intro h
      apply hvS1
      rw [hv, h, mul_one]
      exact hv₁S₁
    have hv₁ord : orderOf v₁ = 2 := orderOf_eq_prime (by rwa [pow_two]) hv₁ne1
    have hv₂ord : orderOf v₂ = 2 := orderOf_eq_prime (by rwa [pow_two]) hv₂ne1
    by_cases hcase : v₁ = z₁ ∨ v₂ = z₂
    ·
      rcases hcase with hv1z | hv2z
      · obtain ⟨g, hg, hgconj⟩ := h₃ v₂ hv₂S₂ z₂ hz₂S₂ hv₂ord hz₂ord
        refine isConj_iff.mpr ⟨g, ?_⟩
        have hgz : g * z₁ * g⁻¹ = z₁ := by
          have hcomm : z₁ * g = g * z₁ := Subgroup.mem_centralizer_iff.mp hg z₁ hz₁Z
          rw [← hcomm]
          group
        calc g * v * g⁻¹ = g * (z₁ * v₂) * g⁻¹ := by rw [hv, hv1z]
          _ = (g * z₁ * g⁻¹) * (g * v₂ * g⁻¹) := by group
          _ = z₁ * z₂ := by rw [hgz, hgconj]
      ·
        obtain ⟨g, hg, hgconj⟩ := h₂ v₁ hv₁S₁ z₁ hz₁S₁ hv₁ord hz₁ord
        refine isConj_iff.mpr ⟨g, ?_⟩
        have hgz : g * z₂ * g⁻¹ = z₂ := by
          have hcomm : z₂ * g = g * z₂ := Subgroup.mem_centralizer_iff.mp hg z₂ hz₂Z
          rw [← hcomm]
          group
        calc g * v * g⁻¹ = g * (v₁ * z₂) * g⁻¹ := by rw [hv, hv2z]
          _ = (g * v₁ * g⁻¹) * (g * z₂ * g⁻¹) := by group
          _ = z₁ * z₂ := by rw [hgconj, hgz]
    ·
      simp only [not_or] at hcase
      obtain ⟨hv1ne, hv2ne⟩ := hcase
      have hcommzv₁ : z₁ * v₁ = v₁ * z₁ :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hz₁cent hv₁S₁)).symm
      have hcommzv₂ : z₂ * v₂ = v₂ * z₂ :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hz₂cent hv₂S₂)).symm
      have hV₁ : IsFourIn 𝔖.S₁ (Subgroup.closure ({z₁, v₁} : Set G)) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [Subgroup.closure_le]
          intro x hx
          rcases hx with rfl | rfl
          · exact hz₁S₁
          · exact hv₁S₁
        · intro x hx
          have hx' : x ∈ ({1, z₁, v₁, z₁ * v₁} : Set G) := by
            have hmem : x ∈ (Subgroup.closure ({z₁, v₁} : Set G) : Set G) := hx
            rwa [CFSG.GroupTheory.coe_closure_pair_eq hz₁sq hv₁sq hcommzv₁ hz₁ne1 hv₁ne1
              (Ne.symm hv1ne)] at hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
          rcases hx' with h | h | h | h
          · rw [h]
            simp
          · rw [h]
            exact hz₁sq
          · rw [h]
            exact hv₁sq
          · rw [h]
            calc (z₁ * v₁) * (z₁ * v₁) = z₁ * (v₁ * z₁) * v₁ := by group
              _ = z₁ * (z₁ * v₁) * v₁ := by rw [hcommzv₁]
              _ = (z₁ * z₁) * (v₁ * v₁) := by group
              _ = 1 := by rw [hz₁sq, hv₁sq, one_mul]
        · exact CFSG.GroupTheory.card_closure_pair_eq_four hz₁sq hv₁sq hcommzv₁ hz₁ne1 hv₁ne1
            (Ne.symm hv1ne)
      have hV₂ : IsFourIn 𝔖.S₂ (Subgroup.closure ({z₂, v₂} : Set G)) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [Subgroup.closure_le]
          intro x hx
          rcases hx with rfl | rfl
          · exact hz₂S₂
          · exact hv₂S₂
        · intro x hx
          have hx' : x ∈ ({1, z₂, v₂, z₂ * v₂} : Set G) := by
            have hmem : x ∈ (Subgroup.closure ({z₂, v₂} : Set G) : Set G) := hx
            rwa [CFSG.GroupTheory.coe_closure_pair_eq hz₂sq hv₂sq hcommzv₂ hz₂ne1 hv₂ne1
              (Ne.symm hv2ne)] at hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
          rcases hx' with h | h | h | h
          · rw [h]
            simp
          · rw [h]
            exact hz₂sq
          · rw [h]
            exact hv₂sq
          · rw [h]
            calc (z₂ * v₂) * (z₂ * v₂) = z₂ * (v₂ * z₂) * v₂ := by group
              _ = z₂ * (z₂ * v₂) * v₂ := by rw [hcommzv₂]
              _ = (z₂ * z₂) * (v₂ * v₂) := by group
              _ = 1 := by rw [hz₂sq, hv₂sq, one_mul]
        · exact CFSG.GroupTheory.card_closure_pair_eq_four hz₂sq hv₂sq hcommzv₂ hz₂ne1 hv₂ne1
            (Ne.symm hv2ne)
      let A : Subgroup G := Subgroup.closure ({z₁, v₁} : Set G) ⊔
        Subgroup.closure ({z₂, v₂} : Set G)
      have hAS : A ≤ (𝔖.S : Subgroup G) :=
        sup_le (hV₁.1.trans 𝔖.decomp.le_left) (hV₂.1.trans 𝔖.decomp.le_right)
      have hA : IsE16 A := 𝔖.decomp.isE16_sup hV₁ hV₂
      have hv₁V₁ : v₁ ∈ Subgroup.closure ({z₁, v₁} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hv₂V₂ : v₂ ∈ Subgroup.closure ({z₂, v₂} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hz₁V₁ : z₁ ∈ Subgroup.closure ({z₁, v₁} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hz₂V₂ : z₂ ∈ Subgroup.closure ({z₂, v₂} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hvA : v ∈ A := by
        rw [hv]
        exact Subgroup.mul_mem_sup hv₁V₁ hv₂V₂
      have hzprodA : z₁ * z₂ ∈ A :=
        Subgroup.mul_mem_sup hz₁V₁ hz₂V₂
      obtain ⟨g, -, hgconj⟩ :=
        (lemma_3_10 𝔖 h₁ h₂ h₃ A hAS hA).2.2.2 v hvA (z₁ * z₂) hzprodA hvord hzprod_ord
          hvS1 hvS2 hzprod_notS₁ hzprod_notS₂
      exact isConj_iff.mpr ⟨g, hgconj⟩
  intro x hxS y hyS hxS1 hxS2 hyS1 hyS2 hxord hyord
  exact (hmain x hxS hxS1 hxS2 hxord).trans (hmain y hyS hyS1 hyS2 hyord).symm

end Sec3Setting

end CFSG.GH72
