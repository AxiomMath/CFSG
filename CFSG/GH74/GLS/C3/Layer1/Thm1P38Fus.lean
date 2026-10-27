module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

theorem transport_fusion_G' {G : Type} [Group G] [Finite G] {C K T E₁ : Subgroup G}
    (hKC : K ≤ C) (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hT : IsSylowOf 2 T C)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)))
    (hAut : AutLevelF (kBar K)) (hE₁T : E₁ ≤ T) (hE₁ : IsElementaryAbelian 2 ↥E₁)
    (hE₁16 : 16 ≤ Nat.card ↥E₁)
    (hQ : ∀ A : Subgroup G, A ≤ CMK C K → IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2)
    {f z : G} (hfT : f ∈ T) (hf2 : orderOf f = 2) (hfc : ∀ p ∈ T ⊓ K, f * p = p * f)
    (hfinn : ∀ hfC : f ∈ C, Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K))
    (hz : z ∈ T ⊓ K) (hz2 : orderOf z = 2) (hzc : ∀ p ∈ T ⊓ K, z * p = p * z) :
    ∀ u ∈ T ⊓ K ⊔ zpowers f, orderOf u = 2 →
      ∃ g ∈ K ⊔ zpowers f, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = f ∨ g * u * g⁻¹ = f * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu hu2
  have hPC : T ⊓ K ≤ C := inf_le_right.trans hKC
  have hfC : f ∈ C := hT.le hfT
  have hzC : z ∈ C := hPC hz
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁, hz₁2, hz₁c, hz₁u, hfus, -, -⟩ :=
    core_lift_G hKC hKN hT hcen hAut hE₁T hE₁ hE₁16 hQ
  have hzP : (⟨z, hzC⟩ : ↥C) ∈ (T ⊓ K).subgroupOf C := hz
  have hzz₁ : (⟨z, hzC⟩ : ↥C) = z₁ := by
    rcases hz₁u ⟨z, hzC⟩ hzP (fun q hq => Subtype.ext (hzc (q : G) hq)) with h | h
    · exfalso
      have : z = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hz2
      omega
    · exact h
  have hfCT : (⟨f, hfC⟩ : ↥C) ∈ T.subgroupOf C := hfT
  have hfC2 : orderOf (⟨f, hfC⟩ : ↥C) = 2 := by rw [Subgroup.orderOf_mk]; exact hf2
  have hfCc : ∀ p ∈ (T ⊓ K).subgroupOf C, (⟨f, hfC⟩ : ↥C) * p = p * ⟨f, hfC⟩ := by
    intro p hp
    exact Subtype.ext (hfc p hp)
  have huC : u ∈ C := by
    have hle : T ⊓ K ⊔ zpowers f ≤ C := sup_le hPC ((zpowers_le).2 hfC)
    exact hle hu
  have hmap : ((T ⊓ K).subgroupOf C ⊔ zpowers (⟨f, hfC⟩ : ↥C)).map C.subtype =
      T ⊓ K ⊔ zpowers f := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC,
      MonoidHom.map_zpowers]
    rfl
  obtain ⟨u', hu', hu'u⟩ : ∃ u' ∈ (T ⊓ K).subgroupOf C ⊔ zpowers (⟨f, hfC⟩ : ↥C), (u' : G) = u := by
    rw [← hmap] at hu
    exact hu
  have hu'2 : orderOf u' = 2 := by rw [← Subgroup.orderOf_coe, hu'u]; exact hu2
  obtain ⟨g, hg, hgu⟩ := hfus ⟨f, hfC⟩ hfCT hfC2 hfCc (hfinn hfC) u' hu' hu'2
  rw [← map_actHom_K hKC hKN] at hg
  obtain ⟨k', hk', rfl⟩ := hg
  have hkK : (k' : G) ∈ K := hk'
  set k : G := (k' : G) with hk
  have hvC : k * u * k⁻¹ ∈ C := C.mul_mem (C.mul_mem k'.2 huC) (C.inv_mem k'.2)
  have hφv : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ =
      Back.actHom hKN k' * Back.actHom hKN u' * (Back.actHom hKN k')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [hk, hu'u])
  have hMu : u ∈ K ⊔ zpowers f := (sup_le_sup_right (inf_le_right : T ⊓ K ≤ K) _) hu
  have hMf : f ∈ K ⊔ zpowers f := Subgroup.mem_sup_right (mem_zpowers f)
  have hMz : z ∈ K ⊔ zpowers f := Subgroup.mem_sup_left hz.2
  have hMk : k ∈ K ⊔ zpowers f := Subgroup.mem_sup_left hkK
  have hMv : k * u * k⁻¹ ∈ K ⊔ zpowers f :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hMk hMu) (Subgroup.inv_mem _ hMk)
  have hv2 : orderOf (k * u * k⁻¹) = 2 := by
    rw [← hu2]
    exact (MulAut.conj k).orderOf_eq u
  have hfzC : f * z ∈ C := C.mul_mem hfC hzC
  have hfz2 : orderOf (f * z) = 2 := by
    have hfz : f * z = z * f := hfc z hz
    have hφfz : Back.actHom hKN ⟨f * z, hfzC⟩ ∉ innAut (kBar K) := by
      intro h
      apply hfinn hfC
      have h1 : (⟨f * z, hfzC⟩ : ↥C) = ⟨f, hfC⟩ * ⟨z, hzC⟩ := rfl
      rw [h1, map_mul] at h
      have hφz : Back.actHom hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
        rw [Back.actHom_of_mem hKN hz.2 hzC]
        exact ⟨_, rfl⟩
      have := (innAut (kBar K)).mul_mem h ((innAut (kBar K)).inv_mem hφz)
      simpa using this
    have hfz1 : f * z ≠ 1 := fun h => hφfz (by
      have : (⟨f * z, hfzC⟩ : ↥C) = 1 := Subtype.ext h
      rw [this, map_one]
      exact (innAut (kBar K)).one_mem)
    refine orderOf_eq_prime ?_ hfz1
    calc (f * z) ^ 2 = f * z * (f * z) := sq _
      _ = f * (z * f) * z := by simp only [mul_assoc]
      _ = f * (f * z) * z := by rw [← hfz]
      _ = (f * f) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [hff, hzz, one_mul]
  have hMfz : f * z ∈ K ⊔ zpowers f := Subgroup.mul_mem _ hMf hMz
  rw [← hzz₁] at hgu
  rcases hgu with h | h | h
  ·
    have heq : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ = Back.actHom hKN ⟨z, hzC⟩ := by
      rw [hφv]; exact h
    obtain ⟨h₀, hh₀, hh₀v⟩ := conj_of_same_image hKC hKN hcen hfC hff (hfinn hfC) hMv hMz hv2 hz2 hvC hzC heq
    refine ⟨h₀⁻¹ * k, (K ⊔ zpowers f).mul_mem ((K ⊔ zpowers f).inv_mem hh₀) hMk, Or.inl ?_⟩
    rw [← hh₀v]
    group
  · have heq : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ = Back.actHom hKN ⟨f, hfC⟩ := by
      rw [hφv]; exact h
    obtain ⟨h₀, hh₀, hh₀v⟩ := conj_of_same_image hKC hKN hcen hfC hff (hfinn hfC) hMv hMf hv2 hf2 hvC hfC heq
    refine ⟨h₀⁻¹ * k, (K ⊔ zpowers f).mul_mem ((K ⊔ zpowers f).inv_mem hh₀) hMk, Or.inr (Or.inl ?_)⟩
    rw [← hh₀v]
    group
  · have heq : Back.actHom hKN ⟨k * u * k⁻¹, hvC⟩ = Back.actHom hKN ⟨f * z, hfzC⟩ := by
      rw [hφv, h]
      have h1 : (⟨f * z, hfzC⟩ : ↥C) = ⟨f, hfC⟩ * ⟨z, hzC⟩ := rfl
      rw [h1, map_mul]
    obtain ⟨h₀, hh₀, hh₀v⟩ := conj_of_same_image hKC hKN hcen hfC hff (hfinn hfC) hMv hMfz hv2 hfz2 hvC hfzC heq
    refine ⟨h₀⁻¹ * k, (K ⊔ zpowers f).mul_mem ((K ⊔ zpowers f).inv_mem hh₀) hMk, Or.inr (Or.inr ?_)⟩
    rw [← hh₀v]
    group

end CFSG.GH74.GLS.C3.Layer1.Thm1
