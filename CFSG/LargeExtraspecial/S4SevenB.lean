module

public import CFSG.LargeExtraspecial.S4EightF3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

universe u

theorem commutator_sup_le_inf {X : Type*} [Group X] {A B : Subgroup X}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBA : B ≤ normalizer (A : Set X)) (hAB : A ≤ normalizer (B : Set X)) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ A ⊓ B := by
  have hc : ∀ a ∈ A, ∀ b ∈ B, b * a * b⁻¹ * a⁻¹ ∈ A ⊓ B := by
    intro a ha b hb
    refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp (hBA hb) a).mp ha) (inv_mem ha), ?_⟩
    rw [show b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) by group]
    exact mul_mem hb ((mem_normalizer_iff.mp (hAB ha) b⁻¹).mp (inv_mem hb))
  have hzA : ∀ z ∈ A ⊓ B, ∀ a ∈ A, z * a = a * z := fun z hz a ha => hA z (mem_inf.mp hz).1 a ha
  have hzB : ∀ z ∈ A ⊓ B, ∀ b ∈ B, z * b = b * z := fun z hz b hb => hB z (mem_inf.mp hz).2 b hb
  have hset := coe_mul_of_right_le_normalizer_left A B hBA
  rw [commutator_le]
  intro x hx y hy
  have hx' : x ∈ ((A ⊔ B : Subgroup X) : Set X) := hx
  have hy' : y ∈ ((A ⊔ B : Subgroup X) : Set X) := hy
  rw [hset] at hx' hy'
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx'
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy'
  set c₁ := b₁ * a₂ * b₁⁻¹ * a₂⁻¹ with hc₁
  set c₂ := b₂ * a₁⁻¹ * b₂⁻¹ * a₁ with hc₂
  have h₁ : c₁ ∈ A ⊓ B := hc a₂ ha₂ b₁ hb₁
  have h₂ : c₂ ∈ A ⊓ B := by
    have := hc a₁⁻¹ (inv_mem ha₁) b₂ hb₂
    rwa [inv_inv] at this
  have e₁ : b₁ * a₂ * b₁⁻¹ = c₁ * a₂ := by rw [hc₁]; group
  have e₂ : b₂ * a₁⁻¹ * b₂⁻¹ = c₂ * a₁⁻¹ := by rw [hc₂]; group
  have hb : b₂ * b₁⁻¹ = b₁⁻¹ * b₂ := hB _ hb₂ _ (inv_mem hb₁)
  have key : ⁅a₁ * b₁, a₂ * b₂⁆ = c₁ * c₂ := by
    calc ⁅a₁ * b₁, a₂ * b₂⁆ = a₁ * (b₁ * a₂ * b₁⁻¹) * (b₂ * a₁⁻¹ * b₂⁻¹) * a₂⁻¹ := by
          rw [commutatorElement_def]
          calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
              = a₁ * b₁ * a₂ * (b₂ * b₁⁻¹) * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
            _ = a₁ * b₁ * a₂ * (b₁⁻¹ * b₂) * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [hb]
            _ = _ := by group
      _ = a₁ * (c₁ * a₂) * (c₂ * a₁⁻¹) * a₂⁻¹ := by rw [e₁, e₂]
      _ = c₁ * (a₁ * a₂) * (c₂ * a₁⁻¹) * a₂⁻¹ := by
          rw [show a₁ * (c₁ * a₂) = (a₁ * c₁) * a₂ by group, ← hzA c₁ h₁ a₁ ha₁]; group
      _ = c₁ * c₂ * (a₁ * a₂) * a₁⁻¹ * a₂⁻¹ := by
          rw [show c₁ * (a₁ * a₂) * (c₂ * a₁⁻¹) = c₁ * ((a₁ * a₂) * c₂) * a₁⁻¹ by group,
            ← hzA c₂ h₂ _ (mul_mem ha₁ ha₂)]
          group
      _ = c₁ * c₂ := by
          rw [hA a₁ ha₁ a₂ ha₂]
          group
  rw [key]
  exact mul_mem h₁ h₂

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_mem_Rbar_beta_eq_one (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    ∃ k : S.M, ∃ hk : S.ρ k ∈ Rbar S g t,
      beta H C ht ht1 hVQ (aV ht) (orbV H.conj_mem ht hk) = 1 := by
  by_contra h
  push Not at h
  apply aV_ne_zero H ht
  refine (beta_nondegenerate H C ht ht1 hVQ).1 _ fun y => ?_
  have hy : y ∈ Submodule.span (ZMod 2) (orbitOf (RmodN S g t) (aV ht)) := by
    rw [span_orbitOf_RmodN H ht]
    trivial
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨e, ⟨x, hx, hex⟩, rfl⟩ := hv
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
    have he : e (aV ht) = orbV H.conj_mem ht hx := Subtype.ext (hex _)
    rw [he]
    exact (zmod2_eq_zero_or_eq_one _).resolve_right (h k hx)
  | zero => simp
  | add u w _ _ hu hw => rw [map_add, hu, hw, add_zero]
  | smul c u _ hu => rw [map_smul, hu, smul_zero]

end CFSG.LargeExtraspecial.S4
