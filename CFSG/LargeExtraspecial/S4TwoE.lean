module

public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.LargeExtraspecial.S4Span
public import CFSG.LargeExtraspecial.S4TwoC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.CGT.Timmesfeld75

section Abstract

variable {K₀ : Type} [Group K₀] [Finite K₀] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem bender_dichotomy (hβ : β.IsAlt) (φ : K₀ →* (V ≃ₗ[ZMod 2] V))
    (hφ : ∀ k, φ k ∈ TauCeti.BilinForm.isometryGroup β) {T₀ : Subgroup K₀} (v : V)
    (hpt : ∀ k k' : K₀, conjSubgroup k T₀ = conjSubgroup k' T₀ ↔ φ k v = φ k' v)
    (h2 : ConjTwoTransitive K₀ T₀) :
    (∀ k, β v (φ k v) = 0) ∨
      Nat.card (Set.range fun k : K₀ => conjSubgroup k T₀) ≤ finrank (ZMod 2) V + 1 := by
  classical
  by_cases h : ∀ k, β v (φ k v) = 0
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨k₀, hk₀⟩ := h
  have hk₀1 : β v (φ k₀ v) = 1 := CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero hk₀
  have hne₀ : φ 1 v ≠ φ k₀ v := by
    intro h
    rw [map_one] at h
    have hv : v = φ k₀ v := h
    rw [← hv, hβ.self_eq_zero] at hk₀1
    exact zero_ne_one hk₀1
  have hval : ∀ k₁ k₂ : K₀, φ k₁ v ≠ φ k₂ v → β (φ k₁ v) (φ k₂ v) = 1 := by
    intro k₁ k₂ h12
    obtain ⟨k, hk1, hk2⟩ := h2 1 k₀ k₁ k₂ (fun h => hne₀ ((hpt _ _).mp h))
      (fun h => h12 ((hpt _ _).mp h))
    have e1 := (hpt _ _).mp hk1
    have e2 := (hpt _ _).mp hk2
    rw [mul_one] at e1
    rw [← e1, ← e2, map_mul, LinearEquiv.mul_apply,
      TauCeti.BilinForm.mem_isometryGroup_iff.mp (hφ k)]
    exact hk₀1
  have : Fintype K₀ := Fintype.ofFinite K₀
  set P : Finset V := Finset.univ.image fun k : K₀ => φ k v
  have hP : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → β x y = 1 := by
    intro x hx y hy hxy
    obtain ⟨k₁, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k₂, -, rfl⟩ := Finset.mem_image.mp hy
    exact hval k₁ k₂ hxy
  have hcard := card_le_finrank_add_one_of_beta_eq_one hβ hP
  have hbij : Nat.card (Set.range fun k : K₀ => conjSubgroup k T₀) = P.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.ofBijective (fun X => ⟨φ X.2.choose v, ?_⟩) ⟨?_, ?_⟩)
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · intro X Y hXY
      have h1 : φ X.2.choose v = φ Y.2.choose v := congrArg Subtype.val hXY
      apply Subtype.ext
      rw [← X.2.choose_spec, ← Y.2.choose_spec]
      exact (hpt _ _).mpr h1
    · rintro ⟨x, hx⟩
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨⟨conjSubgroup k T₀, k, rfl⟩, Subtype.ext ?_⟩
      exact (hpt _ _).mp (((⟨conjSubgroup k T₀, k, rfl⟩ :
        Set.range fun k : K₀ => conjSubgroup k T₀).2.choose_spec))
  omega

end Abstract

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem map_conj_Lbar_eq_iff (H : Hyp4 S g) {x y : S.O} (hx : x ∈ S.Mbar) (hy : y ∈ S.Mbar) :
    (S.Lbar g).map (MulAut.conj x).toMonoidHom = (S.Lbar g).map (MulAut.conj y).toMonoidHom ↔
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [← Lbar_mul S h, ← Lbar_mul S k, ρ_cl_conj_z S h H.conj_mem, ρ_cl_conj_z S k H.conj_mem]
  constructor
  · exact cl_eq_of_Lbar_eq H
  · intro e
    exact (Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 H.conj_mem) (conj_ne_z' S k.2 H.conj_ne)
      (conj_mem_QG' S h.2 H.conj_mem) e)

end CFSG.LargeExtraspecial.S4
