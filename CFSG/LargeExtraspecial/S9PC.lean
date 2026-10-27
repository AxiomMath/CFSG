module

public import CFSG.LargeExtraspecial.S8Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_map_Wt_add_finrank_Vt {t : S.O} (τ : S.O) :
    finrank (ZMod 2) ((Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) +
      finrank (ZMod 2) (Vt S g t) =
      finrank (ZMod 2) ↥(Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hk := S8.finrank_map_add_finrank_inf_ker
    ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) (Wt S g t)
  have hO := fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate τ.2
  have hinf : Wt S g t ⊓ LinearMap.ker ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) =
      LinearMap.BilinForm.orthogonal S.q.polarBilin
        (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    ext v
    rw [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨hvW, hvk⟩ x hx
      obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
      have h1 : S.q.polarBilin u v = 0 := by
        rw [polarBilin_apply_apply]; exact mem_Wt.mp hvW u hu
      have h2 : S.q.polarBilin c v = 0 := by
        have h3 : v ∈ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := hvk
        rw [hO, LinearMap.BilinForm.mem_orthogonal_iff] at h3
        exact h3 c hc
      change S.q.polarBilin (u + c) v = 0
      rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    · intro h
      refine ⟨mem_Wt.mpr fun u hu => ?_, ?_⟩
      · have h1 : S.q.polarBilin u v = 0 := h u (Submodule.mem_sup_left hu)
        rwa [polarBilin_apply_apply] at h1
      · change v ∈ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)
        rw [hO, LinearMap.BilinForm.mem_orthogonal_iff]
        exact fun c hc => h c (Submodule.mem_sup_right hc)
  rw [hinf] at hk
  have h2 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate
    (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have h3 := finrank_Wt (S := S) (g := g) (t := t)
  have h4 := Submodule.finrank_le (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  omega

theorem finrank_commWV_of_inf_eq_bot (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x : S.O}
    (hinf : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    finrank (ZMod 2) (S8.commWV S g t (x * t * x⁻¹)) = finrank (ZMod 2) (Vt S g t) := by
  have hform := finrank_map_Wt_add_finrank_Vt (S := S) (g := g) (t := t) (x * t * x⁻¹)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
    (commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
  rw [hinf, finrank_bot] at hsum
  have hC := S8.finrank_commSpace_conj H C ht ht1 hVQ (x := x) (τ := x * t * x⁻¹) rfl
  have hk := S8.finrank_map_add_finrank_inf_ker (Vt S g t).mkQ
    ((Wt S g t).map (((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1))
  rw [Submodule.ker_mkQ] at hk
  have hbot : (Wt S g t).map (((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊓
      Vt S g t = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    rintro _ ⟨⟨w, -, rfl⟩, hV⟩
    exact Submodule.mem_inf.mpr ⟨hV, sub_mem_commSpace _ w⟩
  rw [hbot, finrank_bot] at hk
  change finrank (ZMod 2) (((Wt S g t).map
    (((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Vt S g t).mkQ) = _
  omega

end CFSG.LargeExtraspecial.S9
