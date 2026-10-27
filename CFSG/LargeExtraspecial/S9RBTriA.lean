module

public import CFSG.LargeExtraspecial.S8Rad
public import CFSG.LargeExtraspecial.S9GenG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commSpace_mul_le (x y : S.O) :
    commSpace ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  intro v hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  rw [coe_mul_apply]
  have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
      ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
  rw [e]
  exact Submodule.add_mem_sup (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)

theorem finrank_sup_of_inf_eq_bot {A B : Submodule (ZMod 2) S.Qt} (h : A ⊓ B = ⊥) :
    finrank (ZMod 2) ↥(A ⊔ B) = finrank (ZMod 2) A + finrank (ZMod 2) B := by
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [h, finrank_bot] at this
  omega

theorem sup_eq_sup_of_mul {t τ₁ τ₂ : S.O} {V : Submodule (ZMod 2) S.Qt}
    (hV : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = V) (htt : t * t = 1)
    (h4 : finrank (ZMod 2) V = 4)
    (i₁ : V ⊓ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (i₂ : V ⊓ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (i₃ : V ⊓ commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥)
    (f₁ : finrank (ZMod 2) (commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4)
    (f₂ : finrank (ZMod 2) (commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4)
    (f₃ : finrank (ZMod 2) (commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4)
    (w₃ : ∀ v ∈ commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    V ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        V ⊔ commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      V ⊔ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        V ⊔ commSpace ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  set τ₃ := t * τ₁ * τ₂ with hτ₃
  set U := V ⊔ commSpace (τ₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  have dU : finrank (ZMod 2) U = 8 := by rw [hU, finrank_sup_of_inf_eq_bot i₃, h4, f₃]
  have hinf : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      commSpace (τ₃ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by rw [hV]; exact i₃
  have hdim := finrank_commSpace_mul_eq hinf w₃
  rw [hV, h4, f₃] at hdim
  have e : t * τ₃ = τ₁ * τ₂ := by
    rw [hτ₃, show t * (t * τ₁ * τ₂) = (t * t) * τ₁ * τ₂ by group, htt, one_mul]
  have hle1 := commSpace_mul_le t τ₃
  rw [hV] at hle1
  have hU1 : commSpace ((t * τ₃ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = U :=
    Submodule.eq_of_le_of_finrank_le hle1 (by omega)
  have hle2 := commSpace_mul_le τ₁ τ₂
  rw [← e, hU1] at hle2
  have d12 := Submodule.finrank_sup_add_finrank_inf_eq
    (commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)) (commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have hU2 : U = commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
      commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Submodule.eq_of_le_of_finrank_le hle2 (by omega)
  have hVU : V ≤ U := le_sup_left
  constructor
  · have hle : V ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ U :=
      sup_le hVU (hU2 ▸ le_sup_left)
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_sup_of_inf_eq_bot i₁]; omega)
  · have hle : V ⊔ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ U :=
      sup_le hVU (hU2 ▸ le_sup_right)
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_sup_of_inf_eq_bot i₂]; omega)

theorem fix_iff_mem_orthogonal {V : Submodule (ZMod 2) S.Qt} {x : S.O} {w : S.Qt}
    (hw : w ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin V) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w ↔ w ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin
      (V ⊔ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hfix := fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate x.2
  have h := S8.perp_sup (q := S.q) V (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt))
  simp only [S2.perp] at h
  rw [h, Submodule.mem_inf, ← hfix, mem_fixSpace]
  exact ⟨fun h' => ⟨hw, h'⟩, fun h' => h'.2⟩

theorem exists_apply_sub_eq_of_mem {V : Submodule (ZMod 2) S.Qt} {x : S.O}
    (hinf : V ⊓ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) {v : S.Qt}
    (hv : v ∈ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ∃ w ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin V,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = v := by
  set W := LinearMap.BilinForm.orthogonal S.q.polarBilin V with hW
  set A := commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) with hA
  have hnd := S.q_nondegenerate
  have hperp : ∀ X : Submodule (ZMod 2) S.Qt,
      finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin X) +
        finrank (ZMod 2) X = finrank (ZMod 2) S.Qt := by
    intro X
    have := LinearMap.BilinForm.finrank_orthogonal hnd X
    have := Submodule.finrank_le X
    omega
  have d1 := S2.finrank_map_sub_one_add (x : S.Qt ≃ₗ[ZMod 2] S.Qt) W
  have hle : W ⊓ fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin (V ⊔ A) := fun w hw =>
    (fix_iff_mem_orthogonal hw.1).mp (mem_fixSpace.mp hw.2)
  have d2 := Submodule.finrank_mono hle
  have d3 := hperp (V ⊔ A)
  have d4 := hperp V
  rw [← hW] at d4
  have d5 := finrank_sup_of_inf_eq_bot hinf
  have hmap : W.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤ A := by
    rintro _ ⟨w, -, rfl⟩
    exact sub_mem_commSpace _ w
  have heq : W.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) = A :=
    Submodule.eq_of_le_of_finrank_le hmap (by omega)
  rw [← heq] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  exact ⟨w, hw, by simp⟩

theorem apply_sub_eq_add {t τ₁ τ₂ : S.O} {W : Submodule (ZMod 2) S.Qt}
    (htW : ∀ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w)
    (h₁W : ∀ w ∈ W, (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (h₂W : commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ W)
    (h₁₂ : ∀ v ∈ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt), (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    {w : S.Qt} (hw : w ∈ W) :
    ((t * τ₁ * τ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
      ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) + ((τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
  set d := (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w with hd
  have hdC : d ∈ commSpace (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) := sub_mem_commSpace _ w
  have e2 : (τ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + d := by rw [hd]; abel
  rw [coe_mul_apply, coe_mul_apply, e2, map_add, h₁₂ d hdC, map_add, htW _ (h₁W w hw),
    htW d (h₂W hdC)]
  abel

end CFSG.LargeExtraspecial.S9.RB
