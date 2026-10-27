module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKill

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

structure SylowModel (ε : Eps) (t : G) (TH E₁ S : Subgroup G) :
    Prop where
  TH_le : TH ≤ S
  E₁_le : E₁ ≤ S
  le_normalizer : S ≤ normalizer (E₁ : Set G)
  pgroup : IsPGroup 2 S
  maximal : ∀ V : Subgroup G, V ≤ normalizer (E₁ : Set G) → IsPGroup 2 V → S ≤ V → V = S
  iso : ∃ e : S ≃* SModel, ∀ s : S, ((s : G) = t ↔ e s = SModel.tM ε) ∧
    ((s : G) ∈ E₁ ↔ e s ∈ SModel.EM)

structure Hyp (ε : Eps) (t : G) (TH E₁ S : Subgroup G) : Prop where
  t_sq : t * t = 1
  TH_le : TH ≤ centralizer ({t} : Set G)
  TH_pgroup : IsPGroup 2 TH
  TH_max : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH
  sylow : SylowModel ε t TH E₁ S

@[expose] def conjEquiv {K : Subgroup G} {x : G} (hx : x ∈ normalizer (K : Set G)) : K ≃* K where
  toFun k := ⟨x * k * x⁻¹, (mem_normalizer_iff.1 hx k).1 k.2⟩
  invFun k := ⟨x⁻¹ * k * x, by
    have := (mem_normalizer_iff.1 (inv_mem hx) k).1 k.2
    simpa using this⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjEquiv_apply {K : Subgroup G} {x : G} (hx : x ∈ normalizer (K : Set G)) (k : K) :
    ((conjEquiv hx k : K) : G) = x * k * x⁻¹ := rfl

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}
  (hH : Hyp ε t TH E₁ S)
include hH

theorem t_mem_TH [Finite G] : t ∈ TH := by
  have hN : t ∈ normalizer (TH : Set G) := by
    refine mem_normalizer_iff.2 fun y => ?_
    constructor
    · intro hy
      have hyt := mem_centralizer_singleton_iff.1 (hH.TH_le hy)
      rw [show t * y * t⁻¹ = y by rw [← hyt, mul_inv_cancel_right]]
      exact hy
    · intro hy
      have hyt : t * y * t⁻¹ * t = t * (t * y * t⁻¹) :=
        mem_centralizer_singleton_iff.1 (hH.TH_le hy)
      have : y = t * y * t⁻¹ := by
        have h2 : t * y = t * (t * y * t⁻¹) := by
          calc t * y = t * y * t⁻¹ * t := by group
            _ = t * (t * y * t⁻¹) := hyt
        exact mul_left_cancel h2
      rwa [this]
  have hsq : t * t ∈ TH := by rw [hH.t_sq]; exact one_mem _
  have hp := isPGroup_sup_zpowers hH.TH_pgroup hN hsq
  have hle : TH ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le hH.TH_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have := hH.TH_max _ hle hp le_sup_left
  rw [← this]
  exact mem_sup_right (mem_zpowers t)

theorem t_mem_S [Finite G] : t ∈ S := hH.sylow.TH_le hH.t_mem_TH

end Hyp

end CFSG.EvenSmallLie.OmegaEight.SpBranch
