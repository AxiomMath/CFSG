module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

open scoped Pointwise

theorem characteristic_of_normal_of_map_mulEquiv {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (F : Subgroup G → Subgroup G)
    (hF : ∀ (φ : G ≃* G) (S : Subgroup G), (F S).map φ.toMonoidHom = F (S.map φ.toMonoidHom))
    (P : Sylow p G) [(F P).Normal] : (F P).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P
    (Sylow.mapSurjective (f := (φ : G →* G)) φ.surjective P)
  have h := congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_mapSurjective, Subgroup.pointwise_smul_def] at h
  change (F P).map (φ : G →* G) = F P
  have hφ := hF φ P
  simp only [MulEquiv.toMonoidHom_eq_coe] at hφ
  rw [hφ, ← h]
  change F ((P : Subgroup G).map (MulAut.conj g : G →* G)) = F P
  have hc := hF (MulAut.conj g) P
  simp only [MulEquiv.toMonoidHom_eq_coe] at hc
  rw [← hc]
  exact Subgroup.Normal.map_conj_eq _ g
end CFSG
