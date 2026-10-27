module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

section Transport

variable {A B : Type} [Group A] [Group B]

theorem congr_conj (θ : A ≃* B) (a : A) :
    MulAut.congr θ (MulAut.conj a) = MulAut.conj (θ a) := by
  ext b
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_mem_range_iff (θ : A ≃* B) (φ : MulAut A) :
    MulAut.congr θ φ ∈ (MulAut.conj : B →* MulAut B).range ↔
      φ ∈ (MulAut.conj : A →* MulAut A).range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨θ.symm b, ?_⟩
    apply (MulAut.congr θ).injective
    rw [show (MulAut.conj : A →* MulAut A) (θ.symm b) = MulAut.conj (θ.symm b) from rfl, congr_conj,
      MulEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨a, rfl⟩
    exact ⟨θ a, (congr_conj θ a).symm⟩

theorem congr_map_range (θ : A ≃* B) :
    ((MulAut.conj : A →* MulAut A).range).map (MulAut.congr θ).toMonoidHom =
      (MulAut.conj : B →* MulAut B).range := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨θ a, (congr_conj θ a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨MulAut.conj (θ.symm b), ⟨θ.symm b, rfl⟩, ?_⟩
    show MulAut.congr θ (MulAut.conj (θ.symm b)) = MulAut.conj b
    rw [congr_conj, MulEquiv.apply_symm_apply]

theorem congr_map_sup (θ : A ≃* B) (φ : MulAut A) :
    (((MulAut.conj : A →* MulAut A).range) ⊔ zpowers φ).map (MulAut.congr θ).toMonoidHom =
      (MulAut.conj : B →* MulAut B).range ⊔ zpowers (MulAut.congr θ φ) := by
  rw [Subgroup.map_sup, congr_map_range, MonoidHom.map_zpowers]
  rfl

theorem isPGL2_congr {P : ℕ → Prop} (θ : A ≃* B) (φ : MulAut A)
    (h : IVK.IsPGL2 ↥((MulAut.conj : A →* MulAut A).range ⊔ zpowers φ) P) :
    IVK.IsPGL2 ↥((MulAut.conj : B →* MulAut B).range ⊔ zpowers (MulAut.congr θ φ)) P := by
  obtain ⟨F₀, hF, hfin, hP, ⟨e⟩⟩ := h
  refine ⟨F₀, hF, hfin, hP, ⟨?_⟩⟩
  have hmap := congr_map_sup θ φ
  exact ((MulEquiv.subgroupMap (MulAut.congr θ) _).trans (MulEquiv.subgroupCongr hmap)).symm.trans e

end Transport

section Zpowers

variable {G : Type} [Group G]

theorem mem_zpowers_two {y q : G} (hy2 : orderOf y = 2) (hq : q ∈ zpowers y) : q = 1 ∨ q = y := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hq
  have h := zpow_mod_orderOf y j
  rw [hy2] at h
  push_cast at h
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · left
    rw [← h, h0]
    simp
  · right
    rw [← h, h1]
    simp

end Zpowers

end CFSG.GH74.GLS.C3.Layer1.Bk
