module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCBInvolutionTrichotomy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module QuadraticMap
open scoped commutatorElement

namespace TICommutingCenters

open CFSG.RankThree.Literature.FSmith InvolutionTrichotomy

variable {G : Type*} [Group G]

theorem center_map_equiv {K H : Type*} [Group K] [Group H] (e : K ≃* H) :
    (center K).map e.toMonoidHom = center H := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

section Image

variable {K : Type*} [Group K] [Module (ZMod 2) (Additive (Abelianization K))]

@[expose] noncomputable def img (A : Subgroup K) :
    Submodule (ZMod 2) (Additive (Abelianization K)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (A.map Abelianization.of))

theorem mem_img {A : Subgroup K} {v : Additive (Abelianization K)} :
    v ∈ img A ↔ ∃ a ∈ A, Additive.ofMul (Abelianization.of a) = v := by
  rw [img, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, Subgroup.mem_map]
  rfl

theorem ofMul_mem_img_iff (hK : IsExtraspecialPGroup 2 K) {A : Subgroup K} (hA : center K ≤ A)
    (y : K) : Additive.ofMul (Abelianization.of y) ∈ img A ↔ y ∈ A := by
  rw [mem_img]
  constructor
  · rintro ⟨a, ha, h⟩
    have h' : Abelianization.of a = Abelianization.of y := Additive.ofMul.injective h
    rw [MonoidHom.eq_iff, Abelianization.ker_of, hK.2.1] at h'
    have := mul_mem ha (inv_mem (hA h'))
    simpa using this
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem preim_img (hK : IsExtraspecialPGroup 2 K) {A : Subgroup K} (hA : center K ≤ A) :
    preim (img A) = A := by
  ext y
  rw [mem_preim]
  exact ofMul_mem_img_iff hK hA y

theorem finrank_eq [Finite K] (hK : IsExtraspecialPGroup 2 K) {w : ℕ}
    (hw : Nat.card K = 2 ^ (1 + 2 * w)) :
    finrank (ZMod 2) (Additive (Abelianization K)) = 2 * w := by
  have h := card_preim hK (⊤ : Submodule (ZMod 2) (Additive (Abelianization K)))
  have htop : preim (⊤ : Submodule (ZMod 2) (Additive (Abelianization K))) = ⊤ := by
    ext y
    simp [mem_preim]
  rw [htop, Subgroup.card_top, hw, finrank_top, pow_add, pow_one, mul_comm] at h
  exact (Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right (by norm_num) h)).symm

end Image

end TICommutingCenters

end CFSG.LocalAnalysis.GorensteinLyons
