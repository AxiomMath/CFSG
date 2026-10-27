module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup

variable {M : Type*} [Group M]

theorem map_centralizer_mulAut (ι : M ≃* M) (H : Subgroup M) :
    (centralizer (H : Set M)).map ι.toMonoidHom =
      centralizer ((H.map ι.toMonoidHom : Subgroup M) : Set M) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    have h1 := h y hy
    apply ι.symm.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.symm_apply_apply]
    exact h1
  · intro h y hy
    have h1 := h (ι y) ⟨y, hy, rfl⟩
    apply ι.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h1

theorem exists_map_inf_centralizer_eq [Finite M] {p : ℕ} [Fact p.Prime] (S : Sylow p M)
    (ι : M ≃* M) : ∃ d : M,
      ((S : Subgroup M) ⊓ centralizer ((S : Subgroup M) : Set M)).map ι.toMonoidHom =
        ((S : Subgroup M) ⊓ centralizer ((S : Subgroup M) : Set M)).map
          (MulAut.conj d).toMonoidHom := by
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq M S (ι • S)
  have hι : ((ι • S : Sylow p M) : Subgroup M) = (S : Subgroup M).map ι.toMonoidHom := by
    ext x
    rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  have hdS : ((d • S : Sylow p M) : Subgroup M) =
      (S : Subgroup M).map (MulAut.conj d).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  have h1 : (S : Subgroup M).map ι.toMonoidHom =
      (S : Subgroup M).map (MulAut.conj d).toMonoidHom := by
    rw [← hι, ← hdS, hd]
  refine ⟨d, ?_⟩
  rw [map_inf_eq _ _ _ ι.injective, map_inf_eq _ _ _ (MulAut.conj d).injective,
    map_centralizer_mulAut, map_centralizer_mulAut, h1]

theorem map_mulEquiv_sup_map_conj_eq {X : Type*} [Group X] (φ : M →* X) (ι : M ≃* M)
    (Z : Subgroup M) (n d : M) (hZ : Z.map ι.toMonoidHom = Z.map (MulAut.conj d).toMonoidHom) :
    ((Z ⊔ Z.map (MulAut.conj n).toMonoidHom).map ι.toMonoidHom).map φ =
      (Z.map φ).map (MulAut.conj (φ d)).toMonoidHom ⊔
        (Z.map φ).map (MulAut.conj (φ (ι n * d))).toMonoidHom := by
  have hconj : ∀ g : M, ∀ H : Subgroup M,
      (H.map (MulAut.conj g).toMonoidHom).map φ =
        (H.map φ).map (MulAut.conj (φ g)).toMonoidHom := by
    intro g H
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨φ h, ⟨h, hh, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨g * h * g⁻¹, ⟨h, hh, rfl⟩, by simp⟩
  have hιconj : (Z.map (MulAut.conj n).toMonoidHom).map ι.toMonoidHom =
      (Z.map ι.toMonoidHom).map (MulAut.conj (ι n)).toMonoidHom := by
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨ι h, ⟨h, hh, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨n * h * n⁻¹, ⟨h, hh, rfl⟩, by simp⟩
  have hcomp : ∀ a b : M, ∀ H : Subgroup M,
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        H.map (MulAut.conj (a * b)).toMonoidHom := by
    intro a b H
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_sup, Subgroup.map_sup, hιconj, hZ, hcomp, hconj, hconj]

theorem forall_normal_isPGroup_eq_bot_of_inf_centralizer_le [Finite M] {p : ℕ} [Fact p.Prime]
    (S : Sylow p M) {J : Subgroup M}
    (hZJ : (S : Subgroup M) ⊓ centralizer ((S : Subgroup M) : Set M) ≤ J)
    (hJ : IsSimpleGroup J) (hJp : ¬ IsPGroup p J) :
    ∀ N : Subgroup M, N.Normal → IsPGroup p N → N = ⊥ := by
  intro N hN hNp
  by_contra hne
  have hNS : N ≤ S := hNp.le_sylow_of_normal S
  have hnil : Group.IsNilpotent (S : Subgroup M) := S.isPGroup'.isNilpotent
  have hN' : (N.subgroupOf (S : Subgroup M)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    simpa using hN.conj_mem _ hx (g : M)
  have hN'ne : N.subgroupOf (S : Subgroup M) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNS hx⟩ : (S : Subgroup M)) ∈ N.subgroupOf (S : Subgroup M) :=
      mem_subgroupOf.2 hx
    rw [h, mem_bot] at hx'
    exact (mem_bot).2 (congrArg Subtype.val hx')
  obtain ⟨⟨x, hx⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne)
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  obtain ⟨hxN, hxZ⟩ := mem_inf.1 hx
  have hxJ : ((x : (S : Subgroup M)) : M) ∈ J := hZJ (mem_inf.2 ⟨(x : (S : Subgroup M)).2,
    mem_centralizer_iff.2 fun y hy => by
      have := mem_center_iff.1 hxZ ⟨y, hy⟩
      have h2 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h2
      exact h2⟩)
  have hNJ : (N.subgroupOf J).Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    simpa using hN.conj_mem _ hy (g : M)
  rcases hJ.eq_bot_or_eq_top_of_normal (N.subgroupOf J) with h | h
  · apply hx1
    have hxNJ : (⟨((x : (S : Subgroup M)) : M), hxJ⟩ : J) ∈ N.subgroupOf J :=
      mem_subgroupOf.2 (mem_subgroupOf.1 hxN)
    rw [h, mem_bot] at hxNJ
    exact Subtype.ext (by simpa using congrArg Subtype.val hxNJ)
  · apply hJp
    have hJN : J ≤ N := fun y hy => by
      have : (⟨y, hy⟩ : J) ∈ N.subgroupOf J := by rw [h]; exact mem_top _
      exact mem_subgroupOf.1 this
    exact hNp.to_le hJN

theorem map_map_conj_eq {X : Type*} [Group X] (φ : M →* X) (g : M) (H : Subgroup M) :
    (H.map (MulAut.conj g).toMonoidHom).map φ = (H.map φ).map (MulAut.conj (φ g)).toMonoidHom := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨φ h, ⟨h, hh, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨g * h * g⁻¹, ⟨h, hh, rfl⟩, by simp⟩

theorem map_conj_map_conj (a b : M) (H : Subgroup M) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_map_mulEquiv_conj {A : Type*} [Group A] (E : A ≃* M) (ι : M ≃* M) (H : Subgroup A) :
    (H.map E.toMonoidHom).map ι.toMonoidHom =
      (H.map ((E.trans ι).trans E.symm).toMonoidHom).map E.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

end CFSG.SeitzReduction.E7Pilot
