module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameTrans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L) {X Y : Subgroup G}

theorem isPGroup_img_iff (hX : X ≤ L) : IsPGroup 2 (F.img X) ↔ IsPGroup 2 X :=
  ⟨fun h => h.of_equiv (F.imgEquiv hX).symm, fun h => h.of_equiv (F.imgEquiv hX)⟩

theorem isSylow2Of_img (hY : Y ≤ L) (h : IsSylow2Of X Y) :
    IsSylow2Of (F.img X) (F.img Y) := by
  obtain ⟨hXY, hp, hnd⟩ := h
  refine ⟨img_mono hXY, (F.isPGroup_img_iff (hXY.trans hY)).2 hp, ?_⟩
  rw [relIndex_img hXY hY]
  exact hnd

theorem img_conjugate_psi (g : ↥L) :
    F.img (CFSG.conjugate X (g : G)) = CFSG.conjugate (F.img X) (F.ψ g) := by
  have key : ∀ l : ↥L, F.ψ l ∈ F.img (CFSG.conjugate X (g : G)) ↔
      F.ψ l ∈ CFSG.conjugate (F.img X) (F.ψ g) := by
    intro l
    rw [psi_mem_img, mem_conjugate_iff', mem_conjugate_iff']
    have h1 : (g : G) * (l : G) * (g : G)⁻¹ = ((g * l * g⁻¹ : ↥L) : G) := rfl
    rw [h1, ← psi_mem_img (F := F), map_mul, map_mul, map_inv]
  ext p
  constructor
  · intro hp
    obtain ⟨l, -, rfl⟩ := mem_img.1 hp
    exact (key l).1 hp
  · intro hp
    have hP : p ∈ QP45.originalSubgroup := by
      rw [mem_conjugate_iff'] at hp
      have h0 := QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.mul_mem
        (QP45.originalSubgroup.inv_mem (F.ψ_mem g)) (img_le_P X hp)) (F.ψ_mem g)
      have h3 : (F.ψ g)⁻¹ * (F.ψ g * p * (F.ψ g)⁻¹) * F.ψ g = p := by group
      rwa [h3] at h0
    obtain ⟨l, rfl⟩ := F.ψ_surj hP
    exact (key l).2 hp

theorem img_conjugate_phi (y : ↥(normalizer (L : Set G))) :
    F.img (CFSG.conjugate X (y : G)) = CFSG.conjugate (F.img X) (F.φ y) := by
  have key : ∀ l : ↥L, F.ψ l ∈ F.img (CFSG.conjugate X (y : G)) ↔
      F.ψ l ∈ CFSG.conjugate (F.img X) (F.φ y) := by
    intro l
    rw [psi_mem_img, mem_conjugate_iff', mem_conjugate_iff']
    have h1 : (y : G) * (l : G) * (y : G)⁻¹ = ((conjL y l : ↥L) : G) := rfl
    rw [h1, ← psi_mem_img (F := F), psi_conjL]
  ext p
  constructor
  · intro hp
    obtain ⟨l, -, rfl⟩ := mem_img.1 hp
    exact (key l).1 hp
  · intro hp
    have hP : p ∈ QP45.originalSubgroup := by
      rw [mem_conjugate_iff'] at hp
      exact (F.mem_P_conj y p).2 (img_le_P X hp)
    obtain ⟨l, rfl⟩ := F.ψ_surj hP
    exact (key l).2 hp

theorem oTwoRes_le (X : Subgroup G) : oTwoRes X ≤ X :=
  (Subgroup.closure_le X).2 fun _ hx => hx.1

theorem img_oTwoRes (hX : X ≤ L) : F.img (oTwoRes X) = oTwoRes (F.img X) := by
  have hle : oTwoRes (F.img X) ≤ QP45.originalSubgroup :=
    (oTwoRes_le _).trans (img_le_P X)
  apply le_antisymm
  · have h1 : oTwoRes X ≤ F.pre (oTwoRes (F.img X)) := by
      rw [oTwoRes, Subgroup.closure_le]
      rintro x ⟨hx, hodd⟩
      refine mem_pre.2 ⟨hX hx, Subgroup.subset_closure ⟨?_, ?_⟩⟩
      · exact (psi_mem_img (F := F) (l := ⟨x, hX hx⟩)).2 hx
      · rwa [orderOf_psi F ⟨x, hX hx⟩]
    calc F.img (oTwoRes X) ≤ F.img (F.pre (oTwoRes (F.img X))) := img_mono h1
      _ = oTwoRes (F.img X) := img_pre hle
  · rw [oTwoRes, Subgroup.closure_le]
    rintro p ⟨hp, hodd⟩
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
    refine mem_img.2 ⟨l, Subgroup.subset_closure ⟨hl, ?_⟩, rfl⟩
    rwa [orderOf_psi F l] at hodd

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
