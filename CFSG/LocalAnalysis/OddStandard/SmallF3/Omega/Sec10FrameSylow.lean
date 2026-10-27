module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FramePocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelUtil
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11Y

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

theorem card_QT0 : Nat.card QT0.originalSubgroup = 64 :=
  (card_group QT0 QT0_valid.1).trans QT0_valid.2

theorem isSylow2Of_QT0 :
    IsSylow2Of QT0.originalSubgroup QP45.originalSubgroup := by
  have h64 := card_QT0
  refine ⟨X11.QT0_le, IsPGroup.of_card (n := 6) (by rw [h64]; norm_num), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := QT0.originalSubgroup) (K := QP45.originalSubgroup)
  rw [inf_eq_left.2 X11.QT0_le, h64, card_QP45] at h
  rintro ⟨k, hk⟩
  omega

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L) {X : Subgroup G}

include F in
theorem exists_frame_syl
    {P' : Subgroup G} (hP : IsSylow2Of P' L) :
    ∃ F' : PspFrame L, F'.img P' = QT0.originalSubgroup := by
  have hS : IsSylow2Of (F.img P') QP45.originalSubgroup := by
    have := F.isSylow2Of_img le_rfl hP
    rwa [img_L] at this
  obtain ⟨a, ha, hmem⟩ := IsSylow2Of.exists_conj_mem hS isSylow2Of_QT0
  refine ⟨F.conj a ha, ?_⟩
  ext p
  rw [mem_img_conj, ← hmem]

theorem img_centerIn (hX : X ≤ L) : F.img (centerIn X) = centerIn (F.img X) := by
  ext p
  constructor
  · intro hp
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
    obtain ⟨hlX, hc⟩ := mem_centerIn_iff.1 hl
    refine mem_centerIn_iff.2 ⟨mem_img.2 ⟨l, hlX, rfl⟩, fun q hq => ?_⟩
    obtain ⟨l', hl', rfl⟩ := mem_img.1 hq
    rw [← map_mul, ← map_mul]
    exact congrArg F.ψ (Subtype.ext (hc _ hl'))
  · intro hp
    obtain ⟨hpX, hc⟩ := mem_centerIn_iff.1 hp
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hpX
    refine mem_img.2 ⟨l, mem_centerIn_iff.2 ⟨hl, fun y hy => ?_⟩, rfl⟩
    have h := hc (F.ψ ⟨y, hX hy⟩) (mem_img.2 ⟨⟨y, hX hy⟩, hy, rfl⟩)
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (F.ψ_injective h)

theorem card_centerIn_img (hX : X ≤ L) :
    Nat.card (centerIn (F.img X)) = Nat.card (centerIn X) := by
  rw [← F.img_centerIn hX]
  exact F.card_img ((centerIn_le X).trans hX)

theorem comm_phi_psi_iff (y : ↥(normalizer (L : Set G))) (l : ↥L) :
    F.φ y * F.ψ l = F.ψ l * F.φ y ↔ (y : G) * l = l * (y : G) := by
  have h := F.psi_conjL y l
  constructor
  · intro hc
    have h1 : conjL y l = l := F.ψ_injective (by rw [h, hc, mul_inv_cancel_right])
    have h2 : (y : G) * l * (y : G)⁻¹ = l := congrArg Subtype.val h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  · intro hc
    have h1 : conjL y l = l := Subtype.ext (mul_inv_eq_iff_eq_mul.2 hc)
    rw [h1] at h
    exact mul_inv_eq_iff_eq_mul.1 h.symm

theorem mem_sup_of_phi_eq_psi (y : ↥(normalizer (L : Set G))) (l : ↥L) (hl : (l : G) ∈ X)
    (h : F.φ y = F.ψ l) : (y : G) ∈ centralizer (L : Set G) ⊔ X := by
  have hker : F.φ (y * (⟨(l : G), Subgroup.le_normalizer l.2⟩ :
      ↥(normalizer (L : Set G)))⁻¹) = 1 := by
    rw [map_mul, map_inv, h, ← F.ψ_apply l, mul_inv_cancel]
  have hc : (y : G) * (l : G)⁻¹ ∈ centralizer (L : Set G) := (F.ker_iff _).1 hker
  have h2 : (y : G) = ((y : G) * (l : G)⁻¹) * (l : G) := by group
  rw [h2]
  exact Subgroup.mul_mem_sup hc hl

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
