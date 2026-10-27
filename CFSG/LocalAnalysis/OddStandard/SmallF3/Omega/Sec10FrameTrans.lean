module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameImg

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def conj (F : PspFrame L) (a : P45) (ha : a ∈ QP45.originalSubgroup) : PspFrame L where
  φ := (MulAut.conj a).toMonoidHom.comp F.φ
  mem_A y := by
    have h1 : a ∈ QA45.originalSubgroup := QP45_le_QA45 ha
    exact QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.mul_mem h1 (F.mem_A y))
      (QA45.originalSubgroup.inv_mem h1)
  ker_iff y := by
    rw [← F.ker_iff]
    simp [MulAut.conj_apply]
  mem_P y hy := QP45.originalSubgroup.mul_mem
    (QP45.originalSubgroup.mul_mem ha (F.mem_P y hy)) (QP45.originalSubgroup.inv_mem ha)
  inj_L y y' hy hy' h := F.inj_L y y' hy hy' (by simpa [MulAut.conj_apply] using h)
  surj_P p hp := by
    obtain ⟨y, hy, h⟩ := F.surj_P (a⁻¹ * p * a)
      (QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.mul_mem
        (QP45.originalSubgroup.inv_mem ha) hp) ha)
    refine ⟨y, hy, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, h]
    group

variable (F : PspFrame L) {a : P45} {ha : a ∈ QP45.originalSubgroup} {X Y : Subgroup G}

theorem conj_psi (l : ↥L) : (F.conj a ha).ψ l = a * F.ψ l * a⁻¹ := rfl

theorem mem_img_conj {p : P45} : p ∈ (F.conj a ha).img X ↔ a⁻¹ * p * a ∈ F.img X := by
  rw [mem_img, mem_img]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, by rw [conj_psi]; group⟩
  · rintro ⟨l, hl, h⟩
    refine ⟨l, hl, ?_⟩
    rw [conj_psi, h]
    group

theorem orderOf_psi (l : ↥L) : orderOf (F.ψ l) = orderOf (l : G) := by
  rw [orderOf_injective F.ψ F.ψ_injective l, Subgroup.orderOf_coe]

@[expose] def conjL (y : ↥(normalizer (L : Set G))) (l : ↥L) : ↥L :=
  ⟨(y : G) * l * (y : G)⁻¹, (Subgroup.mem_normalizer_iff.1 y.2 (l : G)).1 l.2⟩

theorem psi_conjL (y : ↥(normalizer (L : Set G))) (l : ↥L) :
    F.ψ (conjL y l) = F.φ y * F.ψ l * (F.φ y)⁻¹ := by
  have : (⟨(conjL y l : G), Subgroup.le_normalizer (conjL y l).2⟩ : ↥(normalizer (L : Set G))) =
      y * ⟨(l : G), Subgroup.le_normalizer l.2⟩ * y⁻¹ := rfl
  rw [ψ_apply, this, map_mul, map_mul, map_inv]
  rfl

theorem mem_P_conj (y : ↥(normalizer (L : Set G))) (p : P45) :
    p ∈ QP45.originalSubgroup ↔ F.φ y * p * (F.φ y)⁻¹ ∈ QP45.originalSubgroup := by
  constructor
  · intro hp
    obtain ⟨l, rfl⟩ := F.ψ_surj hp
    rw [← psi_conjL]
    exact F.ψ_mem _
  · intro hp
    obtain ⟨l, hl⟩ := F.ψ_surj hp
    have h2 := psi_conjL F y⁻¹ l
    have h3 : (F.φ y)⁻¹ * (F.φ y * p * (F.φ y)⁻¹) * F.φ y = p := by group
    rw [← h3, ← hl]
    rw [map_inv, inv_inv] at h2
    rw [← h2]
    exact F.ψ_mem _

theorem img_inf_centralizer_singleton (l : ↥L) :
    F.img (L ⊓ centralizer ({(l : G)} : Set G)) =
      QP45.originalSubgroup ⊓ centralizer ({F.ψ l} : Set P45) := by
  ext p
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_img]
  constructor
  · rintro ⟨l', hl', rfl⟩
    refine ⟨F.ψ_mem l', ?_⟩
    have h := (Subgroup.mem_inf.1 hl').2
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    have h2 : l' * l = l * l' := Subtype.ext h
    rw [← map_mul, ← map_mul, h2]
  · rintro ⟨hp, hc⟩
    obtain ⟨l', rfl⟩ := F.ψ_surj hp
    refine ⟨l', Subgroup.mem_inf.2 ⟨l'.2, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : l' * l = l * l' := F.ψ_injective (by rw [map_mul, map_mul]; exact hc)
    exact congrArg Subtype.val h2

theorem img_inf_normalizer (hX : X ≤ L) :
    F.img (L ⊓ normalizer (X : Set G)) =
      QP45.originalSubgroup ⊓ normalizer (F.img X : Set P45) := by
  have key : ∀ l : ↥L, (l : G) ∈ normalizer (X : Set G) ↔
      F.ψ l ∈ normalizer (F.img X : Set P45) := by
    intro l
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    have hc : ∀ x : ↥L, (l : G) * x * (l : G)⁻¹ = ((l * x * l⁻¹ : ↥L) : G) := fun x => rfl
    have hψ : ∀ x : ↥L, F.ψ (l * x * l⁻¹) = F.ψ l * F.ψ x * (F.ψ l)⁻¹ := fun x => by
      rw [map_mul, map_mul, map_inv]
    constructor
    · intro h p
      constructor
      · intro hp
        obtain ⟨x, hx, rfl⟩ := mem_img.1 hp
        have h1 := (h (x : G)).1 hx
        rw [hc] at h1
        have h2 := (psi_mem_img (F := F)).2 h1
        rwa [hψ] at h2
      · intro hp
        have hpP : p ∈ QP45.originalSubgroup := by
          have h0 := QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.mul_mem
            (QP45.originalSubgroup.inv_mem (F.ψ_mem l)) (img_le_P X hp)) (F.ψ_mem l)
          have h3 : (F.ψ l)⁻¹ * (F.ψ l * p * (F.ψ l)⁻¹) * F.ψ l = p := by group
          rwa [h3] at h0
        obtain ⟨x, rfl⟩ := F.ψ_surj hpP
        rw [← hψ] at hp
        have h1 := (psi_mem_img (F := F)).1 hp
        rw [← hc] at h1
        exact (psi_mem_img (F := F)).2 ((h (x : G)).2 h1)
    · intro h' x
      constructor
      · intro hx
        have h1 := (h' (F.ψ ⟨x, hX hx⟩)).1 ((psi_mem_img (F := F)).2 hx)
        rw [← hψ] at h1
        exact (psi_mem_img (F := F)).1 h1
      · intro hx
        have hxL : x ∈ L := by
          have h4 : x = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * l := by group
          rw [h4]
          exact L.mul_mem (L.mul_mem (L.inv_mem l.2) (hX hx)) l.2
        have h1 : ((l * ⟨x, hxL⟩ * l⁻¹ : ↥L) : G) ∈ X := hx
        have h2 := (psi_mem_img (F := F)).2 h1
        rw [hψ] at h2
        exact (psi_mem_img (F := F)).1 ((h' _).2 h2)
  ext p
  rw [Subgroup.mem_inf, mem_img]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨F.ψ_mem l, (key l).1 (Subgroup.mem_inf.1 hl).2⟩
  · rintro ⟨hp, hn⟩
    obtain ⟨l, rfl⟩ := F.ψ_surj hp
    exact ⟨l, Subgroup.mem_inf.2 ⟨l.2, (key l).2 hn⟩, rfl⟩

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
