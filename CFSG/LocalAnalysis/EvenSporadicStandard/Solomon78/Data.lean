module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

@[expose] def PerfectInvolutions (Y : Type) [Group Y] : Prop :=
  ∀ w : Y, orderOf w = 2 → w ∈ ⁅centralizer ({w} : Set Y), centralizer ({w} : Set Y)⁆

@[expose] def CenterInvolutions (Y : Type) [Group Y] : Prop :=
  ∀ a z : Y, orderOf a = 2 → z * z = 1 → z * a = a * z →
    (∀ y : Y, y * a = a * y → z * y = y * z) → z = 1 ∨ z = a

theorem PerfectInvolutions.subgroup {G Y : Type} [Group G] [Group Y] {L : Subgroup G}
    (e : L ≃* Y) (h : PerfectInvolutions Y) :
    ∀ w ∈ L, orderOf w = 2 →
      w ∈ ⁅L ⊓ centralizer ({w} : Set G), L ⊓ centralizer ({w} : Set G)⁆ := by
  intro w hw hw2
  set w' : L := ⟨w, hw⟩ with hw'
  have hw'2 : orderOf (e w') = 2 := by
    have := orderOf_injective e.toMonoidHom e.injective w'
    rw [hw', Subgroup.orderOf_mk, hw2] at this
    exact this
  have h1 := h (e w') hw'2
  set φ : Y →* G := L.subtype.comp e.symm.toMonoidHom with hφ
  have hφw : φ (e w') = w := by
    show ((e.symm (e w') : L) : G) = w
    rw [MulEquiv.symm_apply_apply]
  have hmap : (centralizer ({e w'} : Set Y)).map φ ≤ L ⊓ centralizer ({w} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(e.symm y).2, mem_centralizer_singleton_iff.2 ?_⟩
    have hy' : y * e w' = e w' * y := mem_centralizer_singleton_iff.1 hy
    have := congrArg φ hy'
    rwa [map_mul, map_mul, hφw] at this
  have h2 := Subgroup.mem_map_of_mem φ h1
  rw [hφw, map_commutator] at h2
  exact commutator_mono hmap hmap h2

theorem CenterInvolutions.subgroup {G Y : Type} [Group G] [Group Y] {L : Subgroup G}
    (e : L ≃* Y) (h : CenterInvolutions Y) : Sol78CenterInv L := by
  intro a ha ha2 z hz hzz hza hzc
  have ha' : orderOf (e ⟨a, ha⟩) = 2 := by
    have := orderOf_injective e.toMonoidHom e.injective ⟨a, ha⟩
    rw [Subgroup.orderOf_mk, ha2] at this
    exact this
  have hzz' : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hz⟩ : L) * ⟨z, hz⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hza' : e ⟨z, hz⟩ * e ⟨a, ha⟩ = e ⟨a, ha⟩ * e ⟨z, hz⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hza)
  have hzc' : ∀ y : Y, y * e ⟨a, ha⟩ = e ⟨a, ha⟩ * y → e ⟨z, hz⟩ * y = y * e ⟨z, hz⟩ := by
    intro y hy
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul] at hy ⊢
    have := hzc y' y'.2 (by
      have := e.injective hy
      exact congrArg Subtype.val this)
    exact congrArg e (Subtype.ext this)
  rcases h _ _ ha' hzz' hza' hzc' with h1 | h1
  · left
    have := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · right
    exact congrArg Subtype.val (e.injective h1)

end CFSG.EvenSporadicStandard.Solomon78
