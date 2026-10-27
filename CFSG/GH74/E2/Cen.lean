module

public import CFSG.GH74.E2.Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.E2

open Subgroup

section Basic

variable {G : Type*} [Group G]

abbrev Cen (t : G) : Subgroup G := centralizer ({t} : Set G)

theorem mem_Cen {t x : G} : x ∈ Cen t ↔ t * x = x * t := by
  rw [mem_centralizer_iff]
  simp

theorem mem_Cen' {t x : G} : x ∈ Cen t ↔ x * t = t * x := by
  rw [mem_Cen]
  exact eq_comm

@[expose] def Qt (t : G) : Subgroup G := (CFSG.pCore 2 ↥(Cen t)).map (Cen t).subtype

theorem Qt_le_Cen (t : G) : Qt t ≤ Cen t := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_Qt {t x : G} :
    x ∈ Qt t ↔ ∃ h : x ∈ Cen t, (⟨x, h⟩ : Cen t) ∈ CFSG.pCore 2 ↥(Cen t) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem Qt_isPGroup (t : G) : IsPGroup 2 (Qt t) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(Cen t))).map (Cen t).subtype

theorem Qt_conj_mem (t : G) {c : G} (hc : c ∈ Cen t) {q : G} (hq : q ∈ Qt t) :
    c * q * c⁻¹ ∈ Qt t := by
  obtain ⟨hqC, hq'⟩ := mem_Qt.1 hq
  refine mem_Qt.2 ⟨?_, ?_⟩
  · exact mul_mem (mul_mem hc hqC) (inv_mem hc)
  · have := (CFSG.pCore_normal (p := 2) (G := ↥(Cen t))).conj_mem _ hq' ⟨c, hc⟩
    exact this

theorem t_mem_Qt [Finite G] {t : G} (ht : orderOf t = 2) : t ∈ Qt t := by
  have htC : t ∈ Cen t := mem_Cen.2 rfl
  refine mem_Qt.2 ⟨htC, ?_⟩
  let τ : Cen t := ⟨t, htC⟩
  have hτ : orderOf τ = 2 := by rw [← Subgroup.orderOf_coe]; exact ht
  have hcentral : ∀ g : Cen t, g * τ = τ * g := fun g => Subtype.ext (mem_Cen.1 g.2).symm
  let K : Subgroup (Cen t) := Subgroup.zpowers τ
  have hKnormal : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * τ ^ k * g⁻¹ = τ ^ k := by
      have hc : Commute g τ := hcentral g
      rw [(hc.zpow_right k).eq]
      group
    rw [this]
    exact ⟨k, rfl⟩
  have hKp : IsPGroup 2 K := by
    have hcard : Nat.card K = 2 ^ 1 := by
      rw [Nat.card_zpowers, hτ]; simp
    exact IsPGroup.of_card hcard
  have : K ≤ CFSG.pCore 2 ↥(Cen t) := le_sSup ⟨hKnormal, hKp⟩
  exact this (Subgroup.mem_zpowers τ)

end Basic

section Conj

variable {G : Type*} [Group G]

@[expose] def conjCen (t g : G) : Cen t ≃* Cen (g * t * g⁻¹) where
  toFun x := ⟨g * x * g⁻¹, by
    rw [mem_Cen]
    have := mem_Cen.1 x.2
    calc g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * t * g⁻¹) := by group⟩
  invFun y := ⟨g⁻¹ * y * g, by
    rw [mem_Cen]
    have := mem_Cen.1 y.2
    have h2 : (g * t * g⁻¹) * y = y * (g * t * g⁻¹) := this
    calc t * (g⁻¹ * y * g) = g⁻¹ * ((g * t * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * t * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * y * g * t := by group⟩
  left_inv x := Subtype.ext (by
    show g⁻¹ * (g * (x : G) * g⁻¹) * g = x
    group)
  right_inv y := Subtype.ext (by
    show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y
    group)
  map_mul' x y := Subtype.ext (by
    show g * ((x : G) * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹)
    group)

theorem coe_conjCen (t g : G) (x : Cen t) : ((conjCen t g x : Cen (g * t * g⁻¹)) : G) = g * x * g⁻¹ :=
  rfl

theorem coe_conjCen_symm (t g : G) (y : Cen (g * t * g⁻¹)) :
    (((conjCen t g).symm y : Cen t) : G) = g⁻¹ * y * g :=
  rfl

theorem mem_Qt_conj (t g x : G) : x ∈ Qt (g * t * g⁻¹) ↔ g⁻¹ * x * g ∈ Qt t := by
  have hmap := CFSG.pCore_map_iso 2 (conjCen t g)
  constructor
  · intro hx
    obtain ⟨hxC, hx'⟩ := mem_Qt.1 hx
    have hyC : g⁻¹ * x * g ∈ Cen t := by
      have h1 := ((conjCen t g).symm ⟨x, hxC⟩).2
      rwa [coe_conjCen_symm] at h1
    refine mem_Qt.2 ⟨hyC, ?_⟩
    rw [← hmap] at hx'
    obtain ⟨z, hz, hzx⟩ := hx'
    have hzx' : ((conjCen t g z : Cen (g * t * g⁻¹)) : G) = x := congrArg Subtype.val hzx
    rw [coe_conjCen] at hzx'
    have hz2 : z = ⟨g⁻¹ * x * g, hyC⟩ := by
      apply Subtype.ext
      have : (z : G) = g⁻¹ * x * g := by
        rw [← hzx']
        group
      exact this
    rw [← hz2]
    exact hz
  · intro hx
    obtain ⟨hyC, hy⟩ := mem_Qt.1 hx
    have hxC : x ∈ Cen (g * t * g⁻¹) := by
      have h1 := (conjCen t g ⟨g⁻¹ * x * g, hyC⟩).2
      rw [coe_conjCen] at h1
      have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [h2] at h1
    refine mem_Qt.2 ⟨hxC, ?_⟩
    rw [← hmap]
    refine ⟨⟨g⁻¹ * x * g, hyC⟩, hy, ?_⟩
    apply Subtype.ext
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

end Conj

section Even

variable {G : Type} [Group G] [Finite G]

theorem Hyp.pPrimeCore_cen_bot (hH : Hyp G) {x : G} (hx : orderOf x = 2) :
    CFSG.pPrimeCore 2 ↥(Cen x) = ⊥ :=
  hH.restrictedEven.1.2.1 x hx

theorem centralizer_Qt_le {t : G} (hcore : CFSG.pPrimeCore 2 ↥(Cen t) = ⊥)
    (hlayer : CFSG.layer ↥(Cen t) = ⊥) {c : G} (hc : c ∈ Cen t)
    (h : ∀ q ∈ Qt t, c * q = q * c) : c ∈ Qt t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot (↥(Cen t)) 2 hcore
    hlayer
  have h1 : (⟨c, hc⟩ : Cen t) ∈ Subgroup.centralizer (CFSG.pCore 2 ↥(Cen t) : Set (Cen t)) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hyQ : (y : G) ∈ Qt t := ⟨y, hy, rfl⟩
    exact Subtype.ext (h y hyQ).symm
  exact (mem_Qt.2 ⟨hc, hchar h1⟩)

end Even

end CFSG.GH74.E2
