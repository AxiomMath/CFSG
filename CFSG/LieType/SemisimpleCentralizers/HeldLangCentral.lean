module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement

variable {G : Type*} [Group G]

abbrev fixHom (β : G →* G) : Subgroup G := MonoidHom.eqLocus β (MonoidHom.id G)

theorem mem_fixHom {β : G →* G} {x : G} : x ∈ fixHom β ↔ β x = x := Iff.rfl

section Central

variable (β : G →* G) (Z : Subgroup G)

private theorem central_mul_comm (hZ : Z ≤ Subgroup.center G) {z : G} (hz : z ∈ Z) (w : G) :
    z * w = w * z :=
  (Subgroup.mem_center_iff.1 (hZ hz) w).symm

@[expose] def twistedFix (hZ : Z ≤ Subgroup.center G) : Subgroup G where
  carrier := {x | x⁻¹ * β x ∈ Z}
  mul_mem' {x y} hx hy := by
    have h : (x * y)⁻¹ * β (x * y) = (x⁻¹ * β x) * (y⁻¹ * β y) := by
      have hc := central_mul_comm Z hZ hx y⁻¹
      calc (x * y)⁻¹ * β (x * y) = y⁻¹ * (x⁻¹ * β x) * β y := by rw [map_mul]; group
        _ = (x⁻¹ * β x) * y⁻¹ * β y := by rw [← hc]
        _ = (x⁻¹ * β x) * (y⁻¹ * β y) := by group
    show (x * y)⁻¹ * β (x * y) ∈ Z
    rw [h]
    exact Z.mul_mem hx hy
  one_mem' := by simp
  inv_mem' {x} hx := by
    set z := x⁻¹ * β x with hzdef
    have hz : z ∈ Z := hx
    have hcz : x * z⁻¹ = z⁻¹ * x := (central_mul_comm Z hZ (Z.inv_mem hz) x).symm
    have hβx : β x = x * z := (mul_inv_cancel_left x (β x)).symm
    show (x⁻¹)⁻¹ * β x⁻¹ ∈ Z
    have : (x⁻¹)⁻¹ * β x⁻¹ = z⁻¹ := by
      calc (x⁻¹)⁻¹ * β x⁻¹ = x * (β x)⁻¹ := by rw [inv_inv, map_inv]
        _ = x * (x * z)⁻¹ := by rw [← hβx]
        _ = x * z⁻¹ * x⁻¹ := by group
        _ = z⁻¹ * x * x⁻¹ := by rw [hcz]
        _ = z⁻¹ := by group
    rw [this]
    exact Z.inv_mem hz

theorem mem_twistedFix (hZ : Z ≤ Subgroup.center G) {x : G} : x ∈ twistedFix β Z hZ ↔ x⁻¹ * β x ∈ Z := Iff.rfl

theorem fixHom_le_twistedFix (hZ : Z ≤ Subgroup.center G) : fixHom β ≤ twistedFix β Z hZ := fun x hx => by
  have hx' : β x = x := hx
  show x⁻¹ * β x ∈ Z
  rw [hx', inv_mul_cancel]
  exact Z.one_mem

private theorem commutator_mul_central {x y z₁ z₂ : G} (h1 : ∀ w, z₁ * w = w * z₁)
    (h2 : ∀ w, z₂ * w = w * z₂) : ⁅x * z₁, y * z₂⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z₁ * (y * z₂) * (x * z₁)⁻¹ * (y * z₂)⁻¹
      = x * (z₁ * y) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * (y * z₁) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [h1 y]
    _ = x * y * (z₁ * z₂) * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * (z₂ * z₁) * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [h1 z₂]
    _ = x * y * z₂ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z₂) * z₂⁻¹ * y⁻¹ := by rw [← h2 x⁻¹]; group
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutator_twistedFix_le (hZ : Z ≤ Subgroup.center G) :
    ⁅twistedFix β Z hZ, twistedFix β Z hZ⁆ ≤ fixHom β := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  show β ⁅x, y⁆ = ⁅x, y⁆
  obtain ⟨z₁, hz₁, hxz⟩ : ∃ z ∈ Z, β x = x * z := ⟨x⁻¹ * β x, hx, by group⟩
  obtain ⟨z₂, hz₂, hyz⟩ : ∃ z ∈ Z, β y = y * z := ⟨y⁻¹ * β y, hy, by group⟩
  rw [map_commutatorElement, hxz, hyz]
  exact commutator_mul_central (central_mul_comm Z hZ hz₁) (central_mul_comm Z hZ hz₂)

theorem conj_mem_fixHom (hZ : Z ≤ Subgroup.center G) {x w : G} (hx : x ∈ twistedFix β Z hZ) (hw : w ∈ fixHom β) :
    x * w * x⁻¹ ∈ fixHom β := by
  have hw' : β w = w := hw
  show β (x * w * x⁻¹) = x * w * x⁻¹
  obtain ⟨z, hz, hxz⟩ : ∃ z ∈ Z, β x = x * z := ⟨x⁻¹ * β x, hx, by group⟩
  have hc := central_mul_comm Z hZ hz
  rw [map_mul, map_mul, map_inv, hw', hxz]
  calc x * z * w * (x * z)⁻¹ = x * (z * w) * z⁻¹ * x⁻¹ := by group
    _ = x * (w * z) * z⁻¹ * x⁻¹ := by rw [hc w]
    _ = x * w * x⁻¹ := by group

end Central

section Quotient

variable (β : G →* G) {Z : Subgroup G} [Z.Normal] (hZ : Z ≤ Subgroup.center G)
  (β' : (G ⧸ Z) →* (G ⧸ Z)) (hβ' : ∀ x : G, β' (x : G ⧸ Z) = ((β x : G) : G ⧸ Z))

include hZ hβ' in
theorem mk_mem_fix_iff (x : G) : (x : G ⧸ Z) ∈ fixHom β' ↔ x ∈ twistedFix β Z hZ := by
  show β' (x : G ⧸ Z) = (x : G ⧸ Z) ↔ x⁻¹ * β x ∈ Z
  rw [hβ', eq_comm, QuotientGroup.eq]

include hZ hβ' in
theorem fix_quot_eq_map : fixHom β' = (twistedFix β Z hZ).map (QuotientGroup.mk' Z) := by
  ext a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [mk_mem_fix_iff β hZ β' hβ']
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨w, hw, hwx⟩
    have : (w : G ⧸ Z) = x := hwx
    have hw' := (mk_mem_fix_iff β hZ β' hβ' w).2 hw
    rw [this] at hw'
    exact (mk_mem_fix_iff β hZ β' hβ' x).1 hw'

include hZ hβ' in
theorem commutator_fixHom_le :
    ⁅fixHom β', fixHom β'⁆ ≤ (fixHom β).map (QuotientGroup.mk' Z) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hx := (mk_mem_fix_iff β hZ β' hβ' x).1 ha
  have hy := (mk_mem_fix_iff β hZ β' hβ' y).1 hb
  exact ⟨⁅x, y⁆, commutator_twistedFix_le β Z hZ (Subgroup.commutator_mem_commutator hx hy),
    (map_commutatorElement (QuotientGroup.mk' Z) x y)⟩

include hZ hβ' in
theorem le_map_fixHom_of_perfect {J : Subgroup (G ⧸ Z)} (hJ : ⁅J, J⁆ = J) (hJf : J ≤ fixHom β') :
    J ≤ (fixHom β).map (QuotientGroup.mk' Z) :=
  hJ ▸ (Subgroup.commutator_mono hJf hJf).trans (commutator_fixHom_le β hZ β' hβ')

include hZ hβ' in
theorem map_fixHom_normal :
    (((fixHom β).map (QuotientGroup.mk' Z)).subgroupOf (fixHom β')).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  obtain ⟨x, hxg⟩ := QuotientGroup.mk_surjective (g : G ⧸ Z)
  have hx := (mk_mem_fix_iff β hZ β' hβ' x).1 (hxg ▸ g.2)
  rw [Subgroup.mem_subgroupOf]
  refine ⟨x * w * x⁻¹, conj_mem_fixHom β Z hZ hx hw, ?_⟩
  show ((x * w * x⁻¹ : G) : G ⧸ Z) = _
  have h1 : ((w : G) : G ⧸ Z) = (n : G ⧸ Z) := hwn
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hxg, ← h1]
  rfl

end Quotient

end CFSG.LieType.SemisimpleCentralizers.HeldLang
