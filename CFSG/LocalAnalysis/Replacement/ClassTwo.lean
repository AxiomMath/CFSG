module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace GlaubermanReplacement

open Subgroup
open scoped commutatorElement IsMulCommutative

section Pairing

variable {V C : Type*} [Group V] [CommGroup C]

private theorem pairing_sq_eq_one (β : V →* V →* C) (hβ : ∀ v, β v v = 1) {X Y : V →* V}
    (hXY : ∀ v, X (Y v) = Y (X v)) (hX : ∀ v w, β (X v) (X w) = β v w)
    (hY : ∀ v w, β (Y v) (Y w) = β v w) {v u w z : V} (hu : X v = u * v) (hw : Y v = w * v)
    (hz : X w = z * w) (hXz : X z = z) (hYz : Y z = z) : β u w ^ 2 = 1 := by
  have hanti : β u w * β w u = 1 := by simpa [hβ] using hβ (u * w)
  have huz : β u z = 1 := by simpa [hu, hXz] using hX v z
  have hwz : β w z = 1 := by simpa [hw, hYz] using hY v z
  have hYu : Y u = z * w * u * w⁻¹ := by
    have h := hXY v
    rw [hw, hu, map_mul, map_mul, hz, hu, hw] at h
    calc Y u = Y u * (w * v) * (w * v)⁻¹ := by group
      _ = z * w * u * w⁻¹ := by rw [← h]; group
  have h₁ : β u w * β v z = 1 :=
    mul_eq_right.1 (by simpa [hu, hz, huz, mul_assoc] using hX v w)
  have h₂ : β w u * β v z = 1 :=
    mul_eq_right.1 (by simpa [hw, hYu, hβ, hwz, mul_assoc] using hY v u)
  rw [sq]
  nth_rw 2 [mul_right_cancel (h₁.trans h₂.symm)]
  exact hanti

end Pairing

section ClassTwo

variable {B : Type*} [Group B]

@[expose] def commutatorPairing (h : commutator B ≤ center B) : B →* B →* center B :=
  have hmem (u v : B) : ⁅u, v⁆ ∈ center B :=
    h (commutator_mem_commutator (mem_top u) (mem_top v))
  have hconj (u v g : B) : g * ⁅u, v⁆ * g⁻¹ = ⁅u, v⁆ := by
    rw [mem_center_iff.1 (hmem u v) g, mul_inv_cancel_right]
  have hr (u v w : B) : ⁅u, v * w⁆ = ⁅u, v⁆ * ⁅u, w⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc, mul_assoc, ← mul_assoc v, hconj]
  have hl (u v w : B) : ⁅u * v, w⁆ = ⁅u, w⁆ * ⁅v, w⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hconj, mem_center_iff.1 (hmem u w)]
  MonoidHom.mk' (fun u ↦ MonoidHom.mk' (fun v ↦ ⟨⁅u, v⁆, hmem u v⟩) fun v w ↦
      Subtype.ext (hr u v w))
    fun u v ↦ MonoidHom.ext fun w ↦ Subtype.ext (hl u v w)

@[simp]
theorem coe_commutatorPairing_apply (h : commutator B ≤ center B) (u v : B) :
    (commutatorPairing h u v : B) = ⁅u, v⁆ :=
  rfl

theorem commute_of_commutator_le_center {p : ℕ} (hp : Odd p) (hB : IsPGroup p B)
    (hclass : commutator B ≤ center B) {X Y : B →* B} (hXY : ∀ v, X (Y v) = Y (X v))
    (hX : ∀ c ∈ commutator B, X c = c) (hY : ∀ c ∈ commutator B, Y c = c) {b u w z : B}
    (hu : X b = u * b) (hw : Y b = w * b) (hz : X w = z * w) (hXz : X z = z) (hYz : Y z = z) :
    Commute u w := by
  have hinv {F : B →* B} (hF : ∀ c ∈ commutator B, F c = c) (v w : B) :
      commutatorPairing hclass (F v) (F w) = commutatorPairing hclass v w := by
    ext
    simpa [map_commutatorElement] using hF _ (commutator_mem_commutator (mem_top v) (mem_top w))
  have hsq := pairing_sq_eq_one (commutatorPairing hclass) (fun v ↦ by ext; simp) hXY
    (hinv hX) (hinv hY) hu hw hz hXz hYz
  have hsq' : ⁅u, w⁆ ^ 2 = 1 := by simpa using congrArg Subtype.val hsq
  rw [← commutatorElement_eq_one_iff_commute, ← orderOf_eq_one_iff]
  exact (hB.orderOf_coprime hp.coprime_two_right _).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hsq')

end ClassTwo

section MutuallyNormalizing

variable {G : Type*} [Group G] {A D : Subgroup G}

private theorem commutator_sup_le_left [IsMulCommutative D] (hDA : D ≤ normalizer A) :
    ⁅A ⊔ D, A ⊔ D⁆ ≤ A := by
  have : (A.subgroupOf (A ⊔ D)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hDA)
  have hsup : A.subgroupOf (A ⊔ D) ⊔ D.subgroupOf (A ⊔ D) = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self (A ⊔ D)]
  rw [← map_subtype_commutator]
  refine (map_mono <|
    Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance).trans ?_
  rw [subgroupOf_map_subtype]
  exact inf_le_left

theorem commutator_sup_le_inf [IsMulCommutative A] [IsMulCommutative D]
    (hAD : A ≤ normalizer D) (hDA : D ≤ normalizer A) : ⁅A ⊔ D, A ⊔ D⁆ ≤ A ⊓ D :=
  le_inf (commutator_sup_le_left hDA) (sup_comm A D ▸ commutator_sup_le_left hAD)

theorem inf_le_centralizer_sup [IsMulCommutative A] [IsMulCommutative D] :
    A ⊓ D ≤ centralizer (A ⊔ D : Subgroup G) :=
  le_centralizer_iff.2 <| sup_le (le_centralizer_iff.1 (inf_le_left.trans (le_centralizer A)))
    (le_centralizer_iff.1 (inf_le_right.trans (le_centralizer D)))

end MutuallyNormalizing

end GlaubermanReplacement

end CFSG
