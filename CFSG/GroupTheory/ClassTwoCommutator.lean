module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_commutatorElement_mem_of_classTwo {Q Z : Subgroup G}
    (hZQ : Z ≤ Subgroup.centralizer (Q : Set G)) (hQQ : ⁅Q, Q⁆ ≤ Z) {x y τ : G}
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G)) (hxZ : x ∈ Subgroup.normalizer (Z : Set G))
    (hxyQ : ⁅x, y⁆ ∈ Q) (hτQ : τ ∈ Q) (hyτZ : ⁅y, τ⁆ ∈ Z) :
    ⁅y, ⁅x, τ⁆⁆ ∈ Z := by
  set a := ⁅y, x⁆ with ha
  set b := ⁅y, τ⁆ with hb
  set z := ⁅x, τ⁆ with hz
  have haQ : a ∈ Q := by
    rw [ha, ← commutatorElement_inv]
    exact Q.inv_mem hxyQ
  have hvQ : x * τ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxQ τ).mp hτQ
  have hzQ : z ∈ Q := by
    rw [hz, commutatorElement_def]
    exact Q.mul_mem hvQ (Q.inv_mem hτQ)
  have hb'Z : x * b * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hxZ b).mp hyτZ
  have hcZ : ⁅a, x * τ * x⁻¹⁆ ∈ Z := hQQ (Subgroup.commutator_mem_commutator haQ hvQ)
  have hab : a * (x * b * x⁻¹) = (x * b * x⁻¹) * a :=
    Subgroup.mem_centralizer_iff.mp (hZQ hb'Z) a haQ
  have hzb : z * b⁻¹ = b⁻¹ * z :=
    Subgroup.mem_centralizer_iff.mp (hZQ (Z.inv_mem hyτZ)) z hzQ
  have hyx : y * x * y⁻¹ = a * x := by rw [ha, commutatorElement_def]; group
  have hyτ : y * τ * y⁻¹ = b * τ := by rw [hb, commutatorElement_def]; group
  have hyx' : y * x⁻¹ * y⁻¹ = x⁻¹ * a⁻¹ := by
    have e : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    rw [e, hyx, mul_inv_rev]
  have hyτ' : y * τ⁻¹ * y⁻¹ = τ⁻¹ * b⁻¹ := by
    have e : y * τ⁻¹ * y⁻¹ = (y * τ * y⁻¹)⁻¹ := by group
    rw [e, hyτ, mul_inv_rev]
  have hava : a * (x * τ * x⁻¹) * a⁻¹ = ⁅a, x * τ * x⁻¹⁆ * (x * τ * x⁻¹) := by
    rw [commutatorElement_def]
    group
  have hzv : (x * τ * x⁻¹) * τ⁻¹ = z := by rw [hz]; rfl
  have e1 : y * z * y⁻¹ = (y * x * y⁻¹) * (y * τ * y⁻¹) *
      (y * x⁻¹ * y⁻¹) * (y * τ⁻¹ * y⁻¹) := by
    rw [hz]
    simp only [commutatorElement_def]
    group
  rw [hyx, hyτ, hyx', hyτ'] at e1
  have hmain : y * z * y⁻¹ = (x * b * x⁻¹ * ⁅a, x * τ * x⁻¹⁆ * b⁻¹) * z := by
    rw [e1]
    calc (a * x) * (b * τ) * (x⁻¹ * a⁻¹) * (τ⁻¹ * b⁻¹)
        = ((x * b * x⁻¹) * a) * (x * τ * x⁻¹) * a⁻¹ * τ⁻¹ * b⁻¹ := by
          rw [show (a * x) * (b * τ) * (x⁻¹ * a⁻¹) * (τ⁻¹ * b⁻¹) =
            (a * (x * b * x⁻¹)) * (x * τ * x⁻¹) * a⁻¹ * τ⁻¹ * b⁻¹ by group, hab]
      _ = (x * b * x⁻¹) * (⁅a, x * τ * x⁻¹⁆ * z) * b⁻¹ := by
          rw [show ((x * b * x⁻¹) * a) * (x * τ * x⁻¹) * a⁻¹ * τ⁻¹ * b⁻¹ =
            (x * b * x⁻¹) * (a * (x * τ * x⁻¹) * a⁻¹ * τ⁻¹) * b⁻¹ by group, hava]
          rw [show (x * b * x⁻¹) * (⁅a, x * τ * x⁻¹⁆ * (x * τ * x⁻¹) * τ⁻¹) * b⁻¹ =
            (x * b * x⁻¹) * (⁅a, x * τ * x⁻¹⁆ * ((x * τ * x⁻¹) * τ⁻¹)) * b⁻¹ by group]
          rw [hzv]
      _ = (x * b * x⁻¹ * ⁅a, x * τ * x⁻¹⁆ * b⁻¹) * z := by
          rw [show (x * b * x⁻¹) * (⁅a, x * τ * x⁻¹⁆ * z) * b⁻¹ =
            (x * b * x⁻¹) * (⁅a, x * τ * x⁻¹⁆ * (z * b⁻¹)) by group, hzb]
          group
  have hfinal : ⁅y, z⁆ = x * b * x⁻¹ * ⁅a, x * τ * x⁻¹⁆ * b⁻¹ := by
    rw [commutatorElement_def, hmain]
    group
  rw [hfinal]
  exact Z.mul_mem (Z.mul_mem hb'Z hcZ) (Z.inv_mem hyτZ)

theorem commutatorElement_commutatorElement_eq_of_classTwo {Q Z : Subgroup G}
    (hZQ : Z ≤ Subgroup.centralizer (Q : Set G)) (hQQ : ⁅Q, Q⁆ ≤ Z) {s w y : G}
    (hsQ : s ∈ Subgroup.normalizer (Q : Set G)) (hsZ : s ∈ Subgroup.centralizer (Z : Set G))
    (hw : w ∈ Q) (hy : y ∈ Q) :
    ⁅⁅s, w⁆, y⁆ = ⁅w, ⁅s⁻¹, y⁆⁆ := by
  have hsinv : s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hsQ
  have hsw : s * w * s⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hsQ w).mp hw
  have hsy : s⁻¹ * y * s ∈ Q := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hsinv y).mp hy
  have hZcomm : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z := fun z hz q hq =>
    ((Subgroup.mem_centralizer_iff.mp (hZQ hz)) q hq).symm
  have hsyZ : ⁅w, s⁻¹ * y * s⁆ ∈ Z :=
    hQQ (Subgroup.commutator_mem_commutator hw hsy)
  have hwyinvZ : ⁅w, y⁻¹⁆ ∈ Z :=
    hQQ (Subgroup.commutator_mem_commutator hw (Q.inv_mem hy))
  have hwinvyZ : ⁅w⁻¹, y⁆ ∈ Z :=
    hQQ (Subgroup.commutator_mem_commutator (Q.inv_mem hw) hy)
  have hwinvyQ : ⁅w⁻¹, y⁆ ∈ Q :=
    Subgroup.commutator_le_self Q (Q.commutator_mem_commutator (Q.inv_mem hw) hy)
  have hwyinvQ : ⁅w, y⁻¹⁆ ∈ Q :=
    Subgroup.commutator_le_self Q (Q.commutator_mem_commutator hw (Q.inv_mem hy))
  have hinv : ⁅w⁻¹, y⁆ = ⁅w, y⁻¹⁆ := by
    rw [commutatorElement_inv_left, commutatorElement_inv_right]
    have h1 := hZcomm _ (hQQ (Subgroup.commutator_mem_commutator hy hw)) w hw
    have h2 := hZcomm _ (hQQ (Subgroup.commutator_mem_commutator hy hw)) y hy
    rw [show w⁻¹ * ⁅y, w⁆ * w = w⁻¹ * (⁅y, w⁆ * w) by group,
      show y⁻¹ * ⁅y, w⁆ * y = y⁻¹ * (⁅y, w⁆ * y) by group, h1, h2]
    group
  have hconj : s * ⁅w, s⁻¹ * y * s⁆ * s⁻¹ = ⁅s * w * s⁻¹, y⁆ := by
    have h := conjugate_commutatorElement w (s⁻¹ * y * s) s
    rwa [show s * (s⁻¹ * y * s) * s⁻¹ = y by group] at h
  have hfix : s * ⁅w, s⁻¹ * y * s⁆ * s⁻¹ = ⁅w, s⁻¹ * y * s⁆ := by
    have h := Subgroup.mem_centralizer_iff.mp hsZ _ hsyZ
    rw [← h]; group
  have hA : ⁅s * w * s⁻¹, y⁆ = ⁅w, s⁻¹ * y * s⁆ := by
    rw [← hconj, hfix]
  have hfixw : (s * w * s⁻¹) * ⁅w⁻¹, y⁆ * (s * w * s⁻¹)⁻¹ = ⁅w⁻¹, y⁆ := by
    have h := hZcomm _ hwinvyZ (s * w * s⁻¹) hsw
    rw [← h]; group
  have hfixy : (s⁻¹ * y * s) * ⁅w, y⁻¹⁆ * (s⁻¹ * y * s)⁻¹ = ⁅w, y⁻¹⁆ := by
    have h := hZcomm _ hwyinvZ (s⁻¹ * y * s) hsy
    rw [← h]; group
  have hcomm : ⁅w, y⁻¹⁆ * ⁅w, s⁻¹ * y * s⁆ =
      ⁅w, s⁻¹ * y * s⁆ * ⁅w, y⁻¹⁆ :=
    (hZcomm _ hsyZ _ hwyinvQ).symm
  have hR : ⁅w, s⁻¹ * y * s⁆ * ⁅w, y⁻¹⁆ = ⁅w, (s⁻¹ * y * s) * y⁻¹⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj (a := w) (b := s⁻¹ * y * s) (c := y⁻¹)]
    rw [show ⁅w, s⁻¹ * y * s⁆ * (s⁻¹ * y * s) * ⁅w, y⁻¹⁆ * (s⁻¹ * y * s)⁻¹ =
        ⁅w, s⁻¹ * y * s⁆ * ((s⁻¹ * y * s) * ⁅w, y⁻¹⁆ * (s⁻¹ * y * s)⁻¹) by group]
    rw [hfixy]
  have hswdef : ⁅s, w⁆ = (s * w * s⁻¹) * w⁻¹ := by
    rw [commutatorElement_def]
  have hsdef : ⁅s⁻¹, y⁆ = (s⁻¹ * y * s) * y⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hswdef, hsdef]
  calc
    ⁅(s * w * s⁻¹) * w⁻¹, y⁆ =
        (s * w * s⁻¹) * ⁅w⁻¹, y⁆ * (s * w * s⁻¹)⁻¹ *
          ⁅s * w * s⁻¹, y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul]
    _ = ⁅w⁻¹, y⁆ * ⁅s * w * s⁻¹, y⁆ := by rw [hfixw]
    _ = ⁅w, y⁻¹⁆ * ⁅s * w * s⁻¹, y⁆ := by rw [hinv]
    _ = ⁅w, y⁻¹⁆ * ⁅w, s⁻¹ * y * s⁆ := by rw [hA]
    _ = ⁅w, s⁻¹ * y * s⁆ * ⁅w, y⁻¹⁆ := hcomm
    _ = ⁅w, (s⁻¹ * y * s) * y⁻¹⁆ := hR

end CFSG.GroupTheory
