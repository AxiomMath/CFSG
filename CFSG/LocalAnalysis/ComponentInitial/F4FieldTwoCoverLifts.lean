module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverRoots

public section

namespace CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover

open Subgroup
open scoped commutatorElement

section Identities

variable {G : Type*} [Group G]

theorem conj_eq_of_mem_center' {z : G} (hz : z ∈ center G) (g : G) : g * z * g⁻¹ = z := by
  rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_mem_center {a b c : G} (hz : ⁅a, c⁆ ∈ center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [show ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) by simp only [commutatorElement_def]; group,
    conj_eq_of_mem_center' hz]

theorem commutatorElement_mul_left_of_mem_center {a b c : G} (hz : ⁅b, c⁆ ∈ center G) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  rw [show ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ by simp only [commutatorElement_def]; group,
    conj_eq_of_mem_center' hz]

theorem conj_commutatorElement_of_mul_self {a : G} (ha : a * a = 1) (b : G) :
    a * ⁅a, b⁆ * a⁻¹ = ⁅a, b⁆⁻¹ := by
  refine mul_eq_one_iff_eq_inv.mp ?_
  calc a * ⁅a, b⁆ * a⁻¹ * ⁅a, b⁆ = (a * a) * b * (a * a)⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = 1 := by rw [ha, inv_one, mul_one, one_mul, mul_inv_cancel]

theorem mul_self_of_mul_self_of_commute {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb, one_mul]

end Identities

variable {E X : Type*} [Group E] [Group X]

variable (η : E →* X)

@[expose] def LiftsCommute (u v : X) : Prop :=
  ∀ a b : E, η a = u → η b = v → a * b = b * a

variable {η}

theorem LiftsCommute.symm {u v : X} (h : LiftsCommute η u v) : LiftsCommute η v u :=
  fun a b ha hb => (h b a hb ha).symm

theorem LiftsCommute.of_mul_left {u v : X} (h : LiftsCommute η u (u * v)) :
    LiftsCommute η u v :=
  fun a b ha hb => by
    have h1 := h a (a * b) ha (by rw [map_mul, ha, hb])
    have h2 : a * (a * b) = a * (b * a) := by
      rw [h1]
      group
    exact mul_left_cancel h2

variable (hη : Function.Surjective η) (hC : η.ker ≤ center E)

include hη in
theorem LiftsCommute.of_mul_right {u v w : X} (h : LiftsCommute η u (v * w))
    (hv : LiftsCommute η u v) : LiftsCommute η u w :=
  fun a c ha hc => by
    obtain ⟨b, hb⟩ := hη v
    have h1 := h a (b * c) ha (by rw [map_mul, hb, hc])
    have h2 := hv a b ha hb
    have h3 : b * (a * c) = b * (c * a) := by
      calc b * (a * c) = (b * a) * c := by group
        _ = (a * b) * c := by rw [h2]
        _ = a * (b * c) := by group
        _ = (b * c) * a := h1
        _ = b * (c * a) := by group
    exact mul_left_cancel h3

include hC in
theorem commutatorElement_lift_eq {a a' b b' : E} (ha : η a = η a') (hb : η b = η b') :
    ⁅a, b⁆ = ⁅a', b'⁆ :=
  LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η (fun _ hz => hC hz) ha hb

include hC in
theorem commutatorElement_mem_center_of_commute {a b : E} (hab : η a * η b = η b * η a) :
    ⁅a, b⁆ ∈ center E :=
  hC (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hab])

include hη in
theorem LiftsCommute.conj {u v : X} (h : LiftsCommute η u v) (g : X) :
    LiftsCommute η (g * u * g⁻¹) (g * v * g⁻¹) := by
  intro a b ha hb
  obtain ⟨t, ht⟩ := hη g
  have h1 := h (t⁻¹ * a * t) (t⁻¹ * b * t)
    (by rw [map_mul, map_mul, map_inv, ht, ha]; group)
    (by rw [map_mul, map_mul, map_inv, ht, hb]; group)
  calc a * b = t * ((t⁻¹ * a * t) * (t⁻¹ * b * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * b * t) * (t⁻¹ * a * t)) * t⁻¹ := by rw [h1]
    _ = b * a := by group

include hη hC in
theorem liftsCommute_of_conj_eq_mul {u v w g : X} (huw : u * w = w * u)
    (hgu : g * u * g⁻¹ = u) (hgw : g * w * g⁻¹ = v * w) : LiftsCommute η u v := by
  intro a b ha hb
  obtain ⟨c, hc⟩ := hη w
  obtain ⟨t, ht⟩ := hη g
  have hz : ⁅a, c⁆ ∈ center E :=
    commutatorElement_mem_center_of_commute hC (by rw [ha, hc]; exact huw)
  have e1 : ⁅a, c⁆ = ⁅a, b * c⁆ := by
    rw [← conj_eq_of_mem_center' hz t, conjugate_commutatorElement]
    refine commutatorElement_lift_eq hC ?_ ?_
    · rw [map_mul, map_mul, map_inv, ht, ha, hgu]
    · rw [map_mul, map_mul, map_inv, ht, hc, hgw, map_mul, hb, hc]
  rw [commutatorElement_mul_right_of_mem_center hz] at e1
  exact commutatorElement_eq_one_iff_mul_comm.mp (mul_eq_right.mp e1.symm)

include hη hC in
theorem exists_lift_mul_self_of_conj_eq_mul {u w g : X} (hw : w * w = 1)
    (huw : LiftsCommute η u w) (hgw : g * w * g⁻¹ = u * w) : ∃ y, η y = u ∧ y * y = 1 := by
  obtain ⟨p, hp⟩ := hη u
  obtain ⟨r, hr⟩ := hη w
  obtain ⟨t, ht⟩ := hη g
  have hr2 : r * r ∈ center E := hC (by rw [MonoidHom.mem_ker, map_mul, hr, hw])
  set c := t * r * t⁻¹ * (p * r)⁻¹ with hcdef
  have hc1 : η c = 1 := by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, ht, hr, hp, hgw,
      mul_inv_cancel]
  have hc : c ∈ center E := hC hc1
  have hpr := huw p r hp hr
  have h1 : t * r * t⁻¹ * (t * r * t⁻¹) = r * r := by
    rw [show t * r * t⁻¹ * (t * r * t⁻¹) = t * (r * r) * t⁻¹ by group,
      conj_eq_of_mem_center' hr2]
  have h2 : t * r * t⁻¹ = c * (p * r) := by
    rw [hcdef]
    group
  have hcp := Subgroup.mem_center_iff.mp hc p
  have hcr := Subgroup.mem_center_iff.mp hc r
  have h3 : c * (p * r) * (c * (p * r)) = (c * p) * (c * p) * (r * r) := by
    calc c * (p * r) * (c * (p * r)) = c * p * (r * c) * p * r := by group
      _ = c * p * (c * r) * p * r := by rw [hcr]
      _ = c * p * c * (r * p) * r := by group
      _ = c * p * c * (p * r) * r := by rw [hpr]
      _ = (c * p) * (c * p) * (r * r) := by group
  rw [h2, h3] at h1
  refine ⟨c * p, by rw [map_mul, hc1, hp, one_mul], mul_eq_right.mp h1⟩

include hη in
theorem exists_lift_mul_self_conj {u : X} (h : ∃ y, η y = u ∧ y * y = 1) (g : X) :
    ∃ y, η y = g * u * g⁻¹ ∧ y * y = 1 := by
  obtain ⟨y, hy, hy2⟩ := h
  obtain ⟨t, ht⟩ := hη g
  refine ⟨t * y * t⁻¹, by rw [map_mul, map_mul, map_inv, ht, hy], ?_⟩
  rw [show t * y * t⁻¹ * (t * y * t⁻¹) = t * (y * y) * t⁻¹ by group, hy2, mul_one,
    mul_inv_cancel]

variable (η) in
@[expose] def kerSq (hC : η.ker ≤ center E) : Subgroup E where
  carrier := {c | η c = 1 ∧ c * c = 1}
  one_mem' := ⟨map_one η, one_mul 1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
    have hba := Subgroup.mem_center_iff.mp (hC ha) b
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha', hb', one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_inv, ha, inv_one], by rw [← _root_.mul_inv_rev, ha', inv_one]⟩

theorem mem_kerSq {c : E} : c ∈ kerSq η hC ↔ η c = 1 ∧ c * c = 1 :=
  Iff.rfl

theorem kerSq_le_center : kerSq η hC ≤ center E := fun _ hc => hC hc.1

include hC in
theorem commutatorElement_mem_kerSq_of_commute {a b : E} (hab : η a * η b = η b * η a)
    (ha2 : η a * η a = 1) : ⁅a, b⁆ ∈ kerSq η hC := by
  have hk := commutatorElement_mem_center_of_commute hC hab
  have hk1 : η ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hab]
  refine ⟨hk1, ?_⟩
  have hz : a * a ∈ center E := hC (by rw [MonoidHom.mem_ker, map_mul, ha2])
  have h1 : ⁅a * a, b⁆ = 1 := by
    rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hz b]
    group
  rw [commutatorElement_mul_left_of_mem_center hk] at h1
  exact h1

include hC in
theorem commutatorElement_mul_inv_mem_kerSq {u v γ : X} {yu yv yγ : E} (hyu : η yu = u)
    (hyv : η yv = v) (hyγ : η yγ = γ) (hu2 : yu * yu = 1) (hγ2 : yγ * yγ = 1)
    (huv : ⁅u, v⁆ = γ) (hγu : LiftsCommute η γ u) :
    ⁅yu, yv⁆ * yγ⁻¹ ∈ kerSq η hC := by
  set k := ⁅yu, yv⁆ with hkdef
  have hk : η k = γ := by rw [hkdef, map_commutatorElement, hyu, hyv, huv]
  have hc1 : η (k * yγ⁻¹) = 1 := by rw [map_mul, map_inv, hk, hyγ, mul_inv_cancel]
  refine ⟨hc1, ?_⟩
  have hc := hC hc1
  have hku : k * yu = yu * k := hγu k yu hk hyu
  have hkk : k * k = 1 := by
    have h1 := conj_commutatorElement_of_mul_self hu2 yv
    rw [← hkdef, ← hku, mul_inv_cancel_right] at h1
    rw [← mul_eq_one_iff_eq_inv.mpr h1]
  set c := k * yγ⁻¹ with hcdef
  have hkc : k = c * yγ := by rw [hcdef]; group
  have hcy := Subgroup.mem_center_iff.mp hc yγ
  calc c * c = c * c * (yγ * yγ) := by rw [hγ2, mul_one]
    _ = c * (c * yγ) * yγ := by group
    _ = c * (yγ * c) * yγ := by rw [← hcy]
    _ = (c * yγ) * (c * yγ) := by group
    _ = k * k := by rw [← hkc]
    _ = 1 := hkk

include hC in
theorem commutatorElement_mul_inv_mem_kerSq_of_mul {u v γ δ : X} {yu yv yγ yδ : E}
    (hyu : η yu = u) (hyv : η yv = v) (hyγ : η yγ = γ) (hyδ : η yδ = δ) (hu2 : yu * yu = 1)
    (hγ2 : yγ * yγ = 1) (hδ2 : yδ * yδ = 1) (huv : ⁅u, v⁆ = γ * δ)
    (huγ : LiftsCommute η u γ) (huδ : LiftsCommute η u δ) (hγδ : LiftsCommute η γ δ) :
    ⁅yu, yv⁆ * (yγ * yδ)⁻¹ ∈ kerSq η hC := by
  set k := ⁅yu, yv⁆ with hkdef
  have hk : η k = γ * δ := by rw [hkdef, map_commutatorElement, hyu, hyv, huv]
  have hc1 : η (k * (yγ * yδ)⁻¹) = 1 := by
    rw [map_mul, map_inv, hk, map_mul, hyγ, hyδ, mul_inv_cancel]
  refine ⟨hc1, ?_⟩
  have hc := hC hc1
  set c := k * (yγ * yδ)⁻¹ with hcdef
  have hkc : k = c * (yγ * yδ) := by rw [hcdef]; group
  have hγu := huγ yu yγ hyu hyγ
  have hδu := huδ yu yδ hyu hyδ
  have hcu := Subgroup.mem_center_iff.mp hc yu
  have hku : k * yu = yu * k := by
    rw [hkc]
    calc c * (yγ * yδ) * yu = c * yγ * (yδ * yu) := by group
      _ = c * yγ * (yu * yδ) := by rw [hδu]
      _ = c * (yγ * yu) * yδ := by group
      _ = c * (yu * yγ) * yδ := by rw [hγu]
      _ = (c * yu) * yγ * yδ := by group
      _ = (yu * c) * yγ * yδ := by rw [← hcu]
      _ = yu * (c * (yγ * yδ)) := by group
  have hkk : k * k = 1 := by
    have h1 := conj_commutatorElement_of_mul_self hu2 yv
    rw [← hkdef, ← hku, mul_inv_cancel_right] at h1
    rw [← mul_eq_one_iff_eq_inv.mpr h1]
  have hγδ2 : yγ * yδ * (yγ * yδ) = 1 :=
    mul_self_of_mul_self_of_commute hγ2 hδ2 (hγδ yγ yδ hyγ hyδ)
  have hcy := Subgroup.mem_center_iff.mp hc (yγ * yδ)
  calc c * c = c * c * (yγ * yδ * (yγ * yδ)) := by rw [hγδ2, mul_one]
    _ = c * (c * (yγ * yδ)) * (yγ * yδ) := by group
    _ = c * ((yγ * yδ) * c) * (yγ * yδ) := by rw [← hcy]
    _ = (c * (yγ * yδ)) * (c * (yγ * yδ)) := by group
    _ = k * k := by rw [← hkc]
    _ = 1 := hkk

end CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
