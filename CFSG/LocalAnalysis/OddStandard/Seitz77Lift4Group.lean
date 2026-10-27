module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Lift4

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Group

variable {G : Type*} [Group G]

@[expose] def conjOn (V : Subgroup G) (x : G) (hx : ∀ y, y ∈ V ↔ x * y * x⁻¹ ∈ V) :
    MulAut V where
  toFun y := ⟨x * y * x⁻¹, (hx y).1 y.2⟩
  invFun y := ⟨x⁻¹ * y * x, (hx (x⁻¹ * y * x)).2 (by
    have h : x * (x⁻¹ * (y : G) * x) * x⁻¹ = y := by group
    rw [h]
    exact y.2)⟩
  left_inv y := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv y := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' y z := by
    apply Subtype.ext
    simp [mul_assoc]

theorem coe_conjOn (V : Subgroup G) (x : G) (hx : ∀ y, y ∈ V ↔ x * y * x⁻¹ ∈ V) (y : V) :
    ((conjOn V x hx y : V) : G) = x * y * x⁻¹ := rfl

theorem exists_order_four_lift {F : Type} [Field F] (hF : Nat.card F = 4) {V : Subgroup G}
    (e : V ≃* unipAll F) {x t : G} (hx : ∀ y, y ∈ V ↔ x * y * x⁻¹ ∈ V) (ht : t * t = 1)
    (htx : t * x = x * t) (htV : ∀ y ∈ V, t * y = y * t) {v : G} (hv : v ∈ V)
    (hxv : x * x = t * v) :
    ∃ s ∈ V, ∃ v' ∈ V, (x * s) * (x * s) = t * v' ∧ v' * v' = 1 := by
  have htw : ∀ w ∈ V, t * w * t = w := fun w hw => by
    rw [htV w hw, mul_assoc, ht, mul_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set c := conjOn V x hx with hc
  let ρ : MulAut (unipAll F) := e.symm.trans (c.trans e)
  have hρe : ∀ u : V, ρ (e u) = e (c u) := fun u => by
    simp [ρ]
  have hcc : ∀ u : V, c (c u) = ⟨v, hv⟩ * u * ⟨v, hv⟩⁻¹ := fun u => by
    apply Subtype.ext
    have h1 : x * (x * (u : G) * x⁻¹) * x⁻¹ = (x * x) * u * (x * x)⁻¹ := by group
    have h2 : t * v * (u : G) * (t * v)⁻¹ = t * (v * u * v⁻¹) * t := by
      rw [mul_inv_rev, htinv]
      group
    have hvuv : v * (u : G) * v⁻¹ ∈ V := V.mul_mem (V.mul_mem hv u.2) (V.inv_mem hv)
    show x * (x * (u : G) * x⁻¹) * x⁻¹ = v * u * v⁻¹
    rw [h1, hxv, h2, htw _ hvuv]
  have hρρ : ρ * ρ = MulAut.conj (e ⟨v, hv⟩) := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [MulAut.mul_apply, hρe, hρe, hcc, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hcv : c ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply Subtype.ext
    have hvt : v = t * (x * x) := by rw [hxv, ← mul_assoc, ht, one_mul]
    show x * v * x⁻¹ = v
    calc x * v * x⁻¹ = x * (t * (x * x)) * x⁻¹ := by rw [← hvt]
      _ = (x * t) * (x * x) * x⁻¹ := by rw [mul_assoc x t]
      _ = t * (x * x) := by rw [← htx]; group
      _ = v := hvt.symm
  have hρv : ρ (e ⟨v, hv⟩) = e ⟨v, hv⟩ := by rw [hρe, hcv]
  obtain ⟨sF, hsF⟩ := lift4 hF ρ (e ⟨v, hv⟩) hρρ hρv
  obtain ⟨s, rfl⟩ := e.surjective sF
  rw [hρe, sq, ← map_mul, ← map_mul, ← map_mul, ← map_one e] at hsF
  have hsq := e.injective hsF
  have hv'V : ((c s * ⟨v, hv⟩ * s : V) : G) ∈ V := (c s * ⟨v, hv⟩ * s : V).2
  refine ⟨s, s.2, ((c s * ⟨v, hv⟩ * s : V) : G), hv'V, ?_, ?_⟩
  · have hcs : t * (x * (s : G) * x⁻¹) = (x * s * x⁻¹) * t := htV _ (c s).2
    calc x * (s : G) * (x * s) = (x * s * x⁻¹) * (x * x) * s := by group
      _ = (x * s * x⁻¹) * (t * v) * s := by rw [hxv]
      _ = ((x * s * x⁻¹) * t) * v * s := by simp only [mul_assoc]
      _ = t * ((c s * ⟨v, hv⟩ * s : V) : G) := by
        rw [← hcs]
        show _ = t * ((x * s * x⁻¹) * v * s)
        simp only [mul_assoc]
  · have := congrArg Subtype.val hsq
    simpa using this

end Group

end CFSG.OddStandard.Seitz77
