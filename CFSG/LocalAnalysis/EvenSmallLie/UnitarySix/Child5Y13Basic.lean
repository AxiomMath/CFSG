module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDNormal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParQuot

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup

variable {G : Type} [Group G]

variable {d : YamadaD.Data G}

theorem t_comm_of_mem_L (h : YamadaD.Hyp d) {l : G} (hl : l ∈ d.L) : d.t * l = l * d.t :=
  (h.comm_of_mem_L hl).symm

theorem t_conj_eq_of_mem_L (h : YamadaD.Hyp d) {l : G} (hl : l ∈ d.L) : d.t * l * d.t⁻¹ = l := by
  rw [t_comm_of_mem_L h hl, mul_inv_cancel_right]

theorem t_conj_mem_of_normalizer {X : Subgroup G} (hX : d.t ∈ normalizer (X : Set G)) {x : G}
    (hx : x ∈ X) : d.t * x * d.t⁻¹ ∈ X :=
  (mem_normalizer_iff.mp hX x).mp hx

variable [Finite G]

theorem elemSec (h : YamadaD.Hyp d) (hB : YamadaD.HypB d) (hC : YamadaD.HypC d)
    (hV : ∀ v ∈ d.V₁, v * v = 1) : YamadaPar.ElemSec d.D₁ d.V₁ where
  le := h.V₁_le_D₁ hB hV
  central := fun v hv x hx => by
    have hv' : v ∈ d.D₁ ⊓ centralizer (d.D₁ : Set G) := (h.center_D₁ hB hV).symm ▸ hv
    exact (mem_centralizer_iff.mp hv'.2 x hx).symm
  comm := fun x hx y hy => h.D₁_comm_mod hB hC hV hx hy
  sq := fun x hx => h.D₁_sq_mod hB hC hV hx

theorem mem_A₁_of_comm (h : YamadaD.Hyp d) (hB : YamadaD.HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    {x : G} (hx : x ∈ d.D₁) (hxt : d.t * x = x * d.t) : x ∈ d.A₁ := by
  rw [← h.D₁_inf_H hB hV]
  exact mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr hxt.symm⟩

theorem mem_A₁_of_mem_A₂ (h : YamadaD.Hyp d) (hB : YamadaD.HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    {x : G} (hx : x ∈ d.D₁) (hxA : x ∈ d.A₂) : x ∈ d.A₁ :=
  mem_A₁_of_comm h hB hV hx (t_comm_of_mem_L h (h.A₂_le_L hxA))

theorem mem_zpowers_of_mem_A₁ (h : YamadaD.Hyp d) {x : G} (hx : x ∈ d.A₁) (hxV : x ∈ d.V₁) :
    x ∈ zpowers d.z := by
  rw [← h.V₁_inf_H]
  exact mem_inf.mpr ⟨hxV, h.L_le_H (h.A₁_le_L hx)⟩

theorem zpowers_z_le_V₁ (h : YamadaD.Hyp d) : zpowers d.z ≤ d.V₁ :=
  zpowers_le.mpr h.z_mem_V₁

@[expose] def kap (d : YamadaD.Data G) (x : G) : G := d.t * x * d.t⁻¹ * x⁻¹

theorem kap_mul (h : YamadaD.Hyp d) (hB : YamadaD.HypB d) {x y : G} (hx : x ∈ d.D₂)
    (hy : y ∈ d.D₂) : kap d (x * y) = kap d x * kap d y := by
  have htD := h.t_mem_normalizer_D₂
  have hx' := t_conj_mem_of_normalizer htD hx
  have hc : (d.t * y * d.t⁻¹ * y⁻¹) * x⁻¹ = x⁻¹ * (d.t * y * d.t⁻¹ * y⁻¹) :=
    h.D₂_comm hB (mul_mem (t_conj_mem_of_normalizer htD hy) (inv_mem hy)) (inv_mem hx)
  calc kap d (x * y) = (d.t * x * d.t⁻¹) * ((d.t * y * d.t⁻¹ * y⁻¹) * x⁻¹) := by
        simp only [kap]; group
    _ = (d.t * x * d.t⁻¹) * (x⁻¹ * (d.t * y * d.t⁻¹ * y⁻¹)) := by rw [hc]
    _ = kap d x * kap d y := by simp only [kap]; group

omit [Finite G] in
theorem kap_one : kap d 1 = 1 := by simp [kap]

omit [Finite G] in
theorem kap_mem {X : Subgroup G} (hX : d.t ∈ normalizer (X : Set G)) {x : G}
    (hx : x ∈ X) : kap d x ∈ X :=
  mul_mem (t_conj_mem_of_normalizer hX hx) (inv_mem hx)

theorem kap_mem_A₂ (h : YamadaD.Hyp d) (hB : YamadaD.HypB d) {x : G} (hx : x ∈ d.D₂) :
    kap d x ∈ d.A₂ := by
  have hxC : x⁻¹ ∈ d.C₂ := (h.C₂_eq_D₂_t hB).symm ▸ mem_sup_left (inv_mem hx)
  have h1 := h.crossed_C₂ hxC
  rw [inv_inv] at h1
  have h2 := t_conj_eq_of_mem_L h (h.A₂_le_L h1)
  have e : kap d x = d.t * (x * d.t * x⁻¹ * d.t) * d.t⁻¹ := by
    rw [show d.t * (x * d.t * x⁻¹ * d.t) * d.t⁻¹ = d.t * x * d.t * x⁻¹ by group]
    simp only [kap, h.t_inv]
  rw [e, h2]
  exact h1

omit [Finite G] in
theorem kap_eq_one_iff (h : YamadaD.Hyp d) {x : G} : kap d x = 1 ↔ d.t * x = x * d.t := by
  simp only [kap, h.t_inv]
  constructor
  · intro e
    have := congrArg (· * x * d.t) e
    simp only [mul_assoc, inv_mul_cancel, mul_one, one_mul, h.t_sq] at this
    exact this
  · intro e
    rw [e, mul_assoc x, h.t_sq, mul_one, mul_inv_cancel]

@[expose] noncomputable def kapHom (h : YamadaD.Hyp d) (hB : YamadaD.HypB d) (X : Subgroup G)
    (hXD : X ≤ d.D₂) (hX : d.t ∈ normalizer (X : Set G)) : X →* X where
  toFun x := ⟨kap d x, kap_mem hX x.2⟩
  map_one' := Subtype.ext kap_one
  map_mul' x y := Subtype.ext (kap_mul h hB (hXD x.2) (hXD y.2))

end CFSG.EvenSmallLie.UnitarySix.Child5
