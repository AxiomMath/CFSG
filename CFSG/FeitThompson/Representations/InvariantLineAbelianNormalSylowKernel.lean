module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Finite.Basic

open Matrix Module

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {k : Type*} [Field k] {w u : Fin 2 → k} {g h : GL (Fin 2) k}

private def cross (x y : Fin 2 → k) : k := x 0 * y 1 - x 1 * y 0

private theorem cross_self (x : Fin 2 → k) : cross x x = 0 := by simp [cross]; ring

private theorem cross_smul_right (c : k) (x y : Fin 2 → k) :
    cross x (c • y) = c * cross x y := by simp [cross]; ring

private theorem cross_smul_left (c : k) (x y : Fin 2 → k) :
    cross (c • x) y = c * cross x y := by simp [cross]; ring

private theorem cross_add_left (x y z : Fin 2 → k) :
    cross (x + y) z = cross x z + cross y z := by simp [cross]; ring

private theorem cross_add_right (x y z : Fin 2 → k) :
    cross x (y + z) = cross x y + cross x z := by simp [cross]; ring

private theorem cross_sub_right (x y z : Fin 2 → k) :
    cross x (y - z) = cross x y - cross x z := by simp [cross]; ring

private theorem cross_gl_smul (g : GL (Fin 2) k) (x y : Fin 2 → k) :
    cross (g • x) (g • y) = (Matrix.GeneralLinearGroup.det g : k) * cross x y := by
  change cross ((g : Matrix (Fin 2) (Fin 2) k) *ᵥ x) ((g : Matrix (Fin 2) (Fin 2) k) *ᵥ y) = _
  simp only [cross, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  ring

private theorem apply_one_ne_zero (hw : w ≠ 0) (h0 : w 0 = 0) : w 1 ≠ 0 := by
  intro h1
  refine hw (funext ?_)
  rw [Fin.forall_fin_two]
  simp [h0, h1]

private theorem cross_eq_zero_iff (hw : w ≠ 0) (v : Fin 2 → k) :
    cross w v = 0 ↔ v ∈ Submodule.span k {w} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hv
    simp only [cross, sub_eq_zero] at hv
    rcases eq_or_ne (w 0) 0 with h0 | h0
    · have h1 : w 1 ≠ 0 := apply_one_ne_zero hw h0
      have hv0 : v 0 = 0 := by
        rw [h0, zero_mul] at hv
        exact (mul_eq_zero.mp hv.symm).resolve_left h1
      refine ⟨v 1 / w 1, funext ?_⟩
      rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩ <;> simp only [Pi.smul_apply, smul_eq_mul]
      · rw [h0, mul_zero, hv0]
      · field_simp
    · refine ⟨v 0 / w 0, funext ?_⟩
      rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩ <;> simp only [Pi.smul_apply, smul_eq_mul]
      · field_simp
      · field_simp
        linear_combination -hv
  · rintro ⟨c, rfl⟩
    rw [cross_smul_right, cross_self, mul_zero]

private theorem cross_ne_zero_iff_notMem (hw : w ≠ 0) :
    cross w u ≠ 0 ↔ u ∉ Submodule.span k {w} :=
  not_congr (cross_eq_zero_iff hw u)

private theorem exists_cross_ne_zero (hw : w ≠ 0) : ∃ u, cross w u ≠ 0 := by
  rcases eq_or_ne (w 0) 0 with h0 | h0
  · exact ⟨Pi.single 0 1, by simpa [cross, h0] using apply_one_ne_zero hw h0⟩
  · exact ⟨Pi.single 1 1, by simpa [cross] using h0⟩

private theorem eq_decomp (hc : cross w u ≠ 0) (v : Fin 2 → k) :
    v = (cross v u / cross w u) • w + (cross w v / cross w u) • u := by
  have hc' : u 1 * w 0 - u 0 * w 1 ≠ 0 := fun hh =>
    hc (by simp only [cross]; linear_combination hh)
  refine funext ?_
  rw [Fin.forall_fin_two]
  simp only [cross] at *
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> field_simp <;> ring

private theorem eq_one_of_smul_eq (hc : cross w u ≠ 0) (hgw : g • w = w) (hgu : g • u = u) :
    g = 1 := by
  refine Units.ext ?_
  rw [Matrix.ext_iff_mulVec]
  intro v
  have h1 : ∀ x : Fin 2 → k, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ x = g • x := fun _ => rfl
  rw [eq_decomp hc v, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h1,
    hgw, hgu, Units.val_one, Matrix.one_mulVec]

private theorem gl_smul_ne_zero (g : GL (Fin 2) k) {v : Fin 2 → k} (hv : v ≠ 0) : g • v ≠ 0 := by
  intro hh
  refine hv ?_
  have h1 : g⁻¹ • (g • v) = g⁻¹ • (0 : Fin 2 → k) := by rw [hh]
  rwa [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h1

theorem exists_eq_span_singleton_of_finrank_eq_one {W : Submodule k (Fin 2 → k)}
    (hW : finrank k W = 1) : ∃ w : Fin 2 → k, w ≠ 0 ∧ W = Submodule.span k {w} := by
  have hne : W ≠ ⊥ := by
    intro hb
    rw [hb] at hW
    simp at hW
  obtain ⟨w, hwW, hw0⟩ := W.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨w, hw0, eq_span_singleton_of_mem_of_finrank_eq_one hW hwW hw0⟩

def lineUnipotent (W : Submodule k (Fin 2 → k)) : Subgroup (GL (Fin 2) k) where
  carrier := {g | (∀ v ∈ W, g • v = v) ∧ ∀ v, g • v - v ∈ W}
  one_mem' := ⟨fun v _ => one_smul _ v, fun v => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · rw [mul_smul, hh1 v hv, hg1 v hv]
    · have h1 : (g * h) • v - v = g • (h • v - v) + (g • v - v) := by
        rw [mul_smul, smul_sub]; abel
      rw [h1, hg1 _ (hh2 v)]
      exact W.add_mem (hh2 v) (hg2 v)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · conv_lhs => rw [← hg1 v hv]
      rw [← mul_smul, inv_mul_cancel, one_smul]
    · have h1 : g⁻¹ • v - v = -(g • (g⁻¹ • v) - g⁻¹ • v) := by
        rw [← mul_smul, mul_inv_cancel, one_smul]; abel
      rw [h1]
      exact W.neg_mem (hg2 _)

theorem mem_lineUnipotent {W : Submodule k (Fin 2 → k)} {g : GL (Fin 2) k} :
    g ∈ lineUnipotent W ↔ (∀ v ∈ W, g • v = v) ∧ ∀ v, g • v - v ∈ W := Iff.rfl

theorem smul_eq_self_of_mem_lineUnipotent {W : Submodule k (Fin 2 → k)}
    (hg : g ∈ lineUnipotent W) {v : Fin 2 → k} (hv : v ∈ W) : g • v = v := hg.1 v hv

theorem smul_sub_self_mem_of_mem_lineUnipotent {W : Submodule k (Fin 2 → k)}
    (hg : g ∈ lineUnipotent W) (v : Fin 2 → k) : g • v - v ∈ W := hg.2 v

theorem lineUnipotent_conj_mem {W : Submodule k (Fin 2 → k)}
    (hg : ∀ v ∈ W, g • v ∈ W) (hg' : ∀ v ∈ W, g⁻¹ • v ∈ W)
    (hh : h ∈ lineUnipotent W) : g * h * g⁻¹ ∈ lineUnipotent W := by
  have hcancel : ∀ v : Fin 2 → k, g • (g⁻¹ • v) = v := fun v => by
    rw [← mul_smul, mul_inv_cancel, one_smul]
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h1 : (g * h * g⁻¹) • v = g • (h • (g⁻¹ • v)) := by rw [mul_smul, mul_smul]
    rw [h1, hh.1 _ (hg' v hv), hcancel]
  · have h1 : (g * h * g⁻¹) • v - v = g • (h • (g⁻¹ • v) - g⁻¹ • v) := by
      rw [mul_smul, mul_smul, smul_sub, hcancel]
    rw [h1]
    exact hg _ (hh.2 _)

private def shearCoeff (w u : Fin 2 → k) (g : GL (Fin 2) k) : k := cross (g • u) u / cross w u

private theorem shearCoeff_one : shearCoeff w u (1 : GL (Fin 2) k) = 0 := by
  simp [shearCoeff, one_smul, cross_self]

private theorem smul_eq_add_shearCoeff (hc : cross w u ≠ 0)
    (hg : g ∈ lineUnipotent (Submodule.span k {w})) :
    g • u = u + shearCoeff w u g • w := by
  obtain ⟨c, hcw⟩ := Submodule.mem_span_singleton.1 (hg.2 u)
  have hgu : g • u = u + c • w := by rw [hcw]; abel
  have hs : shearCoeff w u g = c := by
    rw [shearCoeff, hgu, cross_add_left, cross_self, cross_smul_left, zero_add,
      mul_div_cancel_right₀ _ hc]
  rw [hgu, hs]

private theorem shearCoeff_mul (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g ∈ lineUnipotent (Submodule.span k {w}))
    (hh : h ∈ lineUnipotent (Submodule.span k {w})) :
    shearCoeff w u (g * h) = shearCoeff w u g + shearCoeff w u h := by
  have hgw : g • w = w := hg.1 w (Submodule.mem_span_singleton_self w)
  have key : (g * h) • u = u + (shearCoeff w u g + shearCoeff w u h) • w := by
    rw [mul_smul, smul_eq_add_shearCoeff hc hh, smul_add, smul_eq_add_shearCoeff hc hg,
      smul_comm g (shearCoeff w u h) w, hgw, add_smul]
    abel
  have h2 := smul_eq_add_shearCoeff hc ((lineUnipotent (Submodule.span k {w})).mul_mem hg hh)
  rw [key] at h2
  exact (smul_left_injective k hw (add_left_cancel h2)).symm

private theorem eq_one_of_shearCoeff_eq_zero (hc : cross w u ≠ 0)
    (hg : g ∈ lineUnipotent (Submodule.span k {w})) (h0 : shearCoeff w u g = 0) : g = 1 := by
  refine eq_one_of_smul_eq hc (hg.1 w (Submodule.mem_span_singleton_self w)) ?_
  rw [smul_eq_add_shearCoeff hc hg, h0, zero_smul, add_zero]

private def lineCoeff (w u : Fin 2 → k) (g : GL (Fin 2) k) : k := cross (g • w) u / cross w u

private def quotCoeff (w u : Fin 2 → k) (g : GL (Fin 2) k) : k := cross w (g • u) / cross w u

private theorem lineCoeff_one (hc : cross w u ≠ 0) :
    lineCoeff w u (1 : GL (Fin 2) k) = 1 := by
  rw [lineCoeff, one_smul, div_self hc]

private theorem quotCoeff_one (hc : cross w u ≠ 0) :
    quotCoeff w u (1 : GL (Fin 2) k) = 1 := by
  rw [quotCoeff, one_smul, div_self hc]

private theorem smul_snd_eq (hc : cross w u ≠ 0) (g : GL (Fin 2) k) :
    g • u = shearCoeff w u g • w + quotCoeff w u g • u := eq_decomp hc (g • u)

private theorem smul_line (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g • w ∈ Submodule.span k {w}) : g • w = lineCoeff w u g • w := by
  have h0 : cross w (g • w) = 0 := (cross_eq_zero_iff hw _).2 hg
  rw [eq_decomp hc (g • w), h0, zero_div, zero_smul, add_zero, lineCoeff]

private theorem lineCoeff_ne_zero (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g • w ∈ Submodule.span k {w}) : lineCoeff w u g ≠ 0 := by
  intro h0
  refine gl_smul_ne_zero g hw ?_
  rw [smul_line hw hc hg, h0, zero_smul]

private theorem det_eq_mul (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g • w ∈ Submodule.span k {w}) :
    (Matrix.GeneralLinearGroup.det g : k) = lineCoeff w u g * quotCoeff w u g := by
  have h1 : cross (g • w) (g • u) = (Matrix.GeneralLinearGroup.det g : k) * cross w u :=
    cross_gl_smul g w u
  rw [smul_line hw hc hg, smul_snd_eq hc g, cross_smul_left, cross_add_right,
    cross_smul_right, cross_smul_right, cross_self, mul_zero, zero_add] at h1
  field_simp at h1
  exact h1.symm

private theorem quotCoeff_ne_zero (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g • w ∈ Submodule.span k {w}) : quotCoeff w u g ≠ 0 := by
  intro h0
  have hd := det_eq_mul hw hc hg
  rw [h0, mul_zero] at hd
  exact (Matrix.GeneralLinearGroup.det g).ne_zero hd

private theorem lineCoeff_mul (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g • w ∈ Submodule.span k {w}) (hh : h • w ∈ Submodule.span k {w}) :
    lineCoeff w u (g * h) = lineCoeff w u g * lineCoeff w u h := by
  have h1 : (g * h) • w = lineCoeff w u h • (g • w) := by
    rw [mul_smul, smul_line hw hc hh, smul_comm]
  rw [lineCoeff, h1, cross_smul_left, smul_line hw hc hg, cross_smul_left, lineCoeff]
  field_simp

private theorem quotCoeff_mul (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g • w ∈ Submodule.span k {w}) :
    quotCoeff w u (g * h) = quotCoeff w u g * quotCoeff w u h := by
  have hgw : cross w (g • w) = 0 := (cross_eq_zero_iff hw _).2 hg
  have h1 : (g * h) • u = shearCoeff w u h • (g • w) + quotCoeff w u h • (g • u) := by
    rw [mul_smul, smul_snd_eq hc h, smul_add, smul_comm g (shearCoeff w u h),
      smul_comm g (quotCoeff w u h)]
  rw [quotCoeff, h1, cross_add_right, cross_smul_right, cross_smul_right, hgw, mul_zero,
    zero_add, quotCoeff, quotCoeff]
  field_simp

private theorem mem_lineUnipotent_iff (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hg : g • w ∈ Submodule.span k {w}) :
    g ∈ lineUnipotent (Submodule.span k {w}) ↔ lineCoeff w u g = 1 ∧ quotCoeff w u g = 1 := by
  rw [mem_lineUnipotent]
  constructor
  · rintro ⟨h1, h2⟩
    have hgw : g • w = w := h1 w (Submodule.mem_span_singleton_self w)
    refine ⟨?_, ?_⟩
    · have h5 := smul_line hw hc hg
      rw [hgw] at h5
      have h3 : (1 : k) • w = lineCoeff w u g • w := by rw [one_smul]; exact h5
      exact (smul_left_injective k hw h3).symm
    · have h4 : cross w (g • u - u) = 0 := (cross_eq_zero_iff hw _).2 (h2 u)
      rw [cross_sub_right, sub_eq_zero] at h4
      rw [quotCoeff, h4, div_self hc]
  · rintro ⟨h1, h2⟩
    have hgw : g • w = w := by rw [smul_line hw hc hg, h1, one_smul]
    have hgu : g • u - u = shearCoeff w u g • w := by
      rw [smul_snd_eq hc g, h2, one_smul]; abel
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [smul_comm, hgw]
    · rw [eq_decomp hc v, smul_add, smul_comm g _ w, smul_comm g _ u, hgw]
      have h6 : (cross v u / cross w u) • w + (cross w v / cross w u) • (g • u)
          - ((cross v u / cross w u) • w + (cross w v / cross w u) • u)
          = (cross w v / cross w u) • (g • u - u) := by
        rw [smul_sub]; abel
      rw [h6, hgu, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)

variable (G : Subgroup (GL (Fin 2) k))

def lineUnipotentCore (W : Submodule k (Fin 2 → k)) : Subgroup G :=
  (lineUnipotent W).comap G.subtype

variable {G}

theorem mem_lineUnipotentCore {W : Submodule k (Fin 2 → k)} {x : G} :
    x ∈ lineUnipotentCore G W ↔ (x : GL (Fin 2) k) ∈ lineUnipotent W := Iff.rfl

theorem lineUnipotentCore_normal {W : Submodule k (Fin 2 → k)}
    (hG : ∀ g ∈ G, ∀ v ∈ W, g • v ∈ W) : (lineUnipotentCore G W).Normal := by
  constructor
  intro x hx y
  rw [mem_lineUnipotentCore] at hx ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact lineUnipotent_conj_mem (hG _ y.2) (hG _ (G.inv_mem y.2)) hx

theorem smul_mem_span_singleton_of_smul_mem
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) :
    ∀ g ∈ G, ∀ v ∈ Submodule.span k {w}, g • v ∈ Submodule.span k {w} := by
  intro g hg v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (hG g hg)

theorem lineUnipotentCore_span_singleton_normal
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) :
    (lineUnipotentCore G (Submodule.span k {w})).Normal :=
  lineUnipotentCore_normal (smul_mem_span_singleton_of_smul_mem hG)

private def diagHom (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) : G →* kˣ × kˣ where
  toFun x := (Units.mk0 _ (lineCoeff_ne_zero hw hc (hG x x.2)),
    Units.mk0 _ (quotCoeff_ne_zero hw hc (hG x x.2)))
  map_one' := by
    ext
    · exact lineCoeff_one hc
    · exact quotCoeff_one hc
  map_mul' x y := by
    ext
    · exact lineCoeff_mul hw hc (hG x x.2) (hG y y.2)
    · exact quotCoeff_mul hw hc (hG x x.2)

private theorem diagHom_apply_fst (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) (x : G) :
    (((diagHom hw hc hG x).1 : kˣ) : k) = lineCoeff w u (x : GL (Fin 2) k) := rfl

private theorem diagHom_apply_snd (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) (x : G) :
    (((diagHom hw hc hG x).2 : kˣ) : k) = quotCoeff w u (x : GL (Fin 2) k) := rfl

private theorem ker_diagHom (hw : w ≠ 0) (hc : cross w u ≠ 0)
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) :
    (diagHom hw hc hG).ker = lineUnipotentCore G (Submodule.span k {w}) := by
  ext x
  rw [MonoidHom.mem_ker, mem_lineUnipotentCore, mem_lineUnipotent_iff hw hc (hG x x.2),
    Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← diagHom_apply_fst hw hc hG x, h1]; simp
    · rw [← diagHom_apply_snd hw hc hG x, h2]; simp
  · rintro ⟨h1, h2⟩
    refine ⟨Units.ext ?_, Units.ext ?_⟩
    · rw [diagHom_apply_fst hw hc hG x, h1]; simp
    · rw [diagHom_apply_snd hw hc hG x, h2]; simp

theorem commutator_le_lineUnipotentCore (hw : w ≠ 0)
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) :
    commutator G ≤ lineUnipotentCore G (Submodule.span k {w}) := by
  obtain ⟨u, hc⟩ := exists_cross_ne_zero hw
  rw [← ker_diagHom hw hc hG]
  exact Abelianization.commutator_subset_ker (diagHom hw hc hG)

def shearHom (hw : w ≠ 0) (hu : u ∉ Submodule.span k {w}) :
    lineUnipotentCore G (Submodule.span k {w}) →* Multiplicative k where
  toFun x := Multiplicative.ofAdd (shearCoeff w u ((x : G) : GL (Fin 2) k))
  map_one' := by
    change Multiplicative.ofAdd (shearCoeff w u (1 : GL (Fin 2) k)) = 1
    rw [shearCoeff_one]
    rfl
  map_mul' x y := by
    have hc : cross w u ≠ 0 := (cross_ne_zero_iff_notMem hw).2 hu
    have hx : ((x : G) : GL (Fin 2) k) ∈ lineUnipotent (Submodule.span k {w}) :=
      mem_lineUnipotentCore.1 x.2
    have hy : ((y : G) : GL (Fin 2) k) ∈ lineUnipotent (Submodule.span k {w}) :=
      mem_lineUnipotentCore.1 y.2
    change Multiplicative.ofAdd (shearCoeff w u (((x * y : _) : G) : GL (Fin 2) k)) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, shearCoeff_mul hw hc hx hy]
    rfl

theorem shearHom_injective (hw : w ≠ 0) (hu : u ∉ Submodule.span k {w}) :
    Function.Injective (shearHom (G := G) hw hu) := by
  have hc : cross w u ≠ 0 := (cross_ne_zero_iff_notMem hw).2 hu
  rw [injective_iff_map_eq_one]
  intro x hx
  have h0 : shearCoeff w u ((x : G) : GL (Fin 2) k) = 0 := congrArg Multiplicative.toAdd hx
  exact Subtype.ext (Subtype.ext
    (eq_one_of_shearCoeff_eq_zero hc (mem_lineUnipotentCore.1 x.2) h0))

private theorem exists_notMem_span_singleton (hw : w ≠ 0) :
    ∃ u : Fin 2 → k, u ∉ Submodule.span k {w} := by
  obtain ⟨u, hc⟩ := exists_cross_ne_zero hw
  exact ⟨u, (cross_ne_zero_iff_notMem hw).1 hc⟩

theorem lineUnipotentCore_isMulCommutative (hw : w ≠ 0) :
    IsMulCommutative (lineUnipotentCore G (Submodule.span k {w})) := by
  obtain ⟨u, hu⟩ := exists_notMem_span_singleton hw
  refine IsMulCommutative.of_comm fun x y => ?_
  refine shearHom_injective hw hu ?_
  rw [map_mul, map_mul, mul_comm]

theorem pow_ringChar_eq_one_of_mem_lineUnipotentCore (hw : w ≠ 0)
    (x : lineUnipotentCore G (Submodule.span k {w})) : x ^ ringChar k = 1 := by
  obtain ⟨u, hu⟩ := exists_notMem_span_singleton hw
  refine shearHom_injective hw hu ?_
  rw [map_pow, map_one]
  refine Multiplicative.toAdd.injective ?_
  change Multiplicative.toAdd (shearHom hw hu x ^ ringChar k) = 0
  rw [show Multiplicative.toAdd (shearHom hw hu x ^ ringChar k)
      = ringChar k • Multiplicative.toAdd (shearHom hw hu x) from rfl,
    nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]

theorem card_lineUnipotentCore_dvd [Finite k] (hw : w ≠ 0) :
    Nat.card (lineUnipotentCore G (Submodule.span k {w})) ∣ Nat.card k := by
  obtain ⟨u, hu⟩ := exists_notMem_span_singleton hw
  have h1 : Nat.card (lineUnipotentCore G (Submodule.span k {w})) ∣
      Nat.card (Multiplicative k) :=
    Subgroup.card_dvd_of_injective _ (shearHom_injective hw hu)
  rwa [Nat.card_eq_of_bijective Multiplicative.toAdd Multiplicative.toAdd.bijective] at h1

theorem isPGroup_lineUnipotentCore {p : ℕ} [Fact p.Prime] [CharP k p] (hw : w ≠ 0) :
    IsPGroup p (lineUnipotentCore G (Submodule.span k {w})) := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one, ← (ringChar.eq_iff (R := k) (p := p)).2 inferInstance]
  exact pow_ringChar_eq_one_of_mem_lineUnipotentCore hw x

private theorem not_dvd_natCard_units (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p] :
    ¬ p ∣ Nat.card kˣ := by
  classical
  have := Fintype.ofFinite k
  have hcard : Nat.card kˣ = Nat.card k - 1 := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_units k
  have hp : p ∣ Nat.card k := by
    obtain ⟨n, hnp, hn⟩ := FiniteField.card k p
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p n.ne_zero
  intro hdvd
  rw [hcard] at hdvd
  have hone : p ∣ 1 := by
    have h3 := Nat.dvd_sub hp hdvd
    rwa [Nat.sub_sub_self Nat.card_pos] at h3
  exact (Fact.out (p := p.Prime)).one_lt.not_ge (Nat.le_of_dvd one_pos hone)

theorem not_dvd_index_lineUnipotentCore {p : ℕ} [Fact p.Prime] [Finite k] [CharP k p]
    (hw : w ≠ 0) (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) :
    ¬ p ∣ (lineUnipotentCore G (Submodule.span k {w})).index := by
  obtain ⟨u, hc⟩ := exists_cross_ne_zero hw
  rw [← ker_diagHom hw hc hG, Subgroup.index_ker]
  intro hdvd
  have h1 : Nat.card (diagHom hw hc hG).range ∣ Nat.card (kˣ × kˣ) :=
    Subgroup.card_subgroup_dvd_card _
  have h2 : p ∣ Nat.card (kˣ × kˣ) := hdvd.trans h1
  rw [Nat.card_prod] at h2
  rcases (Nat.Prime.dvd_mul (Fact.out (p := p.Prime))).1 h2 with hd | hd <;>
    exact not_dvd_natCard_units p hd

def lineUnipotentSylow {p : ℕ} [Fact p.Prime] [Finite k] [CharP k p] (hw : w ≠ 0)
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) : Sylow p G :=
  (isPGroup_lineUnipotentCore (G := G) (p := p) hw).toSylow
    (not_dvd_index_lineUnipotentCore hw hG)

@[simp]
theorem coe_lineUnipotentSylow {p : ℕ} [Fact p.Prime] [Finite k] [CharP k p] (hw : w ≠ 0)
    (hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w}) :
    (lineUnipotentSylow (p := p) hw hG : Subgroup G)
      = lineUnipotentCore G (Submodule.span k {w}) :=
  IsPGroup.toSylow_coe _ _

end

end CFSG.FeitThompson
