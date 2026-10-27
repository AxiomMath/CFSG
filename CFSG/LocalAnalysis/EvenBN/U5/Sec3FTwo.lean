module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3F

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open CFSG.EvenSmallLie.UnitarySix.YamadaD (crossed_conj)

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem lev_diag_mem_I₃sub_of_norm {ζ : K} (hζ : ζ ≠ 0) (hn : h.bar ζ * ζ = 1) :
    lev (hK := h) !![ζ, 0; 0, 1] (isUnit_det_diag hζ one_ne_zero) ∈ I₃sub h := by
  obtain ⟨hI, h1, -, h3, -⟩ := lev_diag (h := h) hζ one_ne_zero
  rw [mem_I₃sub]
  refine ⟨hI, ?_⟩
  rw [h1, h3]
  exact eq_inv_of_mul_eq_one_right hn

theorem Yof_lev_diag {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {v : hypSU h 2 1} (hv : v ∈ Vsub h) :
    lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb) * v *
        (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb))⁻¹ ∈ Vsub h ∧
      ∀ i j : Fin 2, Yof (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb) * v *
        (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb))⁻¹) i j =
          ![a, b] i * Yof v i j * h.bar (![a, b] j) := by
  obtain ⟨hmem, hY⟩ := lev_conj_Yof h _ (isUnit_det_diag ha hb) hv
  refine ⟨hmem, fun i j => ?_⟩
  rw [hY]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
theorem r_inv_conj_lev_diag (d : Data G h) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    d.r⁻¹ * d.η (lev (hK := h) !![a, 0; 0, b] (isUnit_det_diag ha hb)) * d.r =
      d.η (lev (hK := h) !![b, 0; 0, a] (isUnit_det_diag hb ha)) := by
  have hrinv : (rSU h)⁻¹ = rSU h := inv_eq_of_mul_eq_one_right rSU_mul_self
  rw [show d.r = d.η (rSU h) from rfl, ← map_inv, ← map_mul, ← map_mul, hrinv]
  congr 1
  conv_rhs => rw [← rSU_conj_lev_diag (h := h) ha hb, hrinv]

omit [Finite G] in
theorem comm_conj_of_comm {r j j' v' : G} (hj : r⁻¹ * j * r = j') (hc : j' * v' = v' * j') :
    j * (r * v' * r⁻¹) = (r * v' * r⁻¹) * j := by
  have e : j = r * j' * r⁻¹ := by rw [← hj]; group
  rw [e]
  calc r * j' * r⁻¹ * (r * v' * r⁻¹) = r * (j' * v') * r⁻¹ := by group
    _ = r * (v' * j') * r⁻¹ := by rw [hc]
    _ = r * v' * r⁻¹ * (r * j' * r⁻¹) := by group

theorem Hyp.comm_V_of_mem_I₃ (hd : d.Hyp) {j : hypSU h 2 1} (hj : j ∈ I₃sub h) {v : G}
    (hv : v ∈ d.V) : d.η j * v = v * d.η j :=
  mem_centralizer_iff.1 (hd.V_le_CB₄I₃ hv).2 _ ⟨j, hj, rfl⟩

theorem Hyp.scale_mem_Zp (hd : d.Hyp) {x : G} (hx : x ∈ d.V) {b₁ b₂ b₃ : h.fixedField}
    (h₁ : (b₁ : K) ≠ 0) (h₂ : (b₂ : K) ≠ 0) (h₃ : (b₃ : K) ≠ 0)
    (hb : b₁ * b₁ + b₂ * b₂ = b₃ * b₃) :
    d.η (lev (hK := h) !![(b₁ : K), 0; 0, 1] (isUnit_det_diag h₁ one_ne_zero)) * x *
        (d.η (lev (hK := h) !![(b₁ : K), 0; 0, 1] (isUnit_det_diag h₁ one_ne_zero)))⁻¹ *
      (d.η (lev (hK := h) !![(b₂ : K), 0; 0, 1] (isUnit_det_diag h₂ one_ne_zero)) * x *
        (d.η (lev (hK := h) !![(b₂ : K), 0; 0, 1] (isUnit_det_diag h₂ one_ne_zero)))⁻¹) *
      (d.η (lev (hK := h) !![(b₃ : K), 0; 0, 1] (isUnit_det_diag h₃ one_ne_zero)) * x *
        (d.η (lev (hK := h) !![(b₃ : K), 0; 0, 1] (isUnit_det_diag h₃ one_ne_zero)))⁻¹)⁻¹ ∈
      d.Zp := by
  have hVB : d.V ≤ d.B₄ := hd.V_le_CB₄I₃.trans d.CB₄I₃_le
  obtain ⟨m, hm⟩ := d.ιZp.surjective ⟨x⁻¹ * d.t * x * d.t, hd.cr_mem (hVB hx)⟩
  set c := Multiplicative.toAdd m with hc
  have hxc : x⁻¹ * d.t * x * d.t = d.ιZp (Multiplicative.ofAdd c) := by
    rw [hc, ofAdd_toAdd, hm]
  have key : ∀ (b : h.fixedField) (hb0 : (b : K) ≠ 0),
      d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * x *
          (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)))⁻¹ ∈ d.V ∧
        (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * x *
          (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)))⁻¹)⁻¹ *
          d.t * (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * x *
          (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)))⁻¹) * d.t =
          d.ιZp (Multiplicative.ofAdd (b * b * c)) := by
    intro b hb0
    obtain ⟨hI, h1, -, h3, -⟩ := lev_diag (h := h) hb0 one_ne_zero
    have hjI : d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) ∈ d.I :=
      ⟨_, hI, rfl⟩
    have hjt := hd.comm_t (d.η_mem (lev (hK := h) !![(b : K), 0; 0, 1]
      (isUnit_det_diag hb0 one_ne_zero)))
    refine ⟨(mem_normalizer_iff.1 (hd.I_le_normalizer_V hjI) x).1 hx, ?_⟩
    rw [crossed_conj hjt, hxc]
    refine d.conj_ιZp_torus hI h1 ?_ c
    rw [h3, (h.mem_fixedField.1 b.2)]
  obtain ⟨hx₁, e₁⟩ := key b₁ h₁
  obtain ⟨hx₂, e₂⟩ := key b₂ h₂
  obtain ⟨hx₃, e₃⟩ := key b₃ h₃
  set x₁ := d.η (lev (hK := h) !![(b₁ : K), 0; 0, 1] (isUnit_det_diag h₁ one_ne_zero)) * x *
    (d.η (lev (hK := h) !![(b₁ : K), 0; 0, 1] (isUnit_det_diag h₁ one_ne_zero)))⁻¹
  set x₂ := d.η (lev (hK := h) !![(b₂ : K), 0; 0, 1] (isUnit_det_diag h₂ one_ne_zero)) * x *
    (d.η (lev (hK := h) !![(b₂ : K), 0; 0, 1] (isUnit_det_diag h₂ one_ne_zero)))⁻¹
  set x₃ := d.η (lev (hK := h) !![(b₃ : K), 0; 0, 1] (isUnit_det_diag h₃ one_ne_zero)) * x *
    (d.η (lev (hK := h) !![(b₃ : K), 0; 0, 1] (isUnit_det_diag h₃ one_ne_zero)))⁻¹
  have hX : x₁ * x₂ * x₃⁻¹ ∈ d.V := mul_mem (mul_mem hx₁ hx₂) (inv_mem hx₃)
  have hcr : (x₁ * x₂ * x₃⁻¹)⁻¹ * d.t * (x₁ * x₂ * x₃⁻¹) * d.t = 1 := by
    rw [hd.cr_mul (mul_mem (hVB hx₁) (hVB hx₂)) (inv_mem (hVB hx₃)), hd.cr_mul (hVB hx₁) (hVB hx₂),
      hd.cr_inv (hVB hx₃), e₁, e₂, e₃, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add,
      d.coe_ιZp_mul_inv]
    have e0 : b₁ * b₁ * c + b₂ * b₂ * c - b₃ * b₃ * c = 0 := by
      linear_combination c * hb
    rw [e0, ofAdd_zero, map_one, Subgroup.coe_one]
  rw [← hd.V_inf_B₂]
  exact Subgroup.mem_inf.2 ⟨hX, (hd.cr_eq_one_iff (hVB hX)).1 hcr⟩

theorem Hyp.commutator_mem_F (hd : d.Hyp) {x y : G} (hx : x ∈ d.F) (hy : y ∈ d.F) :
    x * y * x⁻¹ * y⁻¹ ∈ d.A₁ :=
  hd.commutator_mem_A₁ (hd.F_le_B₅ hx) (hd.F_le_centralizer_A₃ hx) (hd.F_le_B₅ hy)
    (hd.F_le_centralizer_A₃ hy)

theorem Hyp.comm_mul_right (hd : d.Hyp) {x y y' : G} (hx : x ∈ d.F) (hy : y ∈ d.F)
    (hy' : y' ∈ d.F) :
    x * (y * y') * x⁻¹ * (y * y')⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * y' * x⁻¹ * y'⁻¹) := by
  have h1 := hd.commutator_mem_F hx hy'
  have h2 : (x * y' * x⁻¹ * y'⁻¹) * y = y * (x * y' * x⁻¹ * y'⁻¹) :=
    mem_centralizer_iff.1 (hd.F_le_centralizer_A₁ hy) _ h1
  calc x * (y * y') * x⁻¹ * (y * y')⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹)) * y⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * ((x * y' * x⁻¹ * y'⁻¹) * y) * y⁻¹ := by rw [h2]
    _ = (x * y * x⁻¹ * y⁻¹) * (x * y' * x⁻¹ * y'⁻¹) := by group

theorem Hyp.comm_mul_left (hd : d.Hyp) {x x' y : G} (hx : x ∈ d.F) (hx' : x' ∈ d.F)
    (hy : y ∈ d.F) :
    (x * x') * y * (x * x')⁻¹ * y⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x' * y * x'⁻¹ * y⁻¹) := by
  have h1 := hd.commutator_mem_F hx' hy
  have h2 : (x' * y * x'⁻¹ * y⁻¹) * x = x * (x' * y * x'⁻¹ * y⁻¹) :=
    mem_centralizer_iff.1 (hd.F_le_centralizer_A₁ hx) _ h1
  have h3 := d.A₁_comm_sq.1 _ h1 _ (hd.commutator_mem_F hx hy)
  calc (x * x') * y * (x * x')⁻¹ * y⁻¹ =
        (x * (x' * y * x'⁻¹ * y⁻¹)) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    _ = ((x' * y * x'⁻¹ * y⁻¹) * x) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by rw [h2]
    _ = (x' * y * x'⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    _ = (x * y * x⁻¹ * y⁻¹) * (x' * y * x'⁻¹ * y⁻¹) := h3

theorem Hyp.comm_mul_comm_right (hd : d.Hyp) {x y₁ y₂ y₃ : G} (hx : x ∈ d.F) (h₁ : y₁ ∈ d.F)
    (h₂ : y₂ ∈ d.F) (h₃ : y₃ ∈ d.F) (hy : y₁ * y₂ * y₃⁻¹ ∈ d.A₁) :
    (x * y₁ * x⁻¹ * y₁⁻¹) * (x * y₂ * x⁻¹ * y₂⁻¹) = x * y₃ * x⁻¹ * y₃⁻¹ := by
  have hz : x * (y₁ * y₂ * y₃⁻¹) * x⁻¹ * (y₁ * y₂ * y₃⁻¹)⁻¹ = 1 := by
    rw [(mem_centralizer_iff.1 (hd.F_le_centralizer_A₁ hx) _ hy).symm]
    group
  have hF : y₁ * y₂ * y₃⁻¹ ∈ d.F := hd.A₁_le_F hy
  have e := hd.comm_mul_right hx hF h₃
  rw [show y₁ * y₂ * y₃⁻¹ * y₃ = y₁ * y₂ by group, hz, one_mul] at e
  rw [← hd.comm_mul_right hx h₁ h₂, e]

theorem Hyp.comm_mul_comm_left (hd : d.Hyp) {x₁ x₂ x₃ y : G} (h₁ : x₁ ∈ d.F) (h₂ : x₂ ∈ d.F)
    (h₃ : x₃ ∈ d.F) (hy : y ∈ d.F) (hx : x₁ * x₂ * x₃⁻¹ ∈ d.A₁) :
    (x₁ * y * x₁⁻¹ * y⁻¹) * (x₂ * y * x₂⁻¹ * y⁻¹) = x₃ * y * x₃⁻¹ * y⁻¹ := by
  have hz : (x₁ * x₂ * x₃⁻¹) * y * (x₁ * x₂ * x₃⁻¹)⁻¹ * y⁻¹ = 1 := by
    rw [mem_centralizer_iff.1 (hd.F_le_centralizer_A₁ hy) _ hx]
    group
  have hF : x₁ * x₂ * x₃⁻¹ ∈ d.F := hd.A₁_le_F hx
  have e := hd.comm_mul_left hF h₃ hy
  rw [show x₁ * x₂ * x₃⁻¹ * x₃ = x₁ * x₂ by group, hz, one_mul] at e
  rw [← hd.comm_mul_left h₁ h₂ hy, e]

omit [Finite G] in
theorem Yof_add_of_η_mul (d : Data G h) {m₁ m₂ m₃ : hypSU h 2 1} (h₁ : m₁ ∈ Vsub h)
    (h₂ : m₂ ∈ Vsub h) (h₃ : m₃ ∈ Vsub h) (e : d.η m₁ * d.η m₂ = d.η m₃) :
    Yof m₁ + Yof m₂ = Yof m₃ := by
  rw [← map_mul] at e
  rw [← Yof_mul h₁ h₂, d.η_injOn (Vsub_le_Ssub.trans Ssub_le_Usub (mul_mem h₁ h₂))
    (Vsub_le_Ssub.trans Ssub_le_Usub h₃) e]

theorem Hyp.comm_V_conj_r (hd : d.Hyp) {v v' : G} (hv : v ∈ d.V) (hv' : v' ∈ d.V) :
    v * (d.r * v' * d.r⁻¹) = (d.r * v' * d.r⁻¹) * v := by
  have := h.charP
  have := finite_fixedField h
  have := charP_fixedField h
  set w := d.r * v' * d.r⁻¹ with hw
  have hvF : v ∈ d.F := d.V_le_F hv
  have hwF : w ∈ d.F := conj_mem_F d.r_mem_N₁ hv'
  set c := v * w * v⁻¹ * w⁻¹ with hc
  have hcA : c ∈ d.A₁ := hd.commutator_mem_F hvF hwF
  suffices hc1 : c = 1 by
    calc v * w = c * (w * v) := by rw [hc]; group
      _ = w * v := by rw [hc1, one_mul]
  obtain ⟨g, hg, hgc⟩ := hcA
  have hK2 : 2 < Nat.card h.fixedField := by
    rw [h.card_fixedField]
    have := hd.four_le
    omega
  obtain ⟨β, hβ0, hβ1⟩ := exists_ne_zero_ne_one hK2
  have hβ1' : (1 : h.fixedField) + β ≠ 0 := fun e => hβ1 (by
    have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
    linear_combination e - h2)
  have hb : (1 : h.fixedField) * 1 + β * β = (1 + β) * (1 + β) := by
    have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
    linear_combination (-β) * h2
  have hK : ∀ b : h.fixedField, b ≠ 0 → (b : K) ≠ 0 := fun b hb0 e => hb0 (Subtype.ext e)
  have h₁ : ((1 : h.fixedField) : K) ≠ 0 := hK 1 one_ne_zero
  have h₂ : (β : K) ≠ 0 := hK β hβ0
  have h₃ : ((1 + β : h.fixedField) : K) ≠ 0 := hK _ hβ1'
  have hrA : d.r ∈ normalizer (d.A₁ : Set G) :=
    hd.normalizer_B₁_le_normalizer_A₁ (hd.N₁_le d.r_mem_N₁).1
  have hY₀₀ : Yof g 0 0 = 0 := by
    have hS := hd.scale_mem_Zp hv' h₁ h₂ h₃ hb
    have key : ∀ (b : h.fixedField) (hb0 : (b : K) ≠ 0),
        d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)) * w *
            (d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)))⁻¹ =
          d.r * (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * v' *
            (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)))⁻¹) *
            d.r⁻¹ := by
      intro b hb0
      have e := d.r_inv_conj_lev_diag (h := h) one_ne_zero hb0
      rw [← e, hw]
      group
    have hconj : ∀ (b : h.fixedField) (hb0 : (b : K) ≠ 0),
        v * (d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)) * w *
            (d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)))⁻¹) *
          v⁻¹ * (d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)) * w *
            (d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)))⁻¹)⁻¹ =
          d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0) * g *
            (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0))⁻¹) := by
      intro b hb0
      have hjv := hd.comm_V_of_mem_I₃ (lev_diag_mem_I₃sub hb0) hv
      rw [map_mul, map_mul, map_inv, hgc, hc]
      set j := d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0))
      calc v * (j * w * j⁻¹) * v⁻¹ * (j * w * j⁻¹)⁻¹ =
            (v * j) * w * (v * j)⁻¹ * (j * w⁻¹ * j⁻¹) := by group
        _ = (j * v) * w * (j * v)⁻¹ * (j * w⁻¹ * j⁻¹) := by rw [hjv]
        _ = j * (v * w * v⁻¹ * w⁻¹) * j⁻¹ := by group
    have hwk : ∀ (b : h.fixedField) (hb0 : (b : K) ≠ 0),
        d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)) * w *
          (d.η (lev (hK := h) !![1, 0; 0, (b : K)] (isUnit_det_diag one_ne_zero hb0)))⁻¹ ∈ d.F :=
      fun b hb0 => by
        rw [key b hb0]
        exact conj_mem_F d.r_mem_N₁ ((mem_normalizer_iff.1 (hd.I_le_normalizer_V
          ⟨_, (lev_diag (h := h) hb0 one_ne_zero).1, rfl⟩) v').1 hv')
    have hprod : (d.η (lev (hK := h) !![1, 0; 0, ((1 : h.fixedField) : K)]
          (isUnit_det_diag one_ne_zero h₁)) * w * (d.η (lev (hK := h)
          !![1, 0; 0, ((1 : h.fixedField) : K)] (isUnit_det_diag one_ne_zero h₁)))⁻¹) *
        (d.η (lev (hK := h) !![1, 0; 0, (β : K)] (isUnit_det_diag one_ne_zero h₂)) * w *
          (d.η (lev (hK := h) !![1, 0; 0, (β : K)] (isUnit_det_diag one_ne_zero h₂)))⁻¹) *
        (d.η (lev (hK := h) !![1, 0; 0, ((1 + β : h.fixedField) : K)]
          (isUnit_det_diag one_ne_zero h₃)) * w * (d.η (lev (hK := h)
          !![1, 0; 0, ((1 + β : h.fixedField) : K)] (isUnit_det_diag one_ne_zero h₃)))⁻¹)⁻¹ ∈
        d.A₁ := by
      rw [key _ h₁, key _ h₂, key _ h₃]
      have e : ∀ a b' c' : G, d.r * a * d.r⁻¹ * (d.r * b' * d.r⁻¹) * (d.r * c' * d.r⁻¹)⁻¹ =
          d.r * (a * b' * c'⁻¹) * d.r⁻¹ := fun a b' c' => by group
      rw [e]
      exact (mem_normalizer_iff.1 hrA _).1 (d.Zp_le_A₁ hS)
    have hid := hd.comm_mul_comm_right hvF (hwk _ h₁) (hwk _ h₂) (hwk _ h₃) hprod
    rw [hconj _ h₁, hconj _ h₂, hconj _ h₃] at hid
    obtain ⟨hm₁, hY₁⟩ := Yof_lev_diag (h := h) one_ne_zero h₁ hg
    obtain ⟨hm₂, hY₂⟩ := Yof_lev_diag (h := h) one_ne_zero h₂ hg
    obtain ⟨hm₃, hY₃⟩ := Yof_lev_diag (h := h) one_ne_zero h₃ hg
    have e := congrFun (congrFun (d.Yof_add_of_η_mul hm₁ hm₂ hm₃ hid) 0) 0
    rw [Matrix.add_apply, hY₁, hY₂, hY₃] at e
    simp only [Matrix.cons_val_zero, one_mul, map_one, mul_one] at e
    linear_combination e
  have hY₁₁ : Yof g 1 1 = 0 := by
    have hS := hd.scale_mem_Zp hv h₁ h₂ h₃ hb
    have hjw : ∀ (b : h.fixedField) (hb0 : (b : K) ≠ 0),
        d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * w =
          w * d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) :=
      fun b hb0 => comm_conj_of_comm (d.r_inv_conj_lev_diag (h := h) hb0 one_ne_zero)
        (hd.comm_V_of_mem_I₃ (lev_diag_mem_I₃sub hb0) hv')
    have hconj : ∀ (b : h.fixedField) (hb0 : (b : K) ≠ 0),
        (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * v *
            (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)))⁻¹) * w *
          (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * v *
            (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)))⁻¹)⁻¹ *
          w⁻¹ = d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero) * g *
            (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero))⁻¹) := by
      intro b hb0
      have hj := hjw b hb0
      rw [map_mul, map_mul, map_inv, hgc, hc]
      set j := d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero))
      have hj1 : j⁻¹ * w * j = w := by rw [mul_assoc, ← hj, inv_mul_cancel_left]
      have hj2 : j⁻¹ * w⁻¹ = w⁻¹ * j⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hj]
      calc j * v * j⁻¹ * w * (j * v * j⁻¹)⁻¹ * w⁻¹ =
            j * v * (j⁻¹ * w * j) * v⁻¹ * (j⁻¹ * w⁻¹) := by group
        _ = j * v * w * v⁻¹ * (w⁻¹ * j⁻¹) := by rw [hj1, hj2]
        _ = j * (v * w * v⁻¹ * w⁻¹) * j⁻¹ := by group
    have hvk : ∀ (b : h.fixedField) (hb0 : (b : K) ≠ 0),
        d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)) * v *
          (d.η (lev (hK := h) !![(b : K), 0; 0, 1] (isUnit_det_diag hb0 one_ne_zero)))⁻¹ ∈ d.F :=
      fun b hb0 => d.V_le_F ((mem_normalizer_iff.1 (hd.I_le_normalizer_V
        ⟨_, (lev_diag (h := h) hb0 one_ne_zero).1, rfl⟩) v).1 hv)
    have hid := hd.comm_mul_comm_left (hvk _ h₁) (hvk _ h₂) (hvk _ h₃) hwF (d.Zp_le_A₁ hS)
    rw [hconj _ h₁, hconj _ h₂, hconj _ h₃] at hid
    obtain ⟨hm₁, hY₁⟩ := Yof_lev_diag (h := h) h₁ one_ne_zero hg
    obtain ⟨hm₂, hY₂⟩ := Yof_lev_diag (h := h) h₂ one_ne_zero hg
    obtain ⟨hm₃, hY₃⟩ := Yof_lev_diag (h := h) h₃ one_ne_zero hg
    have e := congrFun (congrFun (d.Yof_add_of_η_mul hm₁ hm₂ hm₃ hid) 1) 1
    rw [Matrix.add_apply, hY₁, hY₂, hY₃] at e
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, map_one, mul_one] at e
    linear_combination e
  have hY₀₁ : Yof g 0 1 = 0 := by
    obtain ⟨ζ, hζ0, hζn, hζ1⟩ := exists_norm_one_ne_one h
    have hjv := hd.comm_V_of_mem_I₃ (lev_diag_mem_I₃sub hζ0) hv
    have hjw := comm_conj_of_comm (d.r_inv_conj_lev_diag (h := h) one_ne_zero hζ0)
      (hd.comm_V_of_mem_I₃ (lev_diag_mem_I₃sub_of_norm hζ0 hζn) hv')
    rw [← hw] at hjw
    set j := d.η (lev (hK := h) !![1, 0; 0, ζ] (isUnit_det_diag one_ne_zero hζ0)) with hj
    have hfix : j * c * j⁻¹ = c := by
      rw [hc]
      calc j * (v * w * v⁻¹ * w⁻¹) * j⁻¹ = (j * v) * w * v⁻¹ * w⁻¹ * j⁻¹ := by group
        _ = v * (j * w) * v⁻¹ * w⁻¹ * j⁻¹ := by rw [hjv]; group
        _ = v * w * (j * v⁻¹) * w⁻¹ * j⁻¹ := by rw [hjw]; group
        _ = v * w * v⁻¹ * (j * w⁻¹) * j⁻¹ := by
            rw [show j * v⁻¹ = v⁻¹ * j by
              calc j * v⁻¹ = v⁻¹ * (v * j) * v⁻¹ := by group
                _ = v⁻¹ * (j * v) * v⁻¹ := by rw [hjv]
                _ = v⁻¹ * j := by group]
            group
        _ = v * w * v⁻¹ * w⁻¹ := by
            rw [show j * w⁻¹ = w⁻¹ * j by
              calc j * w⁻¹ = w⁻¹ * (w * j) * w⁻¹ := by group
                _ = w⁻¹ * (j * w) * w⁻¹ := by rw [hjw]
                _ = w⁻¹ * j := by group]
            group
    obtain ⟨hm, hY⟩ := Yof_lev_diag (h := h) one_ne_zero hζ0 hg
    have e : lev (hK := h) !![1, 0; 0, ζ] (isUnit_det_diag one_ne_zero hζ0) * g *
        (lev (hK := h) !![1, 0; 0, ζ] (isUnit_det_diag one_ne_zero hζ0))⁻¹ = g :=
      d.η_injOn (Vsub_le_Ssub.trans Ssub_le_Usub hm) (Vsub_le_Ssub.trans Ssub_le_Usub hg)
        (by rw [map_mul, map_mul, map_inv, hgc, ← hj, hfix])
    have e01 := hY 0 1
    rw [e] at e01
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul] at e01
    have hbζ : h.bar ζ ≠ 1 := fun e1 => hζ1 (by
      have := congrArg h.bar e1
      rwa [h.bar_bar, map_one] at this)
    have e2 : Yof g 0 1 * (h.bar ζ - 1) = 0 := by linear_combination -e01
    exact (mul_eq_zero.1 e2).resolve_right (sub_ne_zero.2 hbζ)
  have hg1 : g = 1 := by
    have h0 := (eq_one_iff_Yof_eq_zero h (one_mem (Vsub h))).1 rfl
    exact Yof_ext hg (one_mem _) (by rw [hY₀₀, h0]; rfl) (by rw [hY₀₁, h0]; rfl)
      (by rw [hY₁₁, h0]; rfl)
  rw [← hgc, hg1, map_one]

theorem Hyp.conj_N₁_V (hd : d.Hyp) {n v : G} (hn : n ∈ d.N₁) (hv : v ∈ d.V) :
    n * v * n⁻¹ ∈ d.V ∨ ∃ p ∈ d.P, ∃ v'' ∈ d.V, n * v * n⁻¹ = p * (d.r * v'' * d.r⁻¹) * p⁻¹ := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hn
  have hPV : ∀ p ∈ d.P, ∀ x ∈ d.V, p * x * p⁻¹ = x := fun p hp x hx => by
    rw [mem_centralizer_iff.1 (hd.CB₄I₃_le_centralizer_P (hd.V_le_CB₄I₃ hx)) p hp,
      mul_inv_cancel_right]
  rcases leviSU_bruhat (h := h) A with ⟨p, hp, j, hj, e⟩ | ⟨p, hp, p', hp', j, hj, e⟩
  · left
    have hjv : d.η j * v * (d.η j)⁻¹ ∈ d.V :=
      (mem_normalizer_iff.1 (hd.I_le_normalizer_V ⟨j, hj, rfl⟩) v).1 hv
    rw [e, map_mul, show d.η p * d.η j * v * (d.η p * d.η j)⁻¹ =
      d.η p * (d.η j * v * (d.η j)⁻¹) * (d.η p)⁻¹ by group, hPV _ ⟨p, hp, rfl⟩ _ hjv]
    exact hjv
  · right
    have hjv : d.η j * v * (d.η j)⁻¹ ∈ d.V :=
      (mem_normalizer_iff.1 (hd.I_le_normalizer_V ⟨j, hj, rfl⟩) v).1 hv
    refine ⟨d.η p, ⟨p, hp, rfl⟩, _, hjv, ?_⟩
    rw [e, map_mul, map_mul, map_mul, show d.η (rSU h) = d.r from rfl,
      show d.η p * d.r * d.η p' * d.η j * v * (d.η p * d.r * d.η p' * d.η j)⁻¹ =
        d.η p * (d.r * (d.η p' * (d.η j * v * (d.η j)⁻¹) * (d.η p')⁻¹) * d.r⁻¹) * (d.η p)⁻¹ by
      group, hPV _ ⟨p', hp', rfl⟩ _ hjv]

theorem Hyp.comm_V_conj_N₁ (hd : d.Hyp) (hVc : ∀ x ∈ d.V, ∀ y ∈ d.V, x * y = y * x)
    {v₁ n v : G} (hv₁ : v₁ ∈ d.V) (hn : n ∈ d.N₁) (hv : v ∈ d.V) :
    v₁ * (n * v * n⁻¹) = (n * v * n⁻¹) * v₁ := by
  rcases hd.conj_N₁_V hn hv with h1 | ⟨p, hp, v'', hv'', e⟩
  · exact hVc _ hv₁ _ h1
  · rw [e]
    have hpv : p * v₁ = v₁ * p := mem_centralizer_iff.1
      (hd.CB₄I₃_le_centralizer_P (hd.V_le_CB₄I₃ hv₁)) p hp
    have hc := hd.comm_V_conj_r hv₁ hv''
    have hpinv : p⁻¹ * v₁ = v₁ * p⁻¹ := by
      calc p⁻¹ * v₁ = p⁻¹ * (v₁ * p) * p⁻¹ := by group
        _ = p⁻¹ * (p * v₁) * p⁻¹ := by rw [hpv]
        _ = v₁ * p⁻¹ := by group
    calc v₁ * (p * (d.r * v'' * d.r⁻¹) * p⁻¹) = p * (v₁ * (d.r * v'' * d.r⁻¹)) * p⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, ← hpv]; group
      _ = p * ((d.r * v'' * d.r⁻¹) * v₁) * p⁻¹ := by rw [hc]
      _ = p * (d.r * v'' * d.r⁻¹) * p⁻¹ * v₁ := by
          rw [show p * (d.r * v'' * d.r⁻¹ * v₁) * p⁻¹ = p * (d.r * v'' * d.r⁻¹) * (v₁ * p⁻¹) by
            group, ← hpinv]
          group

theorem Hyp.F_comm_of (hd : d.Hyp) (hVc : ∀ x ∈ d.V, ∀ y ∈ d.V, x * y = y * x) :
    ∀ x ∈ d.F, ∀ y ∈ d.F, x * y = y * x := by
  set S : Set G := {x | ∃ n ∈ d.N₁, ∃ v ∈ d.V, x = n * v * n⁻¹} with hS
  have hSS : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := by
    rintro _ ⟨n₁, hn₁, v₁, hv₁, rfl⟩ _ ⟨n₂, hn₂, v₂, hv₂, rfl⟩
    have e := hd.comm_V_conj_N₁ hVc hv₁ (mul_mem (inv_mem hn₁) hn₂) hv₂
    calc n₁ * v₁ * n₁⁻¹ * (n₂ * v₂ * n₂⁻¹) =
          n₁ * (v₁ * (n₁⁻¹ * n₂ * v₂ * (n₁⁻¹ * n₂)⁻¹)) * n₁⁻¹ := by group
      _ = n₁ * ((n₁⁻¹ * n₂ * v₂ * (n₁⁻¹ * n₂)⁻¹) * v₁) * n₁⁻¹ := by rw [e]
      _ = n₂ * v₂ * n₂⁻¹ * (n₁ * v₁ * n₁⁻¹) := by group
  have h1 : d.F ≤ centralizer S := (closure_le _).2 fun s hs =>
    mem_centralizer_iff.2 fun s' hs' => hSS s' hs' s hs
  have h2 : d.F ≤ centralizer (d.F : Set G) := (closure_le _).2 fun s hs =>
    mem_centralizer_iff.2 fun x hx => ((mem_centralizer_iff.1 (h1 hx)) s hs).symm
  intro x hx y hy
  exact mem_centralizer_iff.1 (h2 hy) x hx

theorem Hyp.isElementaryAbelian_F_of (hd : d.Hyp) (hVc : ∀ x ∈ d.V, ∀ y ∈ d.V, x * y = y * x)
    (hVsq : ∀ x ∈ d.V, x * x = 1) : CFSG.IsElementaryAbelian 2 d.F := by
  have hFc := hd.F_comm_of hVc
  refine isElementaryAbelian_of_forall hFc fun x hx => ?_
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨n, -, v, hv, rfl⟩ := hx
    calc n * v * n⁻¹ * (n * v * n⁻¹) = n * (v * v) * n⁻¹ := by group
      _ = 1 := by rw [hVsq v hv]; group
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hFc y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [← mul_inv_rev, ihx, inv_one]

end Data

end CFSG.LocalAnalysis.EvenBN.U5
