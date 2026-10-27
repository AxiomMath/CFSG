module

public import CFSG.ClassicalInvolution.ModelFacts.MF15Basic
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Mat
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

open QuadraticMap CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts.MF15 CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (two_ne_zero_of_odd_card)
open scoped MatrixGroups

namespace C25X

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure Ortho4 (Q : QuadraticForm F V) (a b c d : V) : Prop where
  qa : Q a = 1
  qb : Q b = 1
  qc : Q c = 1
  qd : Q d = 1
  ab : polar Q a b = 0
  ac : polar Q a c = 0
  ad : polar Q a d = 0
  bc : polar Q b c = 0
  bd : polar Q b d = 0
  cd : polar Q c d = 0

variable {a b c d : V}

theorem Ortho4.polar_comb (h : Ortho4 Q a b c d) (α β γ δ α' β' γ' δ' : F) :
    polar Q (α • a + β • b + γ • c + δ • d) (α' • a + β' • b + γ' • c + δ' • d) =
      2 * (α * α' + β * β' + γ * γ' + δ * δ') := by
  have h2a : polar Q a a = 2 := by rw [polar_self_eq_two_mul, h.qa]; ring
  have h2b : polar Q b b = 2 := by rw [polar_self_eq_two_mul, h.qb]; ring
  have h2c : polar Q c c = 2 := by rw [polar_self_eq_two_mul, h.qc]; ring
  have h2d : polar Q d d = 2 := by rw [polar_self_eq_two_mul, h.qd]; ring
  have hba : polar Q b a = 0 := by rw [polar_comm]; exact h.ab
  have hca : polar Q c a = 0 := by rw [polar_comm]; exact h.ac
  have hda : polar Q d a = 0 := by rw [polar_comm]; exact h.ad
  have hcb : polar Q c b = 0 := by rw [polar_comm]; exact h.bc
  have hdb : polar Q d b = 0 := by rw [polar_comm]; exact h.bd
  have hdc : polar Q d c = 0 := by rw [polar_comm]; exact h.cd
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h2a, h2b,
    h2c, h2d, hba, hca, hda, hcb, hdb, hdc, h.ab, h.ac, h.ad, h.bc, h.bd, h.cd]
  ring

theorem Ortho4.Q_comb (h2 : (2 : F) ≠ 0) (h : Ortho4 Q a b c d) (α β γ δ : F) :
    Q (α • a + β • b + γ • c + δ • d) = α * α + β * β + γ * γ + δ * δ := by
  have := h.polar_comb α β γ δ α β γ δ
  rw [polar_self_eq_two_mul] at this
  have h3 : (2 : F) *
      (Q (α • a + β • b + γ • c + δ • d) - (α * α + β * β + γ * γ + δ * δ)) = 0 := by
    linear_combination this
  have := (mul_eq_zero.mp h3).resolve_left h2
  linear_combination this

@[expose] noncomputable def orthoFrame (x y : F) (h2 : (2 : F) ≠ 0) (hxy : x * x + y * y = -1)
    (h : Ortho4 Q a b c d) : Frame Q :=
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have ht : (4 : F)⁻¹ * 4 = 1 := inv_mul_cancel₀ h4
  frameOfVectors ((1 : F) • a + (0 : F) • b + x • c + y • d)
    ((4 : F)⁻¹ • a + (0 : F) • b + (-(4 : F)⁻¹ * x) • c + (-(4 : F)⁻¹ * y) • d)
    ((0 : F) • a + (-(4 : F)⁻¹) • b + (-(4 : F)⁻¹ * y) • c + ((4 : F)⁻¹ * x) • d)
    ((0 : F) • a + (-1 : F) • b + y • c + (-x) • d)
    (by rw [h.Q_comb h2]; linear_combination hxy)
    (by rw [h.Q_comb h2]; linear_combination ((4 : F)⁻¹ * (4 : F)⁻¹) * hxy)
    (by rw [h.polar_comb]; linear_combination ht - (2 * (4 : F)⁻¹) * hxy)
    (by rw [h.Q_comb h2]; linear_combination ((4 : F)⁻¹ * (4 : F)⁻¹) * hxy)
    (by rw [h.Q_comb h2]; linear_combination hxy)
    (by rw [h.polar_comb]; linear_combination ht - (2 * (4 : F)⁻¹) * hxy)
    (by rw [h.polar_comb]; ring)
    (by rw [h.polar_comb]; ring)
    (by rw [h.polar_comb]; ring)
    (by rw [h.polar_comb]; ring)

section LaFacts

variable {x y : F} {h2 : (2 : F) ≠ 0} {hxy : x * x + y * y = -1} {h : Ortho4 Q a b c d}

theorem orthoFrame_incl (X : Matrix (Fin 2) (Fin 2) F) :
    (orthoFrame x y h2 hxy h).incl X =
      X 0 0 • ((1 : F) • a + (0 : F) • b + x • c + y • d) +
      X 1 1 • ((4 : F)⁻¹ • a + (0 : F) • b + (-(4 : F)⁻¹ * x) • c + (-(4 : F)⁻¹ * y) • d) +
      (-X 0 1) • ((0 : F) • a + (-(4 : F)⁻¹) • b + (-(4 : F)⁻¹ * y) • c + ((4 : F)⁻¹ * x) • d) +
      X 1 0 • ((0 : F) • a + (-1 : F) • b + y • c + (-x) • d) := rfl

theorem four_ne_zero' (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  have : (4 : F) = 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero h2 h2

theorem orthoFrame_incl_a :
    (orthoFrame x y h2 hxy h).incl !![2 * (4 : F)⁻¹, 0; 0, 2] = a := by
  have h4 := four_ne_zero' h2
  rw [orthoFrame_incl]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, neg_zero, zero_smul, add_zero]
  match_scalars
  all_goals field_simp
  all_goals ring

theorem orthoFrame_incl_b :
    (orthoFrame x y h2 hxy h).incl !![0, 2; -(2 * (4 : F)⁻¹), 0] = b := by
  have h4 := four_ne_zero' h2
  rw [orthoFrame_incl]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, zero_smul, add_zero, zero_add]
  match_scalars
  all_goals field_simp
  all_goals ring

theorem orthoFrame_incl_c :
    (orthoFrame x y h2 hxy h).incl !![-(2 * (4 : F)⁻¹ * x), -(2 * y); -(2 * (4 : F)⁻¹ * y), 2 * x]
      = c := by
  have h4 := four_ne_zero' h2
  rw [orthoFrame_incl]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, neg_neg]
  match_scalars
  all_goals field_simp
  all_goals first | ring1 | linear_combination (-4) * hxy

theorem orthoFrame_incl_d :
    (orthoFrame x y h2 hxy h).incl !![-(2 * (4 : F)⁻¹ * y), 2 * x; 2 * (4 : F)⁻¹ * x, 2 * y]
      = d := by
  have h4 := four_ne_zero' h2
  rw [orthoFrame_incl]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  match_scalars
  all_goals field_simp
  all_goals first | ring1 | linear_combination (-4) * hxy

theorem orthoFrame_La_a :
    (orthoFrame x y h2 hxy h).La r0 a = b := by
  have e1 := orthoFrame_incl_a (h2 := h2) (hxy := hxy) (h := h)
  have e2 := orthoFrame_incl_b (h2 := h2) (hxy := hxy) (h := h)
  generalize orthoFrame x y h2 hxy h = fr at e1 e2 ⊢
  rw [← e1, Frame.La_apply_incl, ← e2]
  congr 1
  rw [coe_r0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem orthoFrame_La_b :
    (orthoFrame x y h2 hxy h).La r0 b = -a := by
  have e1 := orthoFrame_incl_a (h2 := h2) (hxy := hxy) (h := h)
  have e2 := orthoFrame_incl_b (h2 := h2) (hxy := hxy) (h := h)
  generalize orthoFrame x y h2 hxy h = fr at e1 e2 ⊢
  rw [← e2, Frame.La_apply_incl, ← e1, ← map_neg]
  congr 1
  rw [coe_r0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem orthoFrame_La_c :
    (orthoFrame x y h2 hxy h).La r0 c = d := by
  have e1 := orthoFrame_incl_c (h2 := h2) (hxy := hxy) (h := h)
  have e2 := orthoFrame_incl_d (h2 := h2) (hxy := hxy) (h := h)
  generalize orthoFrame x y h2 hxy h = fr at e1 e2 ⊢
  rw [← e1, Frame.La_apply_incl, ← e2]
  congr 1
  rw [coe_r0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem orthoFrame_La_d :
    (orthoFrame x y h2 hxy h).La r0 d = -c := by
  have e1 := orthoFrame_incl_c (h2 := h2) (hxy := hxy) (h := h)
  have e2 := orthoFrame_incl_d (h2 := h2) (hxy := hxy) (h := h)
  generalize orthoFrame x y h2 hxy h = fr at e1 e2 ⊢
  rw [← e2, Frame.La_apply_incl, ← e1, ← map_neg]
  congr 1
  rw [coe_r0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem orthoFrame_coords_perp {u : V} (hua : polar Q u a = 0) (hub : polar Q u b = 0)
    (huc : polar Q u c = 0) (hud : polar Q u d = 0) :
    (orthoFrame x y h2 hxy h).coords u = 0 := by
  rw [Frame.coords_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthoFrame, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, polar_add_right,
      hua, hub, huc, hud]

theorem orthoFrame_La_perp {u : V} (hua : polar Q u a = 0) (hub : polar Q u b = 0)
    (huc : polar Q u c = 0) (hud : polar Q u d = 0) (B : SL(2, F)) :
    (orthoFrame x y h2 hxy h).La B u = u :=
  Frame.La_apply_of_coords_eq_zero _ B (orthoFrame_coords_perp hua hub huc hud)

end LaFacts

section Orthonormal

variable [Finite F] [FiniteDimensional F V]

theorem exists_unit_split (hodd : Odd (Nat.card F)) {U : Submodule F V} (hU : PolarNondegOn Q U)
    (h2 : 2 ≤ Module.finrank F U) :
    ∃ v ∈ U, Q v = 1 ∧ ∃ U' : Submodule F V, U' ≤ U ∧ (∀ x ∈ U', polar Q v x = 0) ∧
      PolarNondegOn Q U' ∧ Module.finrank F U ≤ Module.finrank F U' + 1 := by
  have h2' : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  let _ : Invertible (2 : F) := invertibleOfNonzero h2'
  obtain ⟨v, hvU, hvQ⟩ : ∃ v ∈ U, Q v = (1 : Fˣ) :=
    exists_mem_eq_unit hodd (QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict hU)) h2 1
  rw [Units.val_one] at hvQ
  have hvv : polar Q v v = 2 := by rw [polar_self_eq_two_mul, hvQ]; ring
  let φ : U →ₗ[F] F := (polarBilin Q v).domRestrict U
  let U' : Submodule F V := (LinearMap.ker φ).map U.subtype
  have hmem : ∀ x, x ∈ U' ↔ x ∈ U ∧ polar Q v x = 0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, hx', rfl⟩
  refine ⟨v, hvU, hvQ, U', ?_, fun x hx => ((hmem x).mp hx).2, ?_, ?_⟩
  · intro x hx
    exact ((hmem x).mp hx).1
  · intro x hx hxy
    have hxU := ((hmem x).mp hx).1
    have hxv : polar Q v x = 0 := ((hmem x).mp hx).2
    apply hU x hxU
    intro y hy
    have hy' : y - (polar Q y v / 2) • v ∈ U' := by
      rw [hmem]
      refine ⟨U.sub_mem hy (U.smul_mem _ hvU), ?_⟩
      rw [polar_sub_right, polar_smul_right_eq, hvv, polar_comm Q v y]
      field_simp
      ring
    have h1 := hxy _ hy'
    have h3 : y = (y - (polar Q y v / 2) • v) + (polar Q y v / 2) • v := by abel
    rw [h3, polar_add_right, h1, polar_smul_right_eq, polar_comm Q x v, hxv]
    ring
  · have hr := LinearMap.finrank_range_add_finrank_ker φ
    have h1 : Module.finrank F (LinearMap.range φ) ≤ 1 := by
      calc Module.finrank F (LinearMap.range φ) ≤ Module.finrank F F := Submodule.finrank_le _
        _ = 1 := Module.finrank_self F
    have h4 : Module.finrank F U' = Module.finrank F (LinearMap.ker φ) :=
      LinearEquiv.finrank_eq
        ((LinearMap.ker φ).equivMapOfInjective U.subtype U.injective_subtype).symm
    omega

theorem exists_orthonormal_fin (hodd : Odd (Nat.card F)) :
    ∀ (n : ℕ) (U : Submodule F V), PolarNondegOn Q U → n + 1 ≤ Module.finrank F U →
      ∃ l : Fin n → V, (∀ i, l i ∈ U) ∧ (∀ i, Q (l i) = 1) ∧
        ∀ i j, i ≠ j → polar Q (l i) (l j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro U _ _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro U hU hdim
    obtain ⟨v, hvU, hvQ, U', hU'U, hU'v, hU'reg, hU'dim⟩ :=
      exists_unit_split hodd hU (by omega)
    obtain ⟨l, hlU, hlQ, hlP⟩ := ih U' hU'reg (by omega)
    refine ⟨Fin.cons v l, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvU
      · simpa using hU'U (hlU j)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvQ
      · simpa using hlQ j
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun h => absurd rfl h) (fun j' _ => ?_) j
        simpa using hU'v _ (hlU j')
      · refine Fin.cases (fun _ => ?_) (fun j' hj => ?_) j
        · rw [polar_comm]
          simpa using hU'v _ (hlU i')
        · have : i' ≠ j' := fun h => hj (by rw [h])
          simpa using hlP i' j' this


end Orthonormal

end C25X

end CFSG.ClassicalInvolution.Asc77
