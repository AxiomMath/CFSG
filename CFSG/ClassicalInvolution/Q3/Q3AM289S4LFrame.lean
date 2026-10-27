module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure ON4 (Q : QuadraticForm F V) (x₀ x₁ x₂ x₃ : V) : Prop where
  q₀ : Q x₀ = 1
  q₁ : Q x₁ = 1
  q₂ : Q x₂ = 1
  q₃ : Q x₃ = 1
  o₀₁ : polar Q x₀ x₁ = 0
  o₀₂ : polar Q x₀ x₂ = 0
  o₀₃ : polar Q x₀ x₃ = 0
  o₁₂ : polar Q x₁ x₂ = 0
  o₁₃ : polar Q x₁ x₃ = 0
  o₂₃ : polar Q x₂ x₃ = 0

@[expose] def cmb (x₀ x₁ x₂ x₃ : V) (a b c d : F) : V := a • x₀ + b • x₁ + c • x₂ + d • x₃

variable {x₀ x₁ x₂ x₃ : V}

theorem two_ne_zero_of_three (h3 : (3 : F) = 0) : (2 : F) ≠ 0 := by
  intro h
  have : (1 : F) = 0 := by linear_combination h3 - h
  exact one_ne_zero this

theorem ON4.polar_cmb (h : ON4 Q x₀ x₁ x₂ x₃) (a b c d a' b' c' d' : F) :
    polar Q (cmb x₀ x₁ x₂ x₃ a b c d) (cmb x₀ x₁ x₂ x₃ a' b' c' d') =
      2 * (a * a' + b * b' + c * c' + d * d') := by
  have p0 : polar Q x₀ x₀ = 2 := by rw [polar_self, h.q₀]; simp
  have p1 : polar Q x₁ x₁ = 2 := by rw [polar_self, h.q₁]; simp
  have p2 : polar Q x₂ x₂ = 2 := by rw [polar_self, h.q₂]; simp
  have p3 : polar Q x₃ x₃ = 2 := by rw [polar_self, h.q₃]; simp
  simp only [cmb, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, p0, p1, p2,
    p3, h.o₀₁, h.o₀₂, h.o₀₃, h.o₁₂, h.o₁₃, h.o₂₃, polar_comm Q x₁ x₀, polar_comm Q x₂ x₀,
    polar_comm Q x₃ x₀, polar_comm Q x₂ x₁, polar_comm Q x₃ x₁, polar_comm Q x₃ x₂, smul_eq_mul]
  ring

theorem ON4.Q_cmb (h : ON4 Q x₀ x₁ x₂ x₃) (h2 : (2 : F) ≠ 0) (a b c d : F) :
    Q (cmb x₀ x₁ x₂ x₃ a b c d) = a * a + b * b + c * c + d * d := by
  have h1 := h.polar_cmb a b c d a b c d
  rw [polar_self] at h1
  have h1' : (2 : F) * Q (cmb x₀ x₁ x₂ x₃ a b c d) = 2 * (a * a + b * b + c * c + d * d) := by
    simpa using h1
  exact mul_left_cancel₀ h2 h1'

theorem ON4.hQ₁ (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0) :
    Q (cmb x₀ x₁ x₂ x₃ (-1 : F) 0 (-1) (-1)) = 0 := by
  rw [h.Q_cmb (two_ne_zero_of_three h3)]; linear_combination h3

theorem ON4.hQ₂ (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0) :
    Q (cmb x₀ x₁ x₂ x₃ (-1 : F) 0 1 1) = 0 := by
  rw [h.Q_cmb (two_ne_zero_of_three h3)]; linear_combination h3

theorem ON4.hQ₃ (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0) :
    Q (cmb x₀ x₁ x₂ x₃ (0 : F) (-1) 1 (-1)) = 0 := by
  rw [h.Q_cmb (two_ne_zero_of_three h3)]; linear_combination h3

theorem ON4.hQ₄ (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0) :
    Q (cmb x₀ x₁ x₂ x₃ (0 : F) (-1) (-1) 1) = 0 := by
  rw [h.Q_cmb (two_ne_zero_of_three h3)]; linear_combination h3

theorem ON4.hp₁₂ (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0) :
    polar Q (cmb x₀ x₁ x₂ x₃ (-1 : F) 0 (-1) (-1)) (cmb x₀ x₁ x₂ x₃ (-1 : F) 0 1 1) = 1 := by
  rw [h.polar_cmb]; linear_combination (-2) * h3 + (-1 : F) * h3 + (2 : F) * h3

theorem ON4.hp₃₄ (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0) :
    polar Q (cmb x₀ x₁ x₂ x₃ (0 : F) (-1) 1 (-1)) (cmb x₀ x₁ x₂ x₃ (0 : F) (-1) (-1) 1) = 1 := by
  rw [h.polar_cmb]; linear_combination (-2) * h3 + (-1 : F) * h3 + (2 : F) * h3

@[expose] noncomputable def adFrame (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0) : Frame Q where
  P := ⟨cmb x₀ x₁ x₂ x₃ (-1 : F) 0 (-1) (-1), cmb x₀ x₁ x₂ x₃ (-1 : F) 0 1 1, h.hQ₁ h3,
    h.hQ₂ h3, h.hp₁₂ h3⟩
  P' := ⟨cmb x₀ x₁ x₂ x₃ (0 : F) (-1) 1 (-1), cmb x₀ x₁ x₂ x₃ (0 : F) (-1) (-1) 1, h.hQ₃ h3,
    h.hQ₄ h3, h.hp₃₄ h3⟩
  orth := ⟨by rw [h.polar_cmb]; ring, by rw [h.polar_cmb]; ring, by rw [h.polar_cmb]; ring,
    by rw [h.polar_cmb]; ring⟩

section Props

variable (h : ON4 Q x₀ x₁ x₂ x₃) (h3 : (3 : F) = 0)

theorem incl_adFrame (Y : Matrix (Fin 2) (Fin 2) F) :
    (adFrame h h3).incl Y = cmb x₀ x₁ x₂ x₃ (-Y 0 0 - Y 1 1) (Y 0 1 - Y 1 0)
      (-Y 0 0 + Y 1 1 - Y 0 1 - Y 1 0) (-Y 0 0 + Y 1 1 + Y 0 1 + Y 1 0) := by
  simp only [Frame.incl_apply, adFrame, cmb, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, smul_add,
    smul_smul]
  module

theorem x₀_eq_incl : x₀ = (adFrame h h3).incl !![1, 0; 0, 1] := by
  rw [incl_adFrame]
  have e : (-1 - 1 : F) = 1 := by linear_combination (-1) * h3
  simp [cmb, e]

theorem x₁_eq_incl : x₁ = (adFrame h h3).incl !![0, -1; 1, 0] := by
  rw [incl_adFrame]
  have e : (-1 - 1 : F) = 1 := by linear_combination (-1) * h3
  simp [cmb, e]

theorem x₂_eq_incl : x₂ = (adFrame h h3).incl !![-1, -1; -1, 1] := by
  rw [incl_adFrame]
  have e : (1 + 1 + 1 + 1 : F) = 1 := by linear_combination h3
  simp [cmb, e]

theorem x₃_eq_incl : x₃ = (adFrame h h3).incl !![-1, 1; 1, 1] := by
  rw [incl_adFrame]
  have e : (1 + 1 + 1 + 1 : F) = 1 := by linear_combination h3
  simp [cmb, e]

theorem polar_right_cmb (v : V) (a b c d : F) :
    polar Q v (cmb x₀ x₁ x₂ x₃ a b c d) =
      a * polar Q v x₀ + b * polar Q v x₁ + c * polar Q v x₂ + d * polar Q v x₃ := by
  simp [cmb, polar_add_right, polar_smul_right]

theorem mem_perp_adFrame_iff {v : V} :
    v ∈ (adFrame h h3).perp ↔ polar Q v x₀ = 0 ∧ polar Q v x₁ = 0 ∧ polar Q v x₂ = 0 ∧
      polar Q v x₃ = 0 := by
  constructor
  · intro hv
    have hc := (Frame.mem_perp_iff _).mp hv
    have key : ∀ Y : Matrix (Fin 2) (Fin 2) F, polar Q v ((adFrame h h3).incl Y) = 0 := by
      intro Y
      rw [Frame.polar_incl_right, hc]
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [x₀_eq_incl h h3]; exact key _
    · rw [x₁_eq_incl h h3]; exact key _
    · rw [x₂_eq_incl h h3]; exact key _
    · rw [x₃_eq_incl h h3]; exact key _
  · rintro ⟨h0, h1, h2, h3'⟩
    rw [Frame.mem_perp_iff, Frame.coords_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, polar_right_cmb, h0, h1, h2, h3']

theorem La_neg_one_incl (Y : Matrix (Fin 2) (Fin 2) F) :
    (adFrame h h3).La (-1) ((adFrame h h3).incl Y) = -(adFrame h h3).incl Y := by
  rw [Frame.La_neg_one_apply, Frame.coords_incl]
  module

theorem La_neg_one_of_mem_perp {v : V} (hv : v ∈ (adFrame h h3).perp) :
    (adFrame h h3).La (-1) v = v :=
  Frame.La_apply_of_coords_eq_zero _ _ ((Frame.mem_perp_iff _).mp hv)

theorem La_neg_one_x₀ : (adFrame h h3).La (-1) x₀ = -x₀ := by
  have e := x₀_eq_incl h h3
  have := La_neg_one_incl h h3 !![1, 0; 0, 1]
  rwa [← e] at this

theorem La_neg_one_x₁ : (adFrame h h3).La (-1) x₁ = -x₁ := by
  have e := x₁_eq_incl h h3
  have := La_neg_one_incl h h3 !![0, -1; 1, 0]
  rwa [← e] at this

theorem La_neg_one_x₂ : (adFrame h h3).La (-1) x₂ = -x₂ := by
  have e := x₂_eq_incl h h3
  have := La_neg_one_incl h h3 !![-1, -1; -1, 1]
  rwa [← e] at this

theorem La_neg_one_x₃ : (adFrame h h3).La (-1) x₃ = -x₃ := by
  have e := x₃_eq_incl h h3
  have := La_neg_one_incl h h3 !![-1, 1; 1, 1]
  rwa [← e] at this

@[expose] def Jmat (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem Jmat_mul_self (F : Type) [Field F] : Jmat F * Jmat F = -1 := by
  apply Subtype.ext
  show (!![0, -1; 1, 0] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def sig (Z : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![Z 1 1, -Z 1 0; -Z 0 1, Z 0 0]

theorem sig_J_mul (Z : Matrix (Fin 2) (Fin 2) F) :
    sig ((Jmat F : Matrix (Fin 2) (Fin 2) F) * Z) =
      (Jmat F : Matrix (Fin 2) (Fin 2) F) * sig Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sig, Jmat, Matrix.mul_apply, Fin.sum_univ_two]

theorem sig_sub (Y Z : Matrix (Fin 2) (Fin 2) F) : sig (Y - Z) = sig Y - sig Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sig] <;> ring

theorem g_incl (g : V ≃ₗ[F] V) (hg0 : g x₀ = x₀) (hg1 : g x₁ = x₁) (hg2 : g x₂ = -x₂)
    (hg3 : g x₃ = -x₃) (Z : Matrix (Fin 2) (Fin 2) F) :
    g ((adFrame h h3).incl Z) = (adFrame h h3).incl (sig Z) := by
  rw [incl_adFrame, incl_adFrame]
  simp only [cmb, map_add, map_smul, hg0, hg1, hg2, hg3, sig]
  simp
  module

theorem La_J_comm (g : V ≃ₗ[F] V) (hg0 : g x₀ = x₀) (hg1 : g x₁ = x₁) (hg2 : g x₂ = -x₂)
    (hg3 : g x₃ = -x₃) (hperp : ∀ v ∈ (adFrame h h3).perp, g v ∈ (adFrame h h3).perp) :
    g * (adFrame h h3).La (Jmat F) = (adFrame h h3).La (Jmat F) * g := by
  refine LinearEquiv.ext fun v => ?_
  set Y := (adFrame h h3).coords v with hY
  have hv' : v - (adFrame h h3).incl Y ∈ (adFrame h h3).perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, ← hY]; simp
  have e : g v = g (v - (adFrame h h3).incl Y) + (adFrame h h3).incl (sig Y) := by
    rw [map_sub, g_incl h h3 g hg0 hg1 hg2 hg3]; abel
  have hcg : (adFrame h h3).coords (g v) = sig Y := by
    rw [e, map_add, Frame.coords_incl,
      (Frame.mem_perp_iff _).mp (hperp _ hv'), zero_add]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_apply, Frame.La_apply, map_add,
    g_incl h h3 g hg0 hg1 hg2 hg3, hcg, ← hY, sig_sub, sig_J_mul]

end Props

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
