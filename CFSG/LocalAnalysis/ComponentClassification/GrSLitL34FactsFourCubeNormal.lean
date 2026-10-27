module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubeAction

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open Matrix Subgroup

theorem uM_sq : uM * uM = X0 := by decide

theorem uM_four : uM ^ 4 = 1 := by decide

theorem fix_uM : ∀ v : V4, uM *ᵥ v = v → v = (1 + X0) *ᵥ ![v 0, 0, 0] := by decide

theorem Cm_four : Cm ^ 4 = 1 := by decide

theorem fix_Cm : ∀ v : V4, Cm *ᵥ v = v → v = v 0 • d1 := by decide

theorem X0_e2 : (1 + X0) *ᵥ ![0, 1, 0] = 0 := by decide

theorem Cm_shift : ((Finset.range 4).sum fun i => (Cm ^ (i + 1)) *ᵥ (Bm *ᵥ ![0, 1, 0])) =
    (2 : ZMod 4) • d1 := by decide

theorem Y0_cube : Y0 * Y0 * Y0 = 1 := by decide

theorem X0_sq : X0 * X0 = 1 := by decide

theorem shift_cases : ∀ e : ZMod 4, e = 0 ∨ e = 1 ∨ e + 2 = 0 ∨ e + 2 = 1 := by decide

variable {L : Type*} [Group L] {T : Subgroup L} [hT : T.Normal]
  (ι : T ≃* Multiplicative V4)

theorem pow_mul_eq (g : L) (t : T) (n : ℕ) :
    ∃ p : T, (g * t) ^ n = p * g ^ n ∧
      vec ι p = (Finset.range n).sum fun i => (mat ι g ^ (i + 1)) *ᵥ vec ι t := by
  induction n with
  | zero => exact ⟨1, by simp, by simp [vec_one]⟩
  | succ n ih =>
    obtain ⟨p, hp, hv⟩ := ih
    refine ⟨p * conjT (g ^ (n + 1)) t, ?_, ?_⟩
    · rw [pow_succ, hp, Subgroup.coe_mul]
      simp only [conjT]
      group
    · rw [vec_mul, hv, vec_conj, mat_pow, Finset.sum_range_succ]

variable (hT0 : ∀ g : L, mat ι g = 1 → g ∈ T)

include hT0 in
theorem exists_inv_lift {x y : L} (hx : mat ι x = X0) (hy : mat ι y = Y0) :
    ∃ a : L, mat ι a = X0 ∧ a * a = 1 := by
  set u := y * x * y * x * y * y * x * y * y * x * y * x * y with hu
  have hmu : mat ι u = uM := by
    simp only [hu, mat_mul, hx, hy]
    rfl
  have hs : (u ^ 2)⁻¹ * x ∈ T := by
    apply hT0
    have h1 : mat ι (u ^ 2) = X0 := by rw [mat_pow, hmu, sq, uM_sq]
    have h2 : mat ι (u ^ 2)⁻¹ * X0 = 1 := by
      rw [← h1, ← mat_mul, inv_mul_cancel, mat_one]
    rw [mat_mul, hx, h2]
  set s : T := ⟨_, hs⟩ with hsdef
  have hxs : x = u ^ 2 * s := by rw [hsdef]; group
  have hu4 : u ^ 4 ∈ T := by
    apply hT0
    rw [mat_pow, hmu]
    exact uM_four
  set w : T := ⟨_, hu4⟩ with hwdef
  have hwfix : uM *ᵥ vec ι w = vec ι w := by
    rw [← hmu, ← vec_conj]
    congr 1
    apply Subtype.ext
    simp only [conjT, hwdef]
    group
  have hw := fix_uM _ hwfix
  obtain ⟨p, hp, hpv⟩ := pow_mul_eq ι (u ^ 2) s 2
  have hm2 : mat ι (u ^ 2) = X0 := by rw [mat_pow, hmu, sq, uM_sq]
  rw [hm2, Finset.sum_range_succ, Finset.sum_range_one, zero_add, pow_one, sq X0, X0_sq] at hpv
  have hx2 : x * x = p * w := by
    rw [hxs, ← sq, hp]
    congr 1
    rw [← pow_mul]
  set σ : T := elt ι (-(vec ι s + ![vec ι w 0, 0, 0])) with hσ
  refine ⟨x * σ, by rw [mat_mul, hx, mat_of_mem ι σ.2, mul_one], ?_⟩
  obtain ⟨p', hp', hp'v⟩ := pow_mul_eq ι x σ 2
  rw [hx, Finset.sum_range_succ, Finset.sum_range_one, zero_add, pow_one, sq X0, X0_sq] at hp'v
  have key : vec ι (p' * (p * w)) = 0 := by
    rw [vec_mul, vec_mul, hp'v, hpv, hσ, vec_elt]
    generalize hW' : (![vec ι w 0, 0, 0] : V4) = W' at hw ⊢
    rw [hw]
    simp only [add_mulVec, one_mulVec, mulVec_add, mulVec_neg]
    abel
  have h1 : p' * (p * w) = 1 := by
    apply vec_injective ι
    rw [key, vec_one]
  calc x * σ * (x * σ) = (x * σ) ^ 2 := (sq _).symm
    _ = p' * x ^ 2 := hp'
    _ = p' * (p * w) := by rw [sq, hx2]
    _ = ((p' * (p * w) : T) : L) := by simp only [Subgroup.coe_mul]
    _ = 1 := by rw [h1, Subgroup.coe_one]

include hT0 in
theorem exists_std_pair {x y : L} (hx : mat ι x = X0) (hy : mat ι y = Y0) :
    ∃ a b : L, mat ι a = X0 ∧ mat ι b = Bm ∧ a * a = 1 ∧ b * b = 1 ∧
      ∃ d : V4, (d = 0 ∨ d = d1) ∧ (a * b) ^ 4 = (elt ι d : L) := by
  obtain ⟨a, ha, ha2⟩ := exists_inv_lift ι hT0 hx hy
  have hyi : mat ι y⁻¹ = Y0 * Y0 := by
    calc mat ι y⁻¹ = mat ι y⁻¹ * (mat ι y * mat ι y * mat ι y) := by rw [hy, Y0_cube, mul_one]
      _ = mat ι (y⁻¹ * y) * mat ι y * mat ι y := by simp only [mat_mul, mul_assoc]
      _ = Y0 * Y0 := by rw [inv_mul_cancel, mat_one, one_mul, hy]
  set b := y * a * y⁻¹ with hbdef
  have hb : mat ι b = Bm := by rw [hbdef, mat_mul, mat_mul, hy, ha, hyi]; rfl
  have hb2 : b * b = 1 := by
    rw [hbdef]
    calc y * a * y⁻¹ * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [ha2, mul_one, mul_inv_cancel]
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hmc : mat ι (a * b) = Cm := by rw [mat_mul, ha, hb]; rfl
  have hc4 : (a * b) ^ 4 ∈ T := hT0 _ (by rw [mat_pow, hmc, Cm_four])
  set δ : T := ⟨_, hc4⟩ with hδ
  have hδfix : Cm *ᵥ vec ι δ = vec ι δ := by
    rw [← hmc, ← vec_conj]
    congr 1
    apply Subtype.ext
    show a * b * (a * b) ^ 4 * (a * b)⁻¹ = (a * b) ^ 4
    rw [← pow_succ', pow_succ, mul_inv_cancel_right]
  have hδv := fix_Cm _ hδfix
  set e := vec ι δ 0 with he
  rcases shift_cases e with h0 | h1 | h2 | h2
  · refine ⟨a, b, ha, hb, ha2, hb2, 0, Or.inl rfl, ?_⟩
    have : δ = elt ι 0 := by
      apply vec_injective ι
      rw [vec_elt, hδv, h0, zero_smul]
    rw [← this]
  · refine ⟨a, b, ha, hb, ha2, hb2, d1, Or.inr rfl, ?_⟩
    have : δ = elt ι d1 := by
      apply vec_injective ι
      rw [vec_elt, hδv, h1, one_smul]
    rw [← this]
  all_goals
    set t₂ : T := elt ι ![0, 1, 0] with ht₂
    obtain ⟨p, hp, hpv⟩ := pow_mul_eq ι a t₂ 2
    rw [ha, Finset.sum_range_succ, Finset.sum_range_one, zero_add, pow_one, sq X0, X0_sq,
      ← add_mulVec, add_comm X0 1, ht₂, vec_elt, X0_e2] at hpv
    have hp1 : p = 1 := vec_injective ι (by rw [hpv, vec_one])
    have ha'2 : a * t₂ * (a * t₂) = 1 := by
      rw [← sq, hp, hp1, Subgroup.coe_one, one_mul, sq, ha2]
    set r : T := conjT b⁻¹ t₂ with hr
    have hrv : vec ι r = Bm *ᵥ ![0, 1, 0] := by
      rw [hr, vec_conj, hbi, hb, ht₂, vec_elt]
    obtain ⟨p', hp', hp'v⟩ := pow_mul_eq ι (a * b) r 4
    rw [hmc, hrv, Cm_shift] at hp'v
    have hab : a * t₂ * b = a * b * r := by
      have hr' : (r : L) = b * t₂ * b := by
        rw [hr]
        show b⁻¹ * (t₂ : L) * b⁻¹⁻¹ = b * t₂ * b
        rw [inv_inv, hbi]
      rw [hr']
      calc a * (t₂ : L) * b = a * (b * b) * t₂ * b := by rw [hb2, mul_one]
        _ = a * b * (b * t₂ * b) := by group
    refine ⟨a * t₂, b, by rw [mat_mul, ha, mat_of_mem ι t₂.2, mul_one], hb, ha'2, hb2,
      (e + 2) • d1, ?_, ?_⟩
    · first
        | exact Or.inl (by rw [h2, zero_smul])
        | exact Or.inr (by rw [h2, one_smul])
    · rw [hab, hp']
      have : p' * δ = elt ι ((e + 2) • d1) := by
        apply vec_injective ι
        rw [vec_elt, vec_mul, hp'v, hδv, add_smul]
        abel
      rw [← this, Subgroup.coe_mul]

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
