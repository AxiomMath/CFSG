module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedScalars)

set_option linter.unusedSectionVars false

section Trace

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem trace_sq_eq_trace_mul_self_char_two (N : Matrix (Fin 3) (Fin 3) K) :
    (Matrix.trace N) ^ 2 = Matrix.trace (N * N) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination (N 0 0 * N 1 1 + N 0 0 * N 2 2 + N 1 1 * N 2 2 - N 0 1 * N 1 0 -
    N 0 2 * N 2 0 - N 1 2 * N 2 1) * h2

theorem commute_of_smul_commute {X Y : Matrix (Fin 3) (Fin 3) K} (hX : X * X = 1)
    (hY : Y * Y = 1) {c : K} (hc : X * Y = c • (Y * X)) : X * Y = Y * X := by
  by_cases hc1 : c = 1
  · rw [hc, hc1, one_smul]
  exfalso
  have hring : ringChar K = 2 := ringChar.eq K 2
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hXYYX : X * Y * (Y * X) = 1 := by
    calc X * Y * (Y * X) = X * (Y * Y) * X := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY, Matrix.mul_one, hX]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [hc, zero_smul, Matrix.zero_mul] at hXYYX
    exact zero_ne_one hXYYX
  have hYX : Y * X = c⁻¹ • (X * Y) := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hW2 : (X * Y) * (X * Y) = c⁻¹ • (1 : Matrix (Fin 3) (Fin 3) K) := by
    calc X * Y * (X * Y) = X * (Y * X) * Y := by simp only [Matrix.mul_assoc]
      _ = X * (c⁻¹ • (X * Y)) * Y := by rw [hYX]
      _ = c⁻¹ • (X * X * Y * Y) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = c⁻¹ • 1 := by rw [hX, Matrix.one_mul, hY]
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hring c⁻¹
  have hN : (X * Y - s • (1 : Matrix (Fin 3) (Fin 3) K)) * (X * Y - s • 1) = 0 := by
    have e : (X * Y - s • (1 : Matrix (Fin 3) (Fin 3) K)) * (X * Y - s • 1) =
        (X * Y) * (X * Y) - (2 * s) • (X * Y) + (s * s) • 1 := by
      simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.one_mul, smul_smul, two_mul, add_smul]
      abel
    rw [e, hW2, h2, zero_mul, zero_smul, sub_zero, ← hs, ← add_smul]
    have : c⁻¹ + c⁻¹ = 0 := by
      rw [← two_mul, h2, zero_mul]
    rw [this, zero_smul]
  have htr := trace_sq_eq_trace_mul_self_char_two (X * Y - s • 1)
  rw [hN, Matrix.trace_zero] at htr
  have htr0 : Matrix.trace (X * Y - s • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 :=
    pow_eq_zero_iff (two_ne_zero) |>.1 htr
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htr0
  have h3 : ((Fintype.card (Fin 3) : ℕ) : K) = 1 := by
    simp only [Fintype.card_fin]
    linear_combination h2
  have htr1 : Matrix.trace (X * Y) = s := by
    rw [h3] at htr0
    simpa using sub_eq_zero.1 htr0
  have htr2 : Matrix.trace (X * Y) = c * Matrix.trace (X * Y) := by
    conv_lhs => rw [hc]
    rw [Matrix.trace_smul, Matrix.trace_mul_comm Y X]
    simp
  rw [htr1] at htr2
  have hs0 : s = 0 := by
    have : s * (1 - c) = 0 := by linear_combination htr2
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hc1))
  rw [hs0, mul_zero] at hs
  exact inv_ne_zero hc0 hs

end Trace

section Core

variable {f : ℕ} {K : Type} [Field K]

open CFSG.RankThree.PartTwo.KFacts CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

theorem coe_diagTau_eq_diagonal {τ : K} (hτ : τ ^ 3 = 1) :
    ((Sec4.diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![τ, τ ^ 2, 1] := by
  rw [Sec4.coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_diagTau_inv_eq_diagonal {τ : K} (hτ : τ ^ 3 = 1) :
    (((Sec4.diagTau hτ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![τ ^ 2, τ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sec4.diagTau]

theorem eq_one_of_commute_mod_scalars_diagTau (hK : PiField false 2 f K)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {x : GL (Fin 3) K} (hx : x ∈ glPi false 3 (2 ^ f) K) (hx2 : x * x = 1) {c : K}
    (hc : ((x * (Sec4.diagTau hτ * x * (Sec4.diagTau hτ)⁻¹) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      c • (((Sec4.diagTau hτ * x * (Sec4.diagTau hτ)⁻¹) * x : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) : x = 1 := by
  have := hK.finite
  have : CharP K 2 := hK.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set v : GL (Fin 3) K := Sec4.diagTau hτ with hv
  set y : GL (Fin 3) K := v * x * v⁻¹ with hy
  have hX : (x : Matrix (Fin 3) (Fin 3) K) * x = 1 := by
    rw [← Units.val_mul, hx2, Units.val_one]
  have hy2 : y * y = 1 := by
    rw [hy]
    calc v * x * v⁻¹ * (v * x * v⁻¹) = v * (x * x) * v⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hY : (y : Matrix (Fin 3) (Fin 3) K) * y = 1 := by
    rw [← Units.val_mul, hy2, Units.val_one]
  have hcomm : (x : Matrix (Fin 3) (Fin 3) K) * y = y * x := by
    refine commute_of_smul_commute hX hY (c := c) ?_
    rw [← Units.val_mul, ← Units.val_mul]
    exact hc
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hτsq : τ ^ 2 + τ + 1 = 0 := by
    have h' : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hτ1)
  set d : Fin 3 → K := ![τ, τ ^ 2, 1] with hd
  set e : Fin 3 → K := ![τ ^ 2, τ, 1] with he
  have hde : ∀ i, d i * e i = 1 := by
    intro i
    fin_cases i
    · change τ * τ ^ 2 = 1
      linear_combination hτ
    · change τ ^ 2 * τ = 1
      linear_combination hτ
    · change (1 : K) * 1 = 1
      norm_num
  have hdd : ∀ i k, i ≠ k → d k * e i + d i * e k = 1 := by
    intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · change τ ^ 2 * τ ^ 2 + τ * τ = 1
      linear_combination hτsq + τ * hτ - h2
    · change 1 * τ ^ 2 + τ * 1 = 1
      linear_combination hτsq - h2
    · change τ * τ + τ ^ 2 * τ ^ 2 = 1
      linear_combination hτsq + τ * hτ - h2
    · exact absurd rfl hik
    · change 1 * τ + τ ^ 2 * 1 = 1
      linear_combination hτsq - h2
    · change τ * 1 + 1 * τ ^ 2 = 1
      linear_combination hτsq - h2
    · change τ ^ 2 * 1 + 1 * τ = 1
      linear_combination hτsq - h2
    · exact absurd rfl hik
  set σ := unitaryInvolution K 2 f with hσ
  have hzu : conjTr σ (x : Matrix (Fin 3) (Fin 3) K) * x = 1 := by
    rw [hσ, Sec4.conjTr_unitaryInvolution_eq hK]
    exact (Sec4.mem_glPi_false hK.unitary).1 hx
  have hYd : (y : Matrix (Fin 3) (Fin 3) K) =
      diagonal d * (x : Matrix (Fin 3) (Fin 3) K) * diagonal e := by
    rw [hy, Units.val_mul, Units.val_mul, hv, coe_diagTau_eq_diagonal hτ,
      coe_diagTau_inv_eq_diagonal hτ]
  have hcd : (x : Matrix (Fin 3) (Fin 3) K) * (diagonal d * x * diagonal e) =
      (diagonal d * x * diagonal e) * x := by
    rw [← hYd]
    exact hcomm
  have hx1 := eq_one_of_commute_conj_diagonal σ hde hdd hzu hX hcd
  exact Units.ext hx1

end Core

section Normal

variable {K : Type} [Field K]

theorem exists_smul_of_mk_eq {a b : GL (Fin 3) K}
    (h : Matrix.ProjGenLinGroup.mk a = Matrix.ProjGenLinGroup.mk b) :
    ∃ u : Kˣ, (a : Matrix (Fin 3) (Fin 3) K) = (u : K) • (b : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : Matrix.ProjGenLinGroup.mk (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : a * b⁻¹ ∈ StatedScalars (Fin 3) K := (Sec4.mk_eq_one_iff_mem_statedScalars).1 h1
  obtain ⟨u, hu⟩ := h2
  refine ⟨u, ?_⟩
  have h3 : a = Matrix.GeneralLinearGroup.scalar (Fin 3) u * b := by
    rw [hu]
    group
  rw [h3, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem units_pow_three_of_card_four [Finite K] (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
  rw [hc] at h
  exact Units.ext (by simpa using h)

theorem pgu_two_no_normal_two_group (hK : PiField false 2 1 K) (hq : ModThree false (2 ^ 1))
    (N : Subgroup ↥(projImage (glPi false 3 (2 ^ 1) K))) [hNn : N.Normal]
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have := hK.finite
  have : CharP K 2 := hK.charP
  have hπ : false = false → UnitaryFieldData 2 1 K := fun _ => hK.unitary
  have hK4 : Nat.card K = 4 := by rw [hK.card]; norm_num [Sec4.piCard]
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _)
      (QuotientGroup.mk'_surjective _)
  obtain ⟨τ, hτ3, hτ1⟩ := KFacts.exists_primitive_cube_root hK
  by_contra hne
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  have hZ := hN2.center_nontrivial
  have h2Z : IsPGroup 2 (Subgroup.center N) := hN2.to_subgroup _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card (Subgroup.center N) := by
    rcases h2Z.card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set z' : N := (z : N) with hz'
  have hz'2 : z' * z' = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    exact congrArg Subtype.val h
  have hz'1 : z' ≠ 1 := by
    intro h1
    have h : z = 1 := Subtype.ext h1
    rw [h, orderOf_one] at hz
    norm_num at hz
  set n : ↥(projImage (glPi false 3 (2 ^ 1) K)) :=
    (z' : ↥(projImage (glPi false 3 (2 ^ 1) K))) with hn
  have hnn : (n : Matrix.ProjGenLinGroup (Fin 3) K) * n = 1 := by
    have h := congrArg (fun x : N => ((x : ↥(projImage (glPi false 3 (2 ^ 1) K))) :
      Matrix.ProjGenLinGroup (Fin 3) K)) hz'2
    simpa using h
  obtain ⟨w, hwG, hw⟩ := Subgroup.mem_map.1 n.2
  have hw2 : w * w ∈ StatedScalars (Fin 3) K := by
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, hw]
    exact hnn
  obtain ⟨u, hu⟩ := hw2
  have hx2 : w ^ 3 * w ^ 3 = 1 := by
    have h3 : (w * w) ^ 3 = 1 := by
      rw [← hu, ← map_pow, units_pow_three_of_card_four hK4 u, map_one]
    calc w ^ 3 * w ^ 3 = (w * w) ^ 3 := by rw [← pow_add, ← sq, ← pow_mul]
      _ = 1 := h3
  have hxG : w ^ 3 ∈ glPi false 3 (2 ^ 1) K := pow_mem hwG 3
  have hmkx : Matrix.ProjGenLinGroup.mk (w ^ 3) = (n : Matrix.ProjGenLinGroup (Fin 3) K) := by
    rw [map_pow, hw]
    calc (n : Matrix.ProjGenLinGroup (Fin 3) K) ^ 3 = n * n * n := by rw [pow_succ, pow_two]
      _ = n := by rw [hnn, one_mul]
  have hvG : Sec4.diagTau hτ3 ∈ glPi false 3 (2 ^ 1) K :=
    Sec4.slPi_le_glPi hπ (Sec4.diagTau_mem_slPi hπ (fun _ => hq) hτ3)
  set r : ↥(projImage (glPi false 3 (2 ^ 1) K)) :=
    ⟨Matrix.ProjGenLinGroup.mk (Sec4.diagTau hτ3), Subgroup.mem_map_of_mem _ hvG⟩ with hr
  have hrn : r * n * r⁻¹ ∈ N := hNn.conj_mem _ z'.2 r
  have hcomm := Subgroup.mem_center_iff.1 z.2 ⟨r * n * r⁻¹, hrn⟩
  have hcomm' : (r * n * r⁻¹ : ↥(projImage (glPi false 3 (2 ^ 1) K))) * n =
      n * (r * n * r⁻¹) := by
    have h := congrArg (fun x : N => ((x : ↥(projImage (glPi false 3 (2 ^ 1) K)))) ) hcomm
    simpa using h
  have hmk : Matrix.ProjGenLinGroup.mk (w ^ 3 * (Sec4.diagTau hτ3 * w ^ 3 * (Sec4.diagTau hτ3)⁻¹)) =
      Matrix.ProjGenLinGroup.mk ((Sec4.diagTau hτ3 * w ^ 3 * (Sec4.diagTau hτ3)⁻¹) * w ^ 3) := by
    have h := congrArg (fun x : ↥(projImage (glPi false 3 (2 ^ 1) K)) =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) hcomm'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    simp only [map_mul, map_inv, hmkx]
    exact h.symm
  obtain ⟨c, hc⟩ := exists_smul_of_mk_eq hmk
  have hx1 := eq_one_of_commute_mod_scalars_diagTau hK hτ3 hτ1 hxG hx2 hc
  apply hz'1
  have hn1 : (n : Matrix.ProjGenLinGroup (Fin 3) K) = 1 := by
    rw [← hmkx, hx1, map_one]
  exact Subtype.ext (Subtype.ext hn1)

end Normal

section Center

variable {K : Type} [Field K]

@[expose] def swapGL : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapGL :
    ((swapGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := rfl

theorem swapGL_inv : (swapGL : GL (Fin 3) K)⁻¹ = swapGL := by
  ext i j
  rfl

theorem trace_swapGL : Matrix.trace ((swapGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [coe_swapGL]
  simp [Matrix.trace, Fin.sum_univ_three]

theorem swapGL_mem_glPi {p f : ℕ} (h : UnitaryFieldData p f K) :
    (swapGL : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K := by
  rw [Sec4.mem_glPi_false h, coe_swapGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

theorem swapGL_conj_cycThree : (swapGL : GL (Fin 3) K) * Sec4.cycThree * swapGL⁻¹ =
    (Sec4.cycThree : GL (Fin 3) K)⁻¹ := by
  rw [swapGL_inv]
  apply eq_inv_of_mul_eq_one_left
  ext i j
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_swapGL, Sec4.coe_cycThree, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swapGL_conj_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    (swapGL : GL (Fin 3) K) * Sec4.diagTau hτ * swapGL⁻¹ = (Sec4.diagTau hτ)⁻¹ := by
  rw [swapGL_inv]
  apply eq_inv_of_mul_eq_one_left
  ext i j
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_swapGL, Sec4.coe_diagTau, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hτ]
  · linear_combination hτ
  · linear_combination hτ

theorem sq_eq_one_of_conj_group {G : Type*} [Group G] {w T S c : G}
    (hc : ∀ g : G, g * c = c * g) (hwT : w * T = T * w) (hS : w * S * w⁻¹ = c * S)
    (hTS : T * S * T⁻¹ = S⁻¹) : c * c = 1 := by
  have hTw : T⁻¹ * w⁻¹ = w⁻¹ * T⁻¹ := by
    rw [← _root_.mul_inv_rev, hwT, _root_.mul_inv_rev]
  have h1 : w * (T * S * T⁻¹) * w⁻¹ = T * (w * S * w⁻¹) * T⁻¹ := by
    calc w * (T * S * T⁻¹) * w⁻¹ = (w * T) * S * (T⁻¹ * w⁻¹) := by group
      _ = (T * w) * S * (w⁻¹ * T⁻¹) := by rw [hwT, hTw]
      _ = T * (w * S * w⁻¹) * T⁻¹ := by group
  rw [hTS, hS] at h1
  have h2 : w * S⁻¹ * w⁻¹ = (c * S)⁻¹ := by
    rw [← hS]
    group
  have h3 : T * (c * S) * T⁻¹ = c * S⁻¹ := by
    calc T * (c * S) * T⁻¹ = (T * c) * S * T⁻¹ := by group
      _ = (c * T) * S * T⁻¹ := by rw [hc T]
      _ = c * (T * S * T⁻¹) := by group
      _ = c * S⁻¹ := by rw [hTS]
  rw [h3, h2] at h1
  have h4 : S⁻¹ * c⁻¹ = c * S⁻¹ := by
    rw [← _root_.mul_inv_rev]
    exact h1
  have h5 : c⁻¹ = c := by
    have hcS : S⁻¹ * c = c * S⁻¹ := (hc S⁻¹)
    have : S⁻¹ * c⁻¹ = S⁻¹ * c := by rw [h4, hcS]
    exact mul_left_cancel this
  calc c * c = c * c⁻¹ := by rw [h5]
    _ = 1 := mul_inv_cancel c

theorem pgu_two_center_trivial [Finite K] (hK : PiField false 2 1 K) (hq : ModThree false (2 ^ 1))
    (z : ↥(projImage (glPi false 3 (2 ^ 1) K))) (hz : ∀ x, z * x = x * z) : z = 1 := by
  have : CharP K 2 := hK.charP
  have hπ : false = false → UnitaryFieldData 2 1 K := fun _ => hK.unitary
  have hK4 : Nat.card K = 4 := by rw [hK.card]; norm_num [Sec4.piCard]
  obtain ⟨τ, hτ3, hτ1⟩ := KFacts.exists_primitive_cube_root hK
  obtain ⟨w, hwG, hw⟩ := Subgroup.mem_map.1 z.2
  have hmod : ∀ g ∈ glPi false 3 (2 ^ 1) K, ∃ u : Kˣ,
      w * g * w⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * g := by
    intro g hg
    have h1 := hz ⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    rw [← hw] at h2
    have h3 : Matrix.ProjGenLinGroup.mk (w * g * w⁻¹ * g⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h2]
      group
    obtain ⟨u, hu⟩ := (Sec4.mk_eq_one_iff_mem_statedScalars).1 h3
    refine ⟨u, ?_⟩
    rw [hu]
    group
  have hTG : (swapGL : GL (Fin 3) K) ∈ glPi false 3 (2 ^ 1) K := swapGL_mem_glPi hK.unitary
  have hwT : w * swapGL = swapGL * w := by
    obtain ⟨u, hu⟩ := hmod _ hTG
    have htr : Matrix.trace (((w * swapGL * w⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.trace ((swapGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [hu, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, trace_swapGL, smul_eq_mul, mul_one] at htr
    have hu1 : u = 1 := Units.ext htr
    rw [hu1, map_one, one_mul] at hu
    calc w * swapGL = w * swapGL * w⁻¹ * w := by group
      _ = swapGL * w := by rw [hu]
  have hcen : ∀ u : Kˣ, ∀ g : GL (Fin 3) K,
      g * Matrix.GeneralLinearGroup.scalar (Fin 3) u = Matrix.GeneralLinearGroup.scalar (Fin 3) u * g :=
    fun u g => (Matrix.GeneralLinearGroup.scalar_commute u g).symm
  have hcomm : ∀ S : GL (Fin 3) K, S ∈ glPi false 3 (2 ^ 1) K →
      (swapGL * S * swapGL⁻¹ = S⁻¹) → w * S = S * w := by
    intro S hS hTS
    obtain ⟨u, hu⟩ := hmod S hS
    have hsq := sq_eq_one_of_conj_group (hcen u) hwT hu hTS
    have hu2 : u * u = 1 := by
      have h := congrArg (fun a : GL (Fin 3) K => (a : Matrix (Fin 3) (Fin 3) K) 0 0) hsq
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Units.val_one] at h
      exact Units.ext (by simpa [Matrix.mul_apply, Matrix.diagonal_apply] using h)
    have hu3 := units_pow_three_of_card_four hK4 u
    have hu1 : u = 1 := by
      calc u = u ^ 3 * (u * u)⁻¹ := by group
        _ = 1 := by rw [hu3, hu2]; simp
    rw [hu1, map_one, one_mul] at hu
    calc w * S = w * S * w⁻¹ * w := by group
      _ = S * w := by rw [hu]
  have hcycG : (Sec4.cycThree : GL (Fin 3) K) ∈ glPi false 3 (2 ^ 1) K :=
    Sec4.slPi_le_glPi hπ (Sec4.cycThree_mem_slPi hπ)
  have hdG : Sec4.diagTau hτ3 ∈ glPi false 3 (2 ^ 1) K :=
    Sec4.slPi_le_glPi hπ (Sec4.diagTau_mem_slPi hπ (fun _ => hq) hτ3)
  have h1 := hcomm _ hdG (swapGL_conj_diagTau hτ3)
  have h2 := hcomm _ hcycG swapGL_conj_cycThree
  have hM := Sec4.eq_smul_one_of_commute hτ3 hτ1
    (M := (w : Matrix (Fin 3) (Fin 3) K)) (by rw [← Units.val_mul, ← Units.val_mul, h1])
    (by rw [← Units.val_mul, ← Units.val_mul, h2])
  have hw0 : w ∈ StatedScalars (Fin 3) K := by
    refine Sec4.mem_statedScalars_of_eq_smul hM fun h0 => ?_
    have hdet := congrArg Matrix.det hM
    rw [h0, zero_smul, Matrix.det_zero] at hdet
    exact (w.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero hdet
  refine Subtype.ext ?_
  rw [← hw, Subgroup.coe_one]
  exact (Sec4.mk_eq_one_iff_mem_statedScalars).2 hw0

end Center

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
