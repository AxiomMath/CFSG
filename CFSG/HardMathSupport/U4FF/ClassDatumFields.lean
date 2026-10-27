module

public import CFSG.HardMathSupport.U4FF.ClassDatumBruhat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverLift
public import CFSG.HardMathSupport.U4FF.ClassUminusB

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw (IsPElt)

namespace Datum

section Fields

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem gm_pow (g : G4 K n) (k : ℕ) : gm (g ^ k) = gm g ^ k := by
  induction k with
  | zero => simp [gm_one]
  | succ k ih => rw [pow_succ, gm_mul, ih, pow_succ]

theorem pow_four_U {g : G4 K n} (hg : g ∈ UpperU K n) : g ^ 4 = 1 :=
  eq_of_gm_eq (by rw [gm_pow, gm_one]; exact isUpperUni_pow_four (mem_UpperU'.mp hg))

theorem pow_four_L {g : G4 K n} (hg : g ∈ LowerU K n) : g ^ 4 = 1 :=
  eq_of_gm_eq (by rw [gm_pow, gm_one]; exact isLowerUni_pow_four (mem_LowerU'.mp hg))

theorem isPElt_of_mem_U {g : G4 K n} (hg : g ∈ UpperU K n) : IsPElt 2 g :=
  ⟨2, by rw [show (2 : ℕ) ^ 2 = 4 from rfl]; exact pow_four_U hg⟩

theorem isPElt_of_mem_L {g : G4 K n} (hg : g ∈ LowerU K n) : IsPElt 2 g :=
  ⟨2, by rw [show (2 : ℕ) ^ 2 = 4 from rfl]; exact pow_four_L hg⟩

theorem isPGroup_U : IsPGroup 2 ↥(UpperU K n) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  show (g : G4 K n) ^ 2 ^ 2 = 1
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  exact pow_four_U g.2

theorem isPGroup_L : IsPGroup 2 ↥(LowerU K n) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  show (g : G4 K n) ^ 2 ^ 2 = 1
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  exact pow_four_L g.2

theorem UpperU_inf_LowerU : UpperU K n ⊓ LowerU K n = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hu, hl⟩ := Subgroup.mem_inf.1 hx
  have hu' := mem_UpperU'.mp hu
  have hl' := mem_LowerU'.mp hl
  rw [Subgroup.mem_bot]
  apply eq_of_gm_eq
  ext i j
  rw [gm_one]
  by_cases hij : i = j
  · subst hij
    rw [hu'.2, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hij]
    rcases lt_or_gt_of_ne hij with h | h
    · exact hl'.1 i j h
    · exact hu'.1 i j h

theorem Hd_comm {a b : G4 K n} (ha : a ∈ Hd K n) (hb : b ∈ Hd K n) : a * b = b * a := by
  obtain ⟨d, hd, -⟩ := exists_diag ha
  obtain ⟨e, he, -⟩ := exists_diag hb
  apply eq_of_gm_eq
  rw [gm_mul, gm_mul, hd, he, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem y0_mem_L (hK : Nat.card K = (2 ^ n) ^ 2) (c : K) : y0 hK c ∈ LowerU K n :=
  mem_LowerU'.mpr (by rw [gm_y0 hK]; exact isLowerUni_y0Mat n c)

theorem y1_mem_L (hK : Nat.card K = (2 ^ n) ^ 2) (c : Fq K n) : y1 hK c ∈ LowerU K n :=
  mem_LowerU'.mpr (by rw [gm_y1 hK]; exact isLowerUni_y1Mat _)

theorem X0_ne_bot (hK : Nat.card K = (2 ^ n) ^ 2) : X0 K n ≠ ⊥ := by
  intro h
  have hx := x0_mem_X0 hK (1 : K)
  rw [h, Subgroup.mem_bot] at hx
  have := congrArg (fun g => gm g 0 1) hx
  simp [gm_x0 hK, x0Mat, gm_one] at this

theorem X1_ne_bot (hK : Nat.card K = (2 ^ n) ^ 2) : X1 K n ≠ ⊥ := by
  intro h
  have hx := x1_mem_X1 hK (1 : Fq K n)
  rw [h, Subgroup.mem_bot] at hx
  have := congrArg (fun g => gm g 1 2) hx
  simp [gm_x1 hK, x1Mat, gm_one] at this

theorem phi_ex (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {x : G4 K n} (hx : x ∈ Xs K n s)
    (hx1 : x ≠ 1) :
    ∃ h ∈ Hd K n, ∃ l ∈ LowerU K n, ∃ u ∈ UpperU K n, x * nSimple K n s = l * h * u := by
  fin_cases s
  · obtain ⟨u, rfl⟩ := exists_unit_X0 hK hx hx1
    exact ⟨hTor0 hK u, hTor0_mem hK u, y0 hK ((u⁻¹ : Kˣ) : K), y0_mem_L hK _,
      x0 hK ((u⁻¹ : Kˣ) : K), X0_le_U n (x0_mem_X0 hK _), rank0_phi hK u⟩
  · obtain ⟨u, rfl⟩ := exists_unit_X1 hK hx hx1
    exact ⟨hTor1 hK u, hTor1_mem hK u, y1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n), y1_mem_L hK _,
      x1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n), X1_le_U n (x1_mem_X1 hK _), rank1_phi hK u⟩

theorem psi_ex (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {x : G4 K n} (hx : x ∈ Xs K n s)
    (hx1 : x ≠ 1) :
    ∃ h ∈ Hd K n, ∃ a ∈ Xs K n s, ∃ u ∈ UpperU K n,
      nSimple K n s * x * nSimple K n s = a * nSimple K n s * h * u := by
  obtain ⟨a, ha, h, hh, e⟩ := psi_form hK s hx hx1
  exact ⟨h, hh, a, ha, a, Xs_le_U s ha, e⟩

theorem y0Mat_zero (n : ℕ) : y0Mat n (0 : K) = 1 := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y0Mat, zero_pow hq]

theorem y1Mat_zero : y1Mat (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y1Mat]

theorem exists_y0 (hK : Nat.card K = (2 ^ n) ^ 2) {y : G4 K n} (hy : y ∈ Jconj K n (X0 K n))
    (hy1 : y ≠ 1) : ∃ w : Kˣ, y = y0 hK (w : K) := by
  obtain ⟨t, ht⟩ := mem_X0.mp (mem_Jconj.mp hy)
  have hw : y = y0 hK (t ^ 2 ^ n) := by
    apply eq_of_gm_eq
    ext a b
    rw [gm_entry_via_J, ht, gm_y0 hK]
    fin_cases a <;> fin_cases b <;>
      simp [x0Mat, y0Mat, rev0, rev1, rev2, rev3, pow_pow_of_card hK]
  have hw0 : t ^ 2 ^ n ≠ 0 := by
    intro h0
    apply hy1
    rw [hw, h0]
    exact eq_of_gm_eq (by rw [gm_y0 hK, y0Mat_zero, gm_one])
  exact ⟨Units.mk0 _ hw0, hw⟩

theorem exists_y1 (hK : Nat.card K = (2 ^ n) ^ 2) {y : G4 K n} (hy : y ∈ Jconj K n (X1 K n))
    (hy1 : y ≠ 1) : ∃ w : (Fq K n)ˣ, y = y1 hK (w : Fq K n) := by
  obtain ⟨t, htq, ht⟩ := mem_X1.mp (mem_Jconj.mp hy)
  have hw : y = y1 hK ⟨t, htq⟩ := by
    apply eq_of_gm_eq
    ext a b
    rw [gm_entry_via_J, ht, gm_y1 hK]
    fin_cases a <;> fin_cases b <;> simp [x1Mat, y1Mat, rev0, rev1, rev2, rev3]
  have hw0 : (⟨t, htq⟩ : Fq K n) ≠ 0 := by
    intro h0
    apply hy1
    rw [hw, h0]
    exact eq_of_gm_eq (by rw [gm_y1 hK]; show y1Mat ((0 : Fq K n) : K) = _
                          rw [gm_one]; exact y1Mat_zero)
  exact ⟨Units.mk0 _ hw0, hw⟩

theorem bruhatY0 (hK : Nat.card K = (2 ^ n) ^ 2) {y : G4 K n} (hy : y ∈ Jconj K n (X0 K n))
    (hy1 : y ≠ 1) : ∃ h ∈ Hd K n, ∃ a ∈ X0 K n, ∃ c ∈ X0 K n, y = a * (h * nHom K n s0) * c := by
  obtain ⟨w, rfl⟩ := exists_y0 hK hy hy1
  have h := rank0_bruhat hK w⁻¹
  rw [inv_inv] at h
  exact ⟨hTor0 hK w⁻¹, hTor0_mem hK _, x0 hK ((w⁻¹ : Kˣ) : K), x0_mem_X0 hK _,
    x0 hK ((w⁻¹ : Kˣ) : K), x0_mem_X0 hK _, by rw [h]; group⟩

theorem bruhatY1 (hK : Nat.card K = (2 ^ n) ^ 2) {y : G4 K n} (hy : y ∈ Jconj K n (X1 K n))
    (hy1 : y ≠ 1) : ∃ h ∈ Hd K n, ∃ a ∈ X1 K n, ∃ c ∈ X1 K n, y = a * (h * nHom K n s1) * c := by
  obtain ⟨w, rfl⟩ := exists_y1 hK hy hy1
  have h := rank1_bruhat hK w⁻¹
  rw [inv_inv] at h
  exact ⟨hTor1 hK w⁻¹, hTor1_mem hK _, x1 hK ((w⁻¹ : (Fq K n)ˣ) : Fq K n), x1_mem_X1 hK _,
    x1 hK ((w⁻¹ : (Fq K n)ˣ) : Fq K n), x1_mem_X1 hK _, by rw [h]; group⟩

theorem Hd_pow_card_sub_one {h : G4 K n} (hh : h ∈ Hd K n) : h ^ (Nat.card K - 1) = 1 := by
  obtain ⟨d, hd, hdi⟩ := exists_diag hh
  apply eq_of_gm_eq
  rw [gm_pow, gm_one, hd, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  have hne : d i ≠ 0 := by rw [← hdi]; exact Hd_diag_ne hh i
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ hne

theorem Hd_eq_one_of_isPElt (hK : Nat.card K = (2 ^ n) ^ 2) {h : G4 K n} (hh : h ∈ Hd K n)
    (hp : IsPElt 2 h) : h = 1 := by
  obtain ⟨k, hk⟩ := hp
  have h1 := Hd_pow_card_sub_one hh
  have hn : n ≠ 0 := by
    rintro rfl
    have := one_lt_two_pow_of_card hK
    simp at this
  have hev : Even (Nat.card K) := by
    rw [hK]
    exact Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hn⟩, two_ne_zero⟩
  have hodd : Odd (Nat.card K - 1) := by
    obtain ⟨m, hm⟩ := hev
    have hpos : 0 < Nat.card K := Nat.card_pos
    exact ⟨m - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have : orderOf h = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h1)
  exact orderOf_eq_one_iff.mp this

end Fields

end Datum

end CFSG.HardMathSupport.U4FF
