module

public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Blueprint CFSG.LieType.Ree
open scoped LinearAlgebra.Projectivization

namespace SpChain

variable {K : Type} [Field K]

theorem minorJ_eq_suzukiW : minorJ K = suzukiW K := rfl

variable (a : ℕ)

theorem suzukiS_transpose_mul [CharP K 2] (u v : K) :
    (suzukiS a u v)ᵀ * minorJ K * suzukiS a u v = minorJ K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply]
  all_goals ring_nf
  all_goals simp [h2]

theorem minorMap_suzukiS [CharP K 2] (hθθ : ∀ x : K, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2)
    (u v : K) : minorMap (suzukiS a u v) = (suzukiS a u v).map (· ^ 2 ^ (a + 1)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hadd : ∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1) :=
    fun x y => add_pow_char_pow x y 2 (a + 1)
  have h1 : u ^ (2 ^ (a + 1) + 1) = u ^ 2 ^ (a + 1) * u := pow_succ u _
  have hN : suzukiN a u v = u ^ 2 ^ (a + 1) * u ^ 2 + u * v + v ^ 2 ^ (a + 1) := by
    rw [suzukiN, pow_add]
  have hNθ : suzukiN a u v ^ 2 ^ (a + 1) =
      u ^ 2 * (u ^ 2 ^ (a + 1)) ^ 2 + u ^ 2 ^ (a + 1) * v ^ 2 ^ (a + 1) + v ^ 2 := by
    rw [hN, hadd, hadd, mul_pow, mul_pow, hθθ, hθθ, ← pow_mul u 2 (2 ^ (a + 1)),
      mul_comm 2 (2 ^ (a + 1)), pow_mul]
  have hSθ : (u ^ (2 ^ (a + 1) + 1) + v) ^ 2 ^ (a + 1) =
      u ^ 2 * u ^ 2 ^ (a + 1) + v ^ 2 ^ (a + 1) := by
    rw [hadd, h1, mul_pow, hθθ]
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, suzukiS]
  · rw [h1, hN]
    linear_combination (-(v ^ 2 ^ (a + 1))) * h2
  · rw [hθθ]
    ring
  · rw [hNθ, h1, hN]
    linear_combination (-((u ^ 2 ^ (a + 1)) ^ 2 * u ^ 2 + u ^ 2 ^ (a + 1) * v ^ 2 ^ (a + 1))) * h2
  · rw [hN, hSθ]
    linear_combination (-(u ^ 2 ^ (a + 1) * u ^ 2 + v ^ 2 ^ (a + 1))) * h2

theorem suzukiD_transpose_mul (l : Kˣ) :
    (suzukiD a l)ᵀ * minorJ K * suzukiD a l = minorJ K := by
  have hl : (l : K) ≠ 0 := l.ne_zero
  have hm : (l : K) ^ 2 ^ a ≠ 0 := pow_ne_zero _ hl
  rw [suzukiD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply, Matrix.diagonal_apply, hm]
  all_goals field_simp

theorem minorMap_suzukiD (hq : ∀ x : K, x ^ 2 ^ (2 * a + 1) = x) (l : Kˣ) :
    minorMap (suzukiD a l) = (suzukiD a l).map (· ^ 2 ^ (a + 1)) := by
  have hl : (l : K) ≠ 0 := l.ne_zero
  have hm : (l : K) ^ 2 ^ a ≠ 0 := pow_ne_zero _ hl
  have hθ0 : (2 ^ (a + 1) : ℕ) ≠ 0 := by positivity
  have hmθ : ((l : K) ^ 2 ^ a) ^ 2 ^ (a + 1) = l := by
    rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring, hq]
  have hlθ : (l : K) ^ 2 ^ (a + 1) = ((l : K) ^ 2 ^ a) ^ 2 := by
    rw [← pow_mul, ← pow_succ]
  rw [suzukiD_eq]
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three,
      zero_pow hθ0, mul_pow, inv_pow, hmθ, hlθ, hm]
  · ring
  · field_simp

theorem suzukiW_transpose_mul : (suzukiW K)ᵀ * minorJ K * suzukiW K = minorJ K := by
  rw [← minorJ_eq_suzukiW, minorJ_transpose, Matrix.mul_assoc, minorJ_mul_self, Matrix.mul_one]

theorem minorMap_suzukiW [CharP K 2] :
    minorMap (suzukiW K) = (suzukiW K).map (· ^ 2 ^ (a + 1)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hθ0 : (2 ^ (a + 1) : ℕ) ≠ 0 := by positivity
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, suzukiW,
      zero_pow hθ0]
  all_goals exact CharTwo.neg_eq 1

variable (K) in
@[expose] def antiFrobPowHom [CharP K 2] (n : ℕ) : antiSp K →* antiSp K :=
  ((GeneralLinearGroup.map (iterateFrobenius K 2 n)).comp (antiSp K).subtype).codRestrict
    (antiSp K) fun g => by
      rw [mem_antiSp]
      change ((glMat g).map (iterateFrobenius K 2 n))ᵀ * minorJ K *
        (glMat g).map (iterateFrobenius K 2 n) = minorJ K
      rw [← minorJ_map (iterateFrobenius K 2 n), ← transpose_map, ← Matrix.map_mul,
        ← Matrix.map_mul, mem_antiSp.mp g.2]

theorem glMat_antiFrobPowHom [CharP K 2] (n : ℕ) (g : antiSp K) :
    glMat (antiFrobPowHom K n g : GL (Fin 4) K) = (glMat g).map fun x => x ^ 2 ^ n := by
  ext i j
  exact iterateFrobenius_def (p := 2) n _

variable (K) in
@[expose] def minorFixGroup [CharP K 2] (n : ℕ) : Subgroup (GL (Fin 4) K) :=
  ((minorHom K).eqLocus (antiFrobPowHom K n)).map (antiSp K).subtype

theorem mem_minorFixGroup [CharP K 2] {n : ℕ} {g : GL (Fin 4) K} :
    g ∈ minorFixGroup K n ↔ (glMat g)ᵀ * minorJ K * glMat g = minorJ K ∧
      minorMap (glMat g) = (glMat g).map fun x => x ^ 2 ^ n := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g'.2, ?_⟩
    have h := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hg'
    simpa only [glMat_minorHom, glMat_antiFrobPowHom, Subgroup.coe_subtype] using h
  · rintro ⟨hg, hfix⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    change glMat (minorHom K ⟨g, hg⟩ : GL (Fin 4) K) =
      glMat (antiFrobPowHom K n ⟨g, hg⟩ : GL (Fin 4) K)
    rw [glMat_minorHom, glMat_antiFrobPowHom]
    exact hfix

theorem pow_card_suzuki [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : K) :
    x ^ 2 ^ (2 * a + 1) = x := by
  have : Fintype K := Fintype.ofFinite K
  rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem suzukiGroup_le_minorFixGroup [CharP K 2] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : suzukiGroup a K ≤ minorFixGroup K (a + 1) := by
  obtain ⟨-, -, hθθ, -⟩ := suzuki_frobenius_exponents a K hK
  refine (Subgroup.closure_le _).2 ?_
  rintro g (⟨u, v, hg⟩ | ⟨l, hg⟩ | hg) <;> rw [SetLike.mem_coe, mem_minorFixGroup, glMat, hg]
  · exact ⟨suzukiS_transpose_mul a u v, minorMap_suzukiS a hθθ u v⟩
  · exact ⟨suzukiD_transpose_mul a l, minorMap_suzukiD a (pow_card_suzuki a hK) l⟩
  · exact ⟨suzukiW_transpose_mul, minorMap_suzukiW a⟩

theorem col_zero_mem_suzukiOmega [CharP K 2] {g : Matrix (Fin 4) (Fin 4) K}
    (hW : gᵀ * minorJ K * g = minorJ K) (hρ : minorMap g = g.map fun x => x ^ 2 ^ (a + 1))
    (hx : (fun i => g i 0) ≠ 0) :
    Projectivization.mk K (fun i => g i 0) hx ∈ suzukiOmega a K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hθ0 : (2 ^ (a + 1) : ℕ) ≠ 0 := by positivity
  have hρ' : ∀ A B, g (minorIdx A).1 (minorIdx B).1 * g (minorIdx A).2 (minorIdx B).2 -
      g (minorIdx A).1 (minorIdx B).2 * g (minorIdx A).2 (minorIdx B).1 =
        g A B ^ 2 ^ (a + 1) := fun A B => by
    rw [← minorMap_apply, hρ, Matrix.map_apply]
  have hW' : ∀ k l, g 0 k * g 3 l + g 1 k * g 2 l + g 2 k * g 1 l + g 3 k * g 0 l =
      minorJ K k l := fun k l => by rw [← transpose_mul_minorJ_mul_apply, hW]
  have E1 : g 0 0 * g 1 1 + g 1 0 * g 0 1 = g 0 0 ^ 2 ^ (a + 1) := by
    have h := hρ' 0 0
    simp only [minorIdx_zero] at h
    linear_combination h + g 0 1 * g 1 0 * h2
  have E2 : g 0 0 * g 2 1 + g 2 0 * g 0 1 = g 1 0 ^ 2 ^ (a + 1) := by
    have h := hρ' 1 0
    simp only [minorIdx_zero, minorIdx_one] at h
    linear_combination h + g 0 1 * g 2 0 * h2
  have E3 : g 1 0 * g 3 1 + g 3 0 * g 1 1 = g 2 0 ^ 2 ^ (a + 1) := by
    have h := hρ' 2 0
    simp only [minorIdx_zero, minorIdx_two] at h
    linear_combination h + g 1 1 * g 3 0 * h2
  have P : g 0 0 * g 3 1 + g 1 0 * g 2 1 + g 2 0 * g 1 1 + g 3 0 * g 0 1 = 0 := by
    rw [hW' 0 1]
    simp [minorJ_apply]
  set b := g 0 0
  set c := g 1 0
  set d := g 2 0
  set h := g 3 0
  have hcol : (fun i => g i 0) = ![b, c, d, h] := by
    funext i
    fin_cases i <;> rfl
  by_cases hb : b = 0
  ·
    rw [hb, zero_pow hθ0] at E1
    rw [hb] at E2 P
    have hc : c = 0 := by
      by_contra hc
      have hi : g 0 1 = 0 := by
        have : c * g 0 1 = 0 := by linear_combination E1
        exact (mul_eq_zero.mp this).resolve_left hc
      rw [hi] at E2
      exact hc (pow_eq_zero_iff hθ0 |>.mp (by linear_combination -E2))
    rw [hc] at E2 E3 P
    have hd : d = 0 := by
      by_contra hd
      have hi : g 0 1 = 0 := by
        have : d * g 0 1 = 0 := by linear_combination E2
        exact (mul_eq_zero.mp this).resolve_left hd
      have hj : g 1 1 = 0 := by
        rw [hi] at P
        have : d * g 1 1 = 0 := by linear_combination P
        exact (mul_eq_zero.mp this).resolve_left hd
      rw [hj] at E3
      exact hd (pow_eq_zero_iff hθ0 |>.mp (by linear_combination -E3))
    have hh : h ≠ 0 := by
      intro hh
      apply hx
      rw [hcol, hb, hc, hd, hh]
      ext i
      fin_cases i <;> rfl
    have : Projectivization.mk K (fun i => g i 0) hx = suzukiInfty K := by
      rw [suzukiInfty, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 h hh, ?_⟩
      rw [hcol, hb, hc, hd]
      ext i
      fin_cases i <;> simp [Units.smul_def]
    rw [this]
    exact suzukiInfty_mem_suzukiOmega a K
  ·
    have T : b ^ (2 ^ (a + 1) + 1) * h = c ^ (2 ^ (a + 1) + 2) + b ^ 2 ^ (a + 1) * c * d +
        b ^ 2 * d ^ 2 ^ (a + 1) := by
      rw [pow_succ, pow_add c]
      linear_combination b ^ 2 * E3 - b * c * P + c ^ 2 * E2 + (c * d - b * h) * E1 +
        (b * c * h * g 0 1 - c ^ 2 * d * g 0 1) * h2
    set u := c / b with hu
    set v := d / b with hv
    have hcu : c = b * u := by rw [hu]; field_simp
    have hdv : d = b * v := by rw [hv]; field_simp
    have hN : h = b * suzukiN a u v := by
      apply mul_left_cancel₀ (pow_ne_zero (2 ^ (a + 1) + 1) hb)
      rw [T, hcu, hdv, suzukiN]
      ring
    have hline : Projectivization.mk K (fun i => g i 0) hx = suzukiLine a K u v := by
      rw [suzukiLine, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 b hb, ?_⟩
      rw [hcol]
      ext i
      fin_cases i <;> simp [Units.smul_def, ← hcu, ← hdv, ← hN]
    rw [hline]
    exact suzukiLine_mem_suzukiOmega a K u v

theorem eq_W_suzukiS_W [CharP K 2] (hθθ : ∀ x : K, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2)
    {M : Matrix (Fin 4) (Fin 4) K} (hW : Mᵀ * minorJ K * M = minorJ K)
    (hρ : minorMap M = M.map fun x => x ^ 2 ^ (a + 1))
    (h00 : M 0 0 = 1) (h11 : M 1 1 = 1) (h22 : M 2 2 = 1) (h33 : M 3 3 = 1)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h30 : M 3 0 = 0) (h21 : M 2 1 = 0) (h31 : M 3 1 = 0)
    (h32 : M 3 2 = 0) :
    M = suzukiW K * suzukiS a (M 0 1) (M 0 2 + M 0 1 ^ (2 ^ (a + 1) + 1)) * suzukiW K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hadd : ∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1) :=
    fun x y => add_pow_char_pow x y 2 (a + 1)
  have hρ' : ∀ A B, M (minorIdx A).1 (minorIdx B).1 * M (minorIdx A).2 (minorIdx B).2 -
      M (minorIdx A).1 (minorIdx B).2 * M (minorIdx A).2 (minorIdx B).1 =
        M A B ^ 2 ^ (a + 1) := fun A B => by
    rw [← minorMap_apply, hρ, Matrix.map_apply]
  have hW' : ∀ k l, M 0 k * M 3 l + M 1 k * M 2 l + M 2 k * M 1 l + M 3 k * M 0 l =
      minorJ K k l := fun k l => by rw [← transpose_mul_minorJ_mul_apply, hW]
  have hy : M 1 2 = M 0 1 ^ 2 ^ (a + 1) := by
    have h := hρ' 0 1
    simp only [minorIdx_zero, minorIdx_one, h00, h10] at h
    linear_combination h
  have hz : M 2 3 = M 0 1 := by
    have h := hW' 1 3
    simp only [h33, h11, h21, h31, minorJ_apply] at h
    norm_num at h
    linear_combination h - M 0 1 * h2
  have hw : M 1 3 = M 0 2 + M 0 1 ^ (2 ^ (a + 1) + 1) := by
    have h := hW' 2 3
    simp only [h33, h22, h32, hy, hz, minorJ_apply] at h
    norm_num at h
    rw [pow_succ (M 0 1)]
    linear_combination h - (M 0 2 + M 0 1 ^ 2 ^ (a + 1) * M 0 1) * h2
  have hx : M 0 3 = suzukiN a (M 0 1) (M 0 2) := by
    have h := hρ' 1 3
    simp only [minorIdx_one, minorIdx_three, h22, hz, hw] at h
    rw [hadd, pow_succ (M 0 1) (2 ^ (a + 1)), mul_pow, hθθ] at h
    rw [suzukiN, pow_add]
    linear_combination -h - (M 0 1 ^ 2 * M 0 1 ^ 2 ^ (a + 1) + M 0 2 ^ 2 ^ (a + 1)) * h2
  ext i j
  rw [suzukiW_eq]
  fin_cases i <;> fin_cases j <;>
    simp [suzukiS, Matrix.mul_apply, Fin.sum_univ_four, h00, h11, h22, h33, h10, h20, h30, h21,
      h31, h32, hy, hz, hw, hx]
  · linear_combination (-(M 0 1 ^ (2 ^ (a + 1) + 1))) * h2
  · rw [suzukiN, suzukiN, hadd, pow_succ (M 0 1) (2 ^ (a + 1)), mul_pow, hθθ]
    linear_combination (-(M 0 1 ^ 2 * M 0 1 ^ 2 ^ (a + 1))) * h2

theorem suzukiD_inv_eq (l : Kˣ) : suzukiD a l⁻¹ = Matrix.diagonal
    ![((l : K) * (l : K) ^ 2 ^ a)⁻¹, ((l : K) ^ 2 ^ a)⁻¹, (l : K) ^ 2 ^ a,
      (l : K) * (l : K) ^ 2 ^ a] := by
  rw [suzukiD_eq]
  congr 1
  ext i
  fin_cases i <;> simp [Units.val_inv_eq_inv_val, inv_pow, mul_comm]

theorem mem_suzukiGroup_of_col_zero [CharP K 2] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : GL (Fin 4) K} (hg : g ∈ minorFixGroup K (a + 1)) {b : K} (hb : b ≠ 0)
    (h00 : glMat g 0 0 = b) (h10 : glMat g 1 0 = 0) (h20 : glMat g 2 0 = 0)
    (h30 : glMat g 3 0 = 0) : g ∈ suzukiGroup a K := by
  obtain ⟨-, -, hθθ, -, -, -, -, -, -, -, -, -, hbij⟩ := suzuki_frobenius_exponents a K hK
  have hθ0 : (2 ^ (a + 1) : ℕ) ≠ 0 := by positivity
  obtain ⟨hW, hρ⟩ := mem_minorFixGroup.mp hg
  have hρ' : ∀ A B, glMat g (minorIdx A).1 (minorIdx B).1 * glMat g (minorIdx A).2 (minorIdx B).2 -
      glMat g (minorIdx A).1 (minorIdx B).2 * glMat g (minorIdx A).2 (minorIdx B).1 =
        glMat g A B ^ 2 ^ (a + 1) := fun A B => by
    rw [← minorMap_apply, hρ, Matrix.map_apply]
  have hW' : ∀ k l, glMat g 0 k * glMat g 3 l + glMat g 1 k * glMat g 2 l +
      glMat g 2 k * glMat g 1 l + glMat g 3 k * glMat g 0 l = minorJ K k l := fun k l => by
    rw [← transpose_mul_minorJ_mul_apply, hW]
  have E1 : b * glMat g 1 1 = b ^ 2 ^ (a + 1) := by
    have h := hρ' 0 0
    simp only [minorIdx_zero, h00, h10] at h
    linear_combination h
  have h21 : glMat g 2 1 = 0 := by
    have h := hρ' 1 0
    simp only [minorIdx_zero, minorIdx_one, h00, h10, h20, zero_pow hθ0] at h
    exact (mul_eq_zero.mp (by linear_combination h)).resolve_left hb
  have h31 : glMat g 3 1 = 0 := by
    have h := hW' 0 1
    simp only [h00, h10, h20, h30, h21, minorJ_apply] at h
    norm_num at h
    exact h.resolve_left hb
  have h33' : b * glMat g 3 3 = 1 := by
    have h := hW' 0 3
    simp only [h00, h10, h20, h30, minorJ_apply] at h
    norm_num at h
    linear_combination h
  have h32 : glMat g 3 2 = 0 := by
    have h := hW' 0 2
    simp only [h00, h10, h20, h30, minorJ_apply] at h
    norm_num at h
    exact h.resolve_left hb
  have h22' : glMat g 1 1 * glMat g 2 2 = 1 := by
    have h := hW' 1 2
    simp only [h21, h31, h32, minorJ_apply] at h
    norm_num at h
    linear_combination h
  obtain ⟨l, hl⟩ := hbij.2 (Units.mk0 b hb)
  have hlb : (l : K) * (l : K) ^ 2 ^ a = b := by
    have h := congrArg Units.val hl
    simp only [Units.val_mk0] at h
    rw [← h, _root_.zpow_add, zpow_one, zpow_two_pow_eq, Units.val_mul, Units.val_pow_eq_pow_val]
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hm0 : (l : K) ^ 2 ^ a ≠ 0 := pow_ne_zero _ hl0
  have hmθ : ((l : K) ^ 2 ^ a) ^ 2 ^ (a + 1) = l := by
    rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring, pow_card_suzuki a hK]
  have hlθ : (l : K) ^ 2 ^ (a + 1) = ((l : K) ^ 2 ^ a) ^ 2 := by
    rw [← pow_mul, ← pow_succ]
  have h11 : glMat g 1 1 = (l : K) ^ 2 ^ a := by
    apply mul_left_cancel₀ hb
    rw [E1, ← hlb, mul_pow, hlθ, hmθ]
    ring
  have h22 : glMat g 2 2 = ((l : K) ^ 2 ^ a)⁻¹ := by
    rw [h11] at h22'
    exact eq_inv_of_mul_eq_one_right h22'
  have h33 : glMat g 3 3 = ((l : K) * (l : K) ^ 2 ^ a)⁻¹ := by
    rw [hlb]
    exact eq_inv_of_mul_eq_one_right h33'
  set M : GL (Fin 4) K := ((suzukiDElt a K l : suzukiGroup a K) : GL (Fin 4) K)⁻¹ * g with hMdef
  have hM : M ∈ minorFixGroup K (a + 1) :=
    mul_mem (inv_mem (suzukiGroup_le_minorFixGroup a hK (suzukiDElt a K l).2)) hg
  have hMmat : ∀ i j, glMat M i j = ![((l : K) * (l : K) ^ 2 ^ a)⁻¹, ((l : K) ^ 2 ^ a)⁻¹,
      (l : K) ^ 2 ^ a, (l : K) * (l : K) ^ 2 ^ a] i * glMat g i j := fun i j => by
    have hD : ((((suzukiDElt a K l : suzukiGroup a K) : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = suzukiD a l⁻¹ := by
      rw [← Subgroup.coe_inv, suzukiDElt_inv]
      rfl
    rw [hMdef, glMat, Units.val_mul, hD, suzukiD_inv_eq, Matrix.diagonal_mul]
  obtain ⟨hMW, hMρ⟩ := mem_minorFixGroup.mp hM
  have hMeq := eq_W_suzukiS_W a hθθ hMW hMρ
    (by rw [hMmat, h00, ← hlb]; simp; field_simp)
    (by rw [hMmat, h11]; simp [hm0])
    (by rw [hMmat, h22]; simp [hm0])
    (by rw [hMmat, h33]; simp; field_simp)
    (by rw [hMmat, h10]; simp) (by rw [hMmat, h20]; simp) (by rw [hMmat, h30]; simp)
    (by rw [hMmat, h21]; simp) (by rw [hMmat, h31]; simp) (by rw [hMmat, h32]; simp)
  have hMS : M ∈ suzukiGroup a K := by
    have : M = ((suzukiWElt a K * suzukiSElt a K (glMat M 0 1)
        (glMat M 0 2 + glMat M 0 1 ^ (2 ^ (a + 1) + 1)) * suzukiWElt a K : suzukiGroup a K) :
          GL (Fin 4) K) := Units.ext hMeq
    rw [this]
    exact Subtype.property _
  have hgM : g = ((suzukiDElt a K l : suzukiGroup a K) : GL (Fin 4) K) * M := by
    rw [hMdef, mul_inv_cancel_left]
  rw [hgM]
  exact mul_mem (suzukiDElt a K l).2 hMS

end SpChain

open SpChain

theorem suzuki_exterior_square_matrix_characterization (a : ℕ) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.LinearAlgebra.exteriorSquareJ K = suzukiW K ∧
    (suzukiGroup a K : Set (GL (Fin 4) K)) =
      {g : GL (Fin 4) K | (g : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K * g = suzukiW K ∧
        CFSG.LinearAlgebra.exteriorSquareMinor (g : Matrix (Fin 4) (Fin 4) K) =
          (g : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ (a + 1))} := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  refine ⟨rfl, Set.ext fun g => ⟨fun hg => mem_minorFixGroup.mp
    (suzukiGroup_le_minorFixGroup a hK hg), fun hg => ?_⟩⟩
  have hgX : g ∈ minorFixGroup K (a + 1) := mem_minorFixGroup.mpr hg
  have hx : (fun i => glMat g i 0) ≠ 0 := by
    intro h0
    have h := congrFun (congrFun g.inv_mul 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_four] at h
    have h0' : ∀ i, glMat g i 0 = 0 := fun i => congrFun h0 i
    simp only [glMat] at h0'
    rw [h0', h0', h0', h0'] at h
    simp at h
  set P := Projectivization.mk K (fun i => glMat g i 0) hx with hP
  have hΩ : P ∈ suzukiOmega a K := col_zero_mem_suzukiOmega a hg.1 hg.2 hx
  obtain ⟨-, htrans, -⟩ := suzuki_ovoid_double_transitivity (a := a) hK
  have hl00 : suzukiLine a K 0 0 ∈ suzukiOmega a K := suzukiLine_mem_suzukiOmega a K 0 0
  have hinf : suzukiInfty K ∈ suzukiOmega a K := suzukiInfty_mem_suzukiOmega a K
  have hne : suzukiLine a K 0 0 ≠ suzukiInfty K := suzukiLine_ne_suzukiInfty 0 0
  obtain ⟨w, hw⟩ : ∃ w : suzukiGroup a K, w • P = suzukiLine a K 0 0 := by
    by_cases hPi : P = suzukiInfty K
    · obtain ⟨w, hw, -⟩ := htrans P hΩ _ hl00 _ hl00 _ hinf (by rw [hPi]; exact hne.symm) hne
      exact ⟨w, hw⟩
    · obtain ⟨w, hw, -⟩ := htrans P hΩ _ hinf _ hl00 _ hinf hPi hne
      exact ⟨w, hw⟩
  rw [hP, Subgroup.smul_def, Projectivization.smul_mk, suzukiLine, Projectivization.mk_eq_mk_iff]
    at hw
  obtain ⟨b, hb⟩ := hw
  have hcol : ∀ i, glMat ((w : GL (Fin 4) K) * g) i 0 =
      (b • (![1, 0, 0, suzukiN a 0 0] : Fin 4 → K)) i := fun i => by
    rw [hb]
    rfl
  have hN0 : suzukiN a (0 : K) 0 = 0 := by simp [suzukiN]
  have hwg : (w : GL (Fin 4) K) * g ∈ suzukiGroup a K :=
    mem_suzukiGroup_of_col_zero a hK
      (mul_mem (suzukiGroup_le_minorFixGroup a hK w.2) hgX) b.ne_zero
      (by rw [hcol]; simp [Units.smul_def]) (by rw [hcol]; simp) (by rw [hcol]; simp)
      (by rw [hcol]; simp [hN0])
  have hg' : g = ((w : GL (Fin 4) K))⁻¹ * ((w : GL (Fin 4) K) * g) := by
    rw [inv_mul_cancel_left]
  rw [hg']
  exact mul_mem (inv_mem w.2) hwg

end CFSG.ComponentClassification.UnbalancedCatalog
