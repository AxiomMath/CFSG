module

public import CFSG.ClassicalInvolution.Phan.PhanB19Fields

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock mat_longBlock det_stdBlock_eq_one
  mem_coords stdBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

section Poly

variable {F : Type} [Field F]

theorem cent_entries (t x0 x1 : F) (ht : 2 * t = 1) (hx : x0 * x0 + x1 * x1 = 1) (hx0 : x0 ≠ 1)
    (hx1 : x1 ≠ 0) (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hL : G * Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
        !![x0, t * x1; -(2 * x1), x0] =
      Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![x0, t * x1; -(2 * x1), x0] * G)
    (hS : G * twMat t !![x0, -x1; x1, x0] = twMat t !![x0, -x1; x1, x0] * G) :
    G (Sum.inl 0) (Sum.inl 1) = 0 ∧ G (Sum.inl 1) (Sum.inl 0) = 0 ∧
    G (Sum.inr 0) (Sum.inr 1) = 0 ∧ G (Sum.inr 1) (Sum.inr 0) = 0 ∧
    G (Sum.inl 0) (Sum.inr 1) = 0 ∧ G (Sum.inl 1) (Sum.inr 0) = 0 ∧
    G (Sum.inr 0) (Sum.inl 1) = 0 ∧ G (Sum.inr 1) (Sum.inl 0) = 0 ∧
    G (Sum.inr 0) (Sum.inr 0) = G (Sum.inl 0) (Sum.inl 0) ∧
    G (Sum.inr 1) (Sum.inr 1) = G (Sum.inl 1) (Sum.inl 1) ∧
    G (Sum.inr 0) (Sum.inl 0) = -4 * G (Sum.inl 0) (Sum.inr 0) ∧
    G (Sum.inr 1) (Sum.inl 1) = -4 * G (Sum.inl 1) (Sum.inr 1) := by
  have hLe : ∀ i j, (G * Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
        !![x0, t * x1; -(2 * x1), x0]) i j =
      (Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![x0, t * x1; -(2 * x1), x0] *
        G) i j := fun i j => by rw [hL]
  have hSe : ∀ i j, (G * twMat t !![x0, -x1; x1, x0]) i j =
      (twMat t !![x0, -x1; x1, x0] * G) i j := fun i j => by rw [hS]
  have l0 := hLe (Sum.inl 0) (Sum.inl 0)
  have l1 := hLe (Sum.inl 0) (Sum.inl 1)
  have l2 := hLe (Sum.inl 0) (Sum.inr 0)
  have l3 := hLe (Sum.inl 0) (Sum.inr 1)
  have l4 := hLe (Sum.inl 1) (Sum.inl 0)
  have l5 := hLe (Sum.inl 1) (Sum.inl 1)
  have l6 := hLe (Sum.inl 1) (Sum.inr 0)
  have l7 := hLe (Sum.inl 1) (Sum.inr 1)
  have l8 := hLe (Sum.inr 0) (Sum.inl 0)
  have l9 := hLe (Sum.inr 0) (Sum.inl 1)
  have l10 := hLe (Sum.inr 0) (Sum.inr 0)
  have l11 := hLe (Sum.inr 0) (Sum.inr 1)
  have l12 := hLe (Sum.inr 1) (Sum.inl 0)
  have l13 := hLe (Sum.inr 1) (Sum.inl 1)
  have l14 := hLe (Sum.inr 1) (Sum.inr 0)
  have l15 := hLe (Sum.inr 1) (Sum.inr 1)
  have s0 := hSe (Sum.inl 0) (Sum.inl 0)
  have s1 := hSe (Sum.inl 0) (Sum.inl 1)
  have s2 := hSe (Sum.inl 0) (Sum.inr 0)
  have s3 := hSe (Sum.inl 0) (Sum.inr 1)
  have s4 := hSe (Sum.inl 1) (Sum.inl 0)
  have s5 := hSe (Sum.inl 1) (Sum.inl 1)
  have s6 := hSe (Sum.inl 1) (Sum.inr 0)
  have s7 := hSe (Sum.inl 1) (Sum.inr 1)
  have s8 := hSe (Sum.inr 0) (Sum.inl 0)
  have s9 := hSe (Sum.inr 0) (Sum.inl 1)
  have s10 := hSe (Sum.inr 0) (Sum.inr 0)
  have s11 := hSe (Sum.inr 0) (Sum.inr 1)
  have s12 := hSe (Sum.inr 1) (Sum.inl 0)
  have s13 := hSe (Sum.inr 1) (Sum.inl 1)
  have s14 := hSe (Sum.inr 1) (Sum.inr 0)
  have s15 := hSe (Sum.inr 1) (Sum.inr 1)
  simp [Sp.blockMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.one_apply] at l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15
  simp [twMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
  grind

theorem cent_final_matrix (t : F) (ht : 2 * t = 1) (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (z01 : G (Sum.inl 0) (Sum.inl 1) = 0) (z10 : G (Sum.inl 1) (Sum.inl 0) = 0)
    (z23 : G (Sum.inr 0) (Sum.inr 1) = 0) (z32 : G (Sum.inr 1) (Sum.inr 0) = 0)
    (z03 : G (Sum.inl 0) (Sum.inr 1) = 0) (z12 : G (Sum.inl 1) (Sum.inr 0) = 0)
    (z21 : G (Sum.inr 0) (Sum.inl 1) = 0) (z30 : G (Sum.inr 1) (Sum.inl 0) = 0)
    (e22 : G (Sum.inr 0) (Sum.inr 0) = G (Sum.inl 0) (Sum.inl 0))
    (e33 : G (Sum.inr 1) (Sum.inr 1) = G (Sum.inl 1) (Sum.inl 1))
    (e20 : G (Sum.inr 0) (Sum.inl 0) = -4 * G (Sum.inl 0) (Sum.inr 0))
    (e31 : G (Sum.inr 1) (Sum.inl 1) = -4 * G (Sum.inl 1) (Sum.inr 1))
    (hn0 : G (Sum.inl 0) (Sum.inl 0) * G (Sum.inl 0) (Sum.inl 0) +
      4 * (G (Sum.inl 0) (Sum.inr 0) * G (Sum.inl 0) (Sum.inr 0)) = 1)
    (w0 w1 y0 y1 : F) (hw0 : w0 = G (Sum.inl 0) (Sum.inl 0))
    (hw1 : w1 = -2 * G (Sum.inl 0) (Sum.inr 0))
    (hy0 : y0 = G (Sum.inl 1) (Sum.inl 1) * w0 - 2 * G (Sum.inl 1) (Sum.inr 1) * w1)
    (hy1 : y1 = G (Sum.inl 1) (Sum.inl 1) * w1 + 2 * G (Sum.inl 1) (Sum.inr 1) * w0) :
    G = Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) !![y0, t * y1; -(2 * y1), y0] *
      twMat t !![w0, -w1; w1, w0] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Sp.blockMat, twMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.one_apply] <;> grind

end Poly

section Coord

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] [Algebra F K] (Q : QData F K (unitaryInvolution K p f)) (c d : F)
  (hcd : c * c + d * d = -1) (h2 : (2 : F) ≠ 0)

theorem exists_normOne_coords (a b : F) (h : a * a + b * b = 1) :
    ∃ x : normOne (unitaryInvolution K p f),
      Q.re ((x : Kˣ) : K) = a ∧ Q.im ((x : Kˣ) : K) = b := by
  have hz1 : unitaryInvolution K p f (Q.cpl a b) * Q.cpl a b = 1 := by
    apply Q.re_inj
    · rw [Q.re_mul, Q.re_σ, Q.im_σ, Q.re_one, Q.re_cpl, Q.im_cpl]
      linear_combination h
    · rw [Q.im_mul, Q.re_σ, Q.im_σ, Q.im_one, Q.re_cpl, Q.im_cpl]
      ring
  have hz0 : Q.cpl a b ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hz1
    exact zero_ne_one hz1
  refine ⟨⟨Units.mk0 (Q.cpl a b) hz0, (mem_normOne _).2 hz1⟩, ?_, ?_⟩
  · show Q.re (Q.cpl a b) = a
    exact Q.re_cpl a b
  · show Q.im (Q.cpl a b) = b
    exact Q.im_cpl a b

theorem cent_rel (x₀ : normOne (unitaryInvolution K p f)) (hx₀ : x₀ * x₀ ≠ 1) (g : StatedSp 2 F)
    (h1 : g * lHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x₀) =
      lHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x₀) * g)
    (h3 : g * sHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x₀) =
      sHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) x₀) * g) :
    ∃ y w : normOne (unitaryInvolution K p f),
      g = lHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) y) *
        sHom Q c d hcd h2 (torusTwo (unitaryInvolution K p f) w) := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  have hx := normOne_coord Q x₀
  have hx1 : Q.im ((x₀ : Kˣ) : K) ≠ 0 := by
    intro h0
    apply hx₀
    have hx0sq : Q.re ((x₀ : Kˣ) : K) * Q.re ((x₀ : Kˣ) : K) = 1 := by
      rw [h0] at hx
      linear_combination hx
    have hzz : ((x₀ : Kˣ) : K) * ((x₀ : Kˣ) : K) = 1 := by
      apply Q.re_inj
      · rw [Q.re_mul, Q.re_one, h0]
        linear_combination hx0sq
      · rw [Q.im_mul, Q.im_one, h0]
        ring
    exact Subtype.ext (Units.ext (by simpa using hzz))
  have hx0 : Q.re ((x₀ : Kˣ) : K) ≠ 1 := by
    intro h0
    apply hx1
    rw [h0] at hx
    exact mul_self_eq_zero.mp (by linear_combination hx)
  have hL := congrArg (mat 2 F) h1
  have hS := congrArg (mat 2 F) h3
  rw [map_mul, map_mul, mat_lHom, nuOf_torus] at hL
  rw [map_mul, map_mul, mat_sHom, nuOf_torus] at hS
  have hN : conjD2 (2⁻¹ : F) (nuMat c (-d) (Q.re ((x₀ : Kˣ) : K)) (Q.im ((x₀ : Kˣ) : K)) 0 0) =
      !![Q.re ((x₀ : Kˣ) : K), 2⁻¹ * Q.im ((x₀ : Kˣ) : K);
        -(2 * Q.im ((x₀ : Kˣ) : K)), Q.re ((x₀ : Kˣ) : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjD2, nuMat]
  have hM : nuMat c d (Q.re ((x₀ : Kˣ) : K)) (Q.im ((x₀ : Kˣ) : K)) 0 0 =
      !![Q.re ((x₀ : Kˣ) : K), -Q.im ((x₀ : Kˣ) : K);
        Q.im ((x₀ : Kˣ) : K), Q.re ((x₀ : Kˣ) : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nuMat]
  rw [hN] at hL
  rw [hM] at hS
  obtain ⟨z01, z10, z23, z32, z03, z12, z21, z30, e22, e33, e20, e31⟩ :=
    cent_entries (2⁻¹ : F) _ _ ht hx hx0 hx1 (mat 2 F g) hL hS
  have hd0 := det_stdBlock_eq_one g 0 (by
    intro cc hcc
    rw [mem_coords] at hcc
    rcases cc with cc | cc <;> fin_cases cc <;> simp at hcc ⊢ <;> assumption)
  have hd1 := det_stdBlock_eq_one g 1 (by
    intro cc hcc
    rw [mem_coords] at hcc
    rcases cc with cc | cc <;> fin_cases cc <;> simp at hcc ⊢ <;> assumption)
  simp [stdBlock, Matrix.det_fin_two] at hd0 hd1
  have hn0 : (mat 2 F) g (Sum.inl 0) (Sum.inl 0) * (mat 2 F) g (Sum.inl 0) (Sum.inl 0) +
      4 * ((mat 2 F) g (Sum.inl 0) (Sum.inr 0) * (mat 2 F) g (Sum.inl 0) (Sum.inr 0)) = 1 := by
    rw [e22, e20] at hd0
    linear_combination hd0
  have hn1 : (mat 2 F) g (Sum.inl 1) (Sum.inl 1) * (mat 2 F) g (Sum.inl 1) (Sum.inl 1) +
      4 * ((mat 2 F) g (Sum.inl 1) (Sum.inr 1) * (mat 2 F) g (Sum.inl 1) (Sum.inr 1)) = 1 := by
    rw [e33, e31] at hd1
    linear_combination hd1
  obtain ⟨w, hw0, hw1⟩ := exists_normOne_coords (K := K) Q ((mat 2 F) g (Sum.inl 0) (Sum.inl 0))
    (-2 * (mat 2 F) g (Sum.inl 0) (Sum.inr 0)) (by linear_combination hn0)
  obtain ⟨y, hy0, hy1⟩ := exists_normOne_coords (K := K) Q
    ((mat 2 F) g (Sum.inl 1) (Sum.inl 1) * Q.re ((w : Kˣ) : K) -
      2 * (mat 2 F) g (Sum.inl 1) (Sum.inr 1) * Q.im ((w : Kˣ) : K))
    ((mat 2 F) g (Sum.inl 1) (Sum.inl 1) * Q.im ((w : Kˣ) : K) +
      2 * (mat 2 F) g (Sum.inl 1) (Sum.inr 1) * Q.re ((w : Kˣ) : K))
    (by
      have hw := normOne_coord Q w
      linear_combination (Q.re ((w : Kˣ) : K) * Q.re ((w : Kˣ) : K) +
        Q.im ((w : Kˣ) : K) * Q.im ((w : Kˣ) : K)) * hn1 + hw)
  refine ⟨y, w, ?_⟩
  apply mat_injective
  rw [map_mul, mat_lHom, mat_sHom, nuOf_torus, nuOf_torus, hy0, hy1]
  have hN' : ∀ a b : F, conjD2 (2⁻¹ : F) (nuMat c (-d) a b 0 0) = !![a, 2⁻¹ * b; -(2 * b), a] := by
    intro a b
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjD2, nuMat]
  have hM' : ∀ a b : F, nuMat c d a b 0 0 = !![a, -b; b, a] := by
    intro a b
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nuMat]
  rw [hN', hM']
  exact cent_final_matrix (2⁻¹ : F) ht (mat 2 F g) z01 z10 z23 z32 z03 z12 z21 z30 e22 e33 e20 e31
    hn0 _ _ _ _ hw0 hw1 rfl rfl

end Coord

end CFSG.ClassicalInvolution.PhanB3
