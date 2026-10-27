module

public import CFSG.ClassicalInvolution.Asc77.AscCX4U3
public import CFSG.ClassicalInvolution.Asc77.AscCX4L2

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.U4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def g0M (σ : K ≃+* K) (c m n : K) : Matrix (Fin 4) (Fin 4) K :=
  !![σ c, 0, σ c, 0; 0, c, 0, m / n * c; -σ c, 0, σ c, 0; 0, -(n / m * c), 0, c]

omit [Finite K] in
theorem det_g0M (σ : K ≃+* K) {c m n : K} (h2 : (2 : K) ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hN : σ c * c = 2⁻¹) : (g0M σ c m n).det = 1 := by
  simp [g0M, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  have hmn : m / n * (n / m) = 1 := by field_simp
  have h2i : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination (2 * (σ c * c) ^ 2) * hmn + 4 * (σ c * c + 2⁻¹) * hN +
    (2 * 2⁻¹ + 1) * h2i

omit [Finite K] in
theorem unitary_g0M (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) {c m n : K} (h2 : (2 : K) ≠ 0)
    (hm : m ≠ 0) (hn : n ≠ 0) (hσm : σ m = m⁻¹) (hσn : σ n = n⁻¹) (hN : σ c * c = 2⁻¹) :
    conjTr σ (g0M σ c m n) * g0M σ c m n = 1 := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hN
    exact inv_ne_zero h2 hN.symm
  have hσc : σ c = 2⁻¹ * c⁻¹ := (eq_mul_inv_iff_mul_eq₀ hc).mpr hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, g0M, Matrix.mul_apply, Fin.sum_univ_four, hσσ, map_div₀, hσm, hσn] <;>
    rw [hσc] <;> field_simp <;> ring

omit [Finite K] in
theorem fixed_g0M (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) {c m n : K} (hm : m ≠ 0) (hn : n ≠ 0)
    (hσm : σ m = m⁻¹) (hσn : σ n = n⁻¹) :
    !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] * σ.mapMatrix (g0M σ c m n) =
      g0M σ c m n * !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g0M, Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply, hσσ, map_div₀,
      hσm, hσn] <;> field_simp

omit [Finite K] in
theorem g0M_mul_z (σ : K ≃+* K) {c m n : K} (hm : m ≠ 0) (hn : n ≠ 0) :
    g0M σ c m n * !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      L4.wMat m n * g0M σ c m n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g0M, L4.wMat, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

omit [Finite K] in
theorem j_mul_ji {m n : K} (hm : m ≠ 0) (hn : n ≠ 0) :
    (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] : Matrix (Fin 4) (Fin 4) K) *
      !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hm, hn]

theorem comm_of_sq {X : Type} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : b * a = a * b :=
  calc b * a = b * a * (a * b * (a * b)) := by rw [hab, mul_one]
    _ = b * (a * a) * b * (a * b) := by group
    _ = a * b := by rw [ha, mul_one, hb, one_mul]

theorem twisted_witness (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {X : Type} [Group X]
    (θ : Su K p f 4 →* X) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    (hneg : ∀ x : Su K p f 4, suMat x = -1 → θ x = 1) (s : MulAut X)
    (α : Su K p f 4 →* Su K p f 4) (hα : ∀ x, θ (α x) = s (θ x)) {m n : K} (hm : m ≠ 0)
    (hn : n ≠ 0) (hNm : unitaryInvolution K p f m * m = 1)
    (hNn : unitaryInvolution K p f n * n = 1)
    (hαM : ∀ x, suMat (α x) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
      (unitaryInvolution K p f).mapMatrix (suMat x) *
        !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0]) :
    ∃ x : X, s x = x ∧
      x * θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) * x⁻¹ ≠
        θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) ∧
      x * θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) * x⁻¹ *
          θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) =
        θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) *
          (x * θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) * x⁻¹) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  have hσm : unitaryInvolution K p f m = m⁻¹ := eq_inv_of_mul_eq_one_left hNm
  have hσn : unitaryInvolution K p f n = n⁻¹ := eq_inv_of_mul_eq_one_left hNn
  obtain ⟨c, hc⟩ := hσ.exists_norm (d := (2 : K)⁻¹) (by rw [map_inv₀, map_ofNat])
  obtain ⟨g, hgM⟩ : ∃ g : Su K p f 4, suMat g = g0M (unitaryInvolution K p f) c m n :=
    ⟨mkSU K p f _ (det_g0M _ h2 hm hn hc) (unitary_g0M _ hσσ h2 hm hn hσm hσn hc),
      suMat_mkSU _ _⟩
  obtain ⟨w, hw⟩ : ∃ w : Su K p f 4, w = g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹ :=
    ⟨_, rfl⟩
  have hwM : suMat w = L4.wMat m n := by
    have h1 : suMat g * suMat g⁻¹ = 1 := by rw [← suMat_mul, mul_inv_cancel, suMat_one]
    rw [hw, suMat_mul, suMat_mul, suMat_rootInvSU_four, hgM, g0M_mul_z _ hm hn,
      Matrix.mul_assoc, ← hgM, h1, Matrix.mul_one]
  have hww : w * w = 1 := by
    rw [hw]
    calc g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹ *
          (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹) =
        g * (rootInvSU K p f (show 2 ≤ 4 by norm_num) *
          rootInvSU K p f (show 2 ≤ 4 by norm_num)) * g⁻¹ := by group
      _ = 1 := by rw [rootInvSU_mul_self_four, mul_one, mul_inv_cancel]
  have hconj : θ g * θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) * (θ g)⁻¹ = θ w := by
    rw [hw, map_mul, map_mul, map_inv]
  refine ⟨θ g, ?_, ?_, ?_⟩
  · rw [← hα]
    congr 1
    apply suMat_injective
    rw [hαM, hgM, fixed_g0M _ hσσ hm hn hσm hσn, Matrix.mul_assoc, j_mul_ji hm hn,
      Matrix.mul_one]
  · rw [hconj]
    intro h
    have hmem : w * (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹ ∈
        Subgroup.center (Su K p f 4) :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel])
    obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hmem
    have hu' : suMat (w * (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹) =
        Matrix.scalar (Fin 4) (u : K) := hu
    rw [suMat_mul, hwM, suMat_rootInvSU_inv_four] at hu'
    have e := congrFun (congrFun hu' 0) 0
    simp [L4.wMat, Matrix.mul_apply, Fin.sum_univ_four] at e
    exact u.ne_zero e.symm
  · rw [hconj]
    have hzw : suMat (rootInvSU K p f (show 2 ≤ 4 by norm_num) * w *
        (rootInvSU K p f (show 2 ≤ 4 by norm_num) * w)) = -1 := by
      simp only [suMat_mul]
      rw [hwM, suMat_rootInvSU_four, L4.z_mul_w_sq hm hn]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h1 := hneg _ hzw
    rw [map_mul, map_mul] at h1
    refine comm_of_sq ?_ ?_ h1
    · rw [← map_mul, rootInvSU_mul_self_four, map_one]
    · rw [← map_mul, hww, map_one]

theorem fix_invol (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq1 : p ^ f % 4 = 1) {X : Type} [Group X] (θ : Su K p f 4 →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    (hneg : ∀ x : Su K p f 4, suMat x = -1 → θ x = 1) (s : MulAut X)
    (hfix0 : ∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A)) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hsz : s ≠ MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)))) :
    ∃ x : X, s x = x ∧
      x * θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) * x⁻¹ ≠
        θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) ∧
      x * θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) * x⁻¹ *
          θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) =
        θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) *
          (x * θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) * x⁻¹) := by
  rcases two_elem_cases hK hp hq hq1 θ hθ hker s hfix0 hfix2 (k := 1)
      (by rw [pow_one, pow_two]; exact hs2) with (h | h) | ⟨α, hα, m, n, hm, hn, hNm, hNn, hαM⟩
  · exact absurd h hs1
  · exact absurd h hsz
  · exact twisted_witness hK hp θ hker hneg s α hα hm hn hNm hNn hαM

end CFSG.ClassicalInvolution.Asc77.CX.CX4.U4
