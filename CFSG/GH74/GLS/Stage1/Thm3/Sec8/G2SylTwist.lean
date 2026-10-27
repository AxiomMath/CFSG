module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylDefs
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

open CFSG.LieType.Chevalley CFSG.RankThree.Classical Subgroup
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem HSL_mul' (a b : Kˣ) : HSL a * HSL b = HSL (a * b) := by
  apply SL2_ext <;> simp [coe_HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_one' : HSL (1 : Kˣ) = (1 : SL2 K) := by
  apply SL2_ext <;> simp [coe_HSL]

theorem HSL_neg_one_eq : HSL (-1 : Kˣ) = (-1 : SL2 K) := by
  apply SL2_ext <;> simp [coe_HSL]

theorem HSL_pow (a : Kˣ) (m : ℕ) : (HSL a : SL2 K) ^ m = HSL (a ^ m) := by
  induction m with
  | zero => simp [HSL_one']
  | succ m ih => rw [pow_succ, ih, HSL_mul', ← pow_succ]

theorem WSL_mul_WSL' : (WSL : SL2 K) * WSL = -1 := by
  apply SL2_ext <;> simp [coe_WSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem WSL_conj_HSL (a : Kˣ) : (WSL : SL2 K) * HSL a * WSL⁻¹ = HSL a⁻¹ := by
  have h1 : (WSL : SL2 K) * HSL a = HSL a⁻¹ * WSL := by
    apply SL2_ext <;> simp [coe_WSL, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]


theorem matrix_scalar_of_comm (P : Matrix (Fin 2) (Fin 2) K)
    (hu : P * !![1, 1; 0, 1] = !![1, 1; 0, 1] * P) (hv : P * !![1, 0; 1, 1] = !![1, 0; 1, 1] * P) :
    P = Matrix.scalar (Fin 2) (P 0 0) := by
  have u00 := congrFun (congrFun hu 0) 0
  have u01 := congrFun (congrFun hu 0) 1
  have v00 := congrFun (congrFun hv 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at u00 u01 v00
  have h11 : P 1 1 = P 0 0 := by rw [v00] at u01; linear_combination -u01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11, u00, v00]

theorem sl2_eq_one_or_neg_one_of_comm (A : SL2 K) (h : ∀ M : SL2 K, A * M = M * A) :
    A = 1 ∨ A = -1 := by
  have hu := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K)) (h (uSL 1))
  have hv := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K)) (h (vSL 1))
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL] at hu hv
  have hs := matrix_scalar_of_comm _ hu hv
  have hdet := det_SL2 A
  have h00 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by rw [hs]; simp
  have h10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by rw [hs]; simp
  have h11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    rw [hs]; simp
  rw [h00, h10, h11] at hdet
  have hsq : ((A : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((A : Matrix (Fin 2) (Fin 2) K) 0 0 + 1) = 0 := by
    linear_combination hdet
  rcases mul_eq_zero.1 hsq with h1 | h1
  · left
    apply SL2_ext <;> simp [h00, h10, h11, sub_eq_zero.1 h1]
  · right
    apply SL2_ext <;> simp [h00, h10, h11, eq_neg_of_add_eq_zero_left h1]


theorem isSquare_of_conjSL_eq (l : Kˣ) (A : SL2 K)
    (h : ∀ M : SL2 K, conjSL (diagUnitOne l) M = A * M * A⁻¹) : ∃ p : K, (l : K) = p * p := by
  set D : Matrix (Fin 2) (Fin 2) K := (diagUnitOne l : Matrix (Fin 2) (Fin 2) K) with hD
  set D' : Matrix (Fin 2) (Fin 2) K := (↑(diagUnitOne l)⁻¹ : Matrix (Fin 2) (Fin 2) K) with hD'
  have hDD : D' * D = 1 := by
    rw [hD, hD']; exact (diagUnitOne l).inv_mul
  set B : Matrix (Fin 2) (Fin 2) K := ((A⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K) with hB
  set A' : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hA'
  have hBA : B * A' = 1 := by
    rw [hB, hA', ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have key : ∀ M : SL2 K, (B * D) * (M : Matrix (Fin 2) (Fin 2) K) =
      (M : Matrix (Fin 2) (Fin 2) K) * (B * D) := by
    intro M
    set M' : Matrix (Fin 2) (Fin 2) K := (M : Matrix (Fin 2) (Fin 2) K) with hM'
    have hM := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K)) (h M)
    simp only [coe_conjSL, Matrix.SpecialLinearGroup.coe_mul] at hM
    have hM2 : D * M' * D' = A' * M' * B := hM
    have e1 : B * D * M' = B * (D * M' * D') * D := by
      have : D * M' * D' * D = D * M' := by
        rw [Matrix.mul_assoc (D * M'), hDD, Matrix.mul_one]
      calc B * D * M' = B * (D * M') := by rw [Matrix.mul_assoc]
        _ = B * (D * M' * D' * D) := by rw [this]
        _ = B * (D * M' * D') * D := by rw [Matrix.mul_assoc B]
    rw [e1, hM2]
    calc B * (A' * M' * B) * D = (B * A') * M' * (B * D) := by simp only [Matrix.mul_assoc]
      _ = M' * (B * D) := by rw [hBA, Matrix.one_mul]
  have hs := matrix_scalar_of_comm (B * D) (key (uSL 1)) (key (vSL 1))
  refine ⟨(B * D) 0 0, ?_⟩
  have hdet : (B * D).det = (l : K) := by
    rw [Matrix.det_mul, hB, hD]
    have : ((A⁻¹ : SL2 K) : Matrix (Fin 2) (Fin 2) K).det = 1 := (A⁻¹).2
    rw [this, one_mul]
    simp [coe_diagUnitOne, Matrix.det_fin_two]
  rw [hs] at hdet
  simp at hdet
  rw [← hdet]; ring


structure TwistedPair (K : Type) [Field K] (G : Type*) [Group G] where
  ρ₁ : SL2 K →* G
  ρ₂ : SL2 K →* G
  g : G
  l : Kˣ
  comm : ∀ A B, ρ₁ A * ρ₂ B = ρ₂ B * ρ₁ A
  neg : ρ₁ (HSL (-1)) = ρ₂ (HSL (-1))
  inj₁ : Function.Injective ρ₁
  inj₂ : Function.Injective ρ₂
  conj₁ : ∀ A, g * ρ₁ A * g⁻¹ = ρ₁ (conjSL (diagUnitOne l) A)
  conj₂ : ∀ A, g * ρ₂ A * g⁻¹ = ρ₂ (conjSL (diagUnitOne l) A)
  sq : g * g = ρ₁ (HSL l) * ρ₂ (HSL l)
  nonsq : ∀ p : K, (l : K) ≠ p * p

namespace TwistedPair

variable {G : Type*} [Group G] (T : TwistedPair K G)

@[expose] def mu : SL2 K × SL2 K →* G :=
  T.ρ₁.noncommCoprod T.ρ₂ (fun A B => T.comm A B)

theorem mu_apply (A B : SL2 K) : T.mu (A, B) = T.ρ₁ A * T.ρ₂ B := rfl

@[expose] def restrict (H : Subgroup G) (h₁ : ∀ A, T.ρ₁ A ∈ H) (h₂ : ∀ A, T.ρ₂ A ∈ H) (hg : T.g ∈ H) :
    TwistedPair K H where
  ρ₁ := T.ρ₁.codRestrict H h₁
  ρ₂ := T.ρ₂.codRestrict H h₂
  g := ⟨T.g, hg⟩
  l := T.l
  comm A B := Subtype.ext (T.comm A B)
  neg := Subtype.ext T.neg
  inj₁ := fun _ _ h => T.inj₁ (congrArg Subtype.val h)
  inj₂ := fun _ _ h => T.inj₂ (congrArg Subtype.val h)
  conj₁ A := Subtype.ext (T.conj₁ A)
  conj₂ A := Subtype.ext (T.conj₂ A)
  sq := Subtype.ext T.sq
  nonsq := T.nonsq

theorem comm₂₁ (B A : SL2 K) : T.ρ₂ B * T.ρ₁ A = T.ρ₁ A * T.ρ₂ B := (T.comm A B).symm

theorem conj₂₁ (B A : SL2 K) : T.ρ₂ B * T.ρ₁ A * (T.ρ₂ B)⁻¹ = T.ρ₁ A := by
  rw [comm₂₁, mul_assoc, mul_inv_cancel, mul_one]

theorem g_notMem_range : T.g ∉ T.mu.range := by
  rintro ⟨⟨A, B⟩, hAB⟩
  rw [mu_apply] at hAB
  obtain ⟨p, hp⟩ := isSquare_of_conjSL_eq T.l A (fun M => T.inj₁ (by
    rw [← T.conj₁, ← hAB, map_mul, map_mul, map_inv]
    calc T.ρ₁ A * T.ρ₂ B * T.ρ₁ M * (T.ρ₁ A * T.ρ₂ B)⁻¹
        = T.ρ₁ A * (T.ρ₂ B * T.ρ₁ M * (T.ρ₂ B)⁻¹) * (T.ρ₁ A)⁻¹ := by group
      _ = T.ρ₁ A * T.ρ₁ M * (T.ρ₁ A)⁻¹ := by rw [conj₂₁]))
  exact T.nonsq p hp

theorem rho₁_mem_range (A : SL2 K) : T.ρ₁ A ∈ T.mu.range := ⟨(A, 1), by simp [mu_apply]⟩

theorem rho₂_mem_range (B : SL2 K) : T.ρ₂ B ∈ T.mu.range := ⟨(1, B), by simp [mu_apply]⟩

theorem inter_le {c : SL2 K} {m : ℕ} (hc : c ^ m = -1) :
    Subgroup.zpowers (T.ρ₁ c) ⊓ Subgroup.zpowers (T.ρ₂ c) ≤ Subgroup.zpowers (T.ρ₁ c ^ m) := by
  rintro x ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hi' : T.ρ₁ (c ^ i) = x := by rw [map_zpow]; exact hi
  have hj' : T.ρ₂ (c ^ j) = x := by rw [map_zpow]; exact hj
  have hcen : ∀ M : SL2 K, c ^ i * M = M * c ^ i := by
    intro M
    apply T.inj₁
    rw [map_mul, map_mul, hi', ← hj']
    exact (T.comm M (c ^ j)).symm
  rcases sl2_eq_one_or_neg_one_of_comm _ hcen with h1 | h1
  · rw [h1, map_one] at hi'
    rw [← hi']; exact one_mem _
  · rw [h1] at hi'
    rw [← hi', ← map_pow, hc]
    exact Subgroup.mem_zpowers _

theorem neg_one_ne_one (h2 : (2 : K) ≠ 0) : (-1 : SL2 K) ≠ 1 := by
  intro h
  have := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp at this
  apply h2
  linear_combination -this

theorem rho_neg_one_sq : T.ρ₁ (-1) * T.ρ₁ (-1) = 1 := by
  rw [← map_mul]
  have : (-1 : SL2 K) * -1 = 1 := by simp
  rw [this, map_one]

theorem rho₂_neg_one : T.ρ₂ (-1) = T.ρ₁ (-1) := by
  have := T.neg
  rw [HSL_neg_one_eq] at this
  exact this.symm

theorem qpData_caseI (h2 : (2 : K) ≠ 0) {n : ℕ} {c w : SL2 K} (hn : 2 ≤ n)
    (hc : c ^ (2 ^ n) = 1) (hc2 : c ^ (2 ^ (n - 1)) = -1) (hw : w * w = -1)
    (hwc : w * c * w⁻¹ = c⁻¹) (hl : HSL T.l = c) (hcδ : conjSL (diagUnitOne T.l) c = c)
    (hwδ : conjSL (diagUnitOne T.l) w = c * w) :
    QPData n 1 1 (T.ρ₁ c) (T.ρ₂ c) (T.ρ₁ w) (T.ρ₂ w) T.g := by
  have hz₁ : T.ρ₁ c ^ (2 ^ (n - 1)) = T.ρ₁ (-1) := by rw [← map_pow, hc2]
  have hz₂ : T.ρ₂ c ^ (2 ^ (n - 1)) = T.ρ₁ (-1) := by rw [← map_pow, hc2, rho₂_neg_one]
  have hδ₁ := T.conj₁ c
  have hδ₂ := T.conj₂ c
  rw [hcδ] at hδ₁ hδ₂
  have hw₁ := T.conj₁ w
  have hw₂ := T.conj₂ w
  rw [hwδ, map_mul] at hw₁ hw₂
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, odd_one, odd_one, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hc, map_one]
  · rw [← map_pow, hc, map_one]
  · rw [hz₁]; intro h; exact neg_one_ne_one h2 (T.inj₁ (by rw [h, map_one]))
  · rw [hz₂, hz₁]
  · rw [← map_mul, hw, hz₁]
  · rw [← map_mul, hw, rho₂_neg_one, hz₁]
  · rw [← map_mul, ← map_inv, ← map_mul, hwc, map_inv]
  · rw [← map_mul, ← map_inv, ← map_mul, hwc, map_inv]
  · exact T.comm c c
  · exact T.comm c w
  · exact T.comm w c
  · exact T.comm w w
  · exact mul_inv_eq_iff_eq_mul.1 hδ₁
  · exact mul_inv_eq_iff_eq_mul.1 hδ₂
  · rw [pow_one]; exact hw₁
  · rw [pow_one]; exact hw₂
  · rw [pow_one, pow_one, T.sq, hl]
  · exact T.inter_le hc2
  · intro hmem
    have hle : Subgroup.closure ({T.ρ₁ c, T.ρ₂ c} : Set G) ≤ T.mu.range := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact T.rho₁_mem_range c
      · exact T.rho₂_mem_range c
    exact T.g_notMem_range (hle hmem)

theorem g_sq_of_neg_one (hl : T.l = -1) : T.g * T.g = 1 := by
  rw [T.sq, hl, T.neg, ← map_mul, HSL_mul', show (-1 : Kˣ) * -1 = 1 by simp, HSL_one', map_one]

theorem qpData_caseII (h2 : (2 : K) ≠ 0) {n s : ℕ} {c w : SL2 K} (hn : 2 ≤ n) (hs : Odd s)
    (hc : c ^ (2 ^ n) = 1) (hc2 : c ^ (2 ^ (n - 1)) = -1) (hw : w * w = -1)
    (hwc : w * c * w⁻¹ = c⁻¹) (hl : T.l = -1) (hcδ : conjSL (diagUnitOne T.l) c = c⁻¹)
    (hwδ : conjSL (diagUnitOne T.l) w = c ^ s * w) :
    QPData n s s (T.ρ₁ c) (T.ρ₂ c) (T.ρ₁ w) (T.ρ₂ w) (T.g * (T.ρ₁ w * T.ρ₂ w)) := by
  have hz₁ : T.ρ₁ c ^ (2 ^ (n - 1)) = T.ρ₁ (-1) := by rw [← map_pow, hc2]
  have hz₂ : T.ρ₂ c ^ (2 ^ (n - 1)) = T.ρ₁ (-1) := by rw [← map_pow, hc2, rho₂_neg_one]
  have hww₁ : T.ρ₁ w * T.ρ₁ w = T.ρ₁ (-1) := by rw [← map_mul, hw]
  have hww₂ : T.ρ₂ w * T.ρ₂ w = T.ρ₁ (-1) := by rw [← map_mul, hw, rho₂_neg_one]
  have hg2 : T.g * T.g = 1 := g_sq_of_neg_one T hl
  have hginv : T.g⁻¹ = T.g := inv_eq_of_mul_eq_one_right hg2
  have hy2 : (T.ρ₁ w * T.ρ₂ w) * (T.ρ₁ w * T.ρ₂ w) = 1 := by
    calc (T.ρ₁ w * T.ρ₂ w) * (T.ρ₁ w * T.ρ₂ w)
        = (T.ρ₁ w * T.ρ₁ w) * (T.ρ₂ w * T.ρ₂ w) := by
          rw [mul_assoc, ← mul_assoc (T.ρ₂ w), T.comm₂₁, mul_assoc (T.ρ₁ w), ← mul_assoc]
      _ = 1 := by rw [hww₁, hww₂, rho_neg_one_sq]
  have hy_c₁ : (T.ρ₁ w * T.ρ₂ w) * T.ρ₁ c * (T.ρ₁ w * T.ρ₂ w)⁻¹ = (T.ρ₁ c)⁻¹ := by
    calc (T.ρ₁ w * T.ρ₂ w) * T.ρ₁ c * (T.ρ₁ w * T.ρ₂ w)⁻¹
        = T.ρ₁ w * (T.ρ₂ w * T.ρ₁ c * (T.ρ₂ w)⁻¹) * (T.ρ₁ w)⁻¹ := by group
      _ = T.ρ₁ (w * c * w⁻¹) := by rw [conj₂₁, map_mul, map_mul, map_inv]
      _ = (T.ρ₁ c)⁻¹ := by rw [hwc, map_inv]
  have hy_c₂ : (T.ρ₁ w * T.ρ₂ w) * T.ρ₂ c * (T.ρ₁ w * T.ρ₂ w)⁻¹ = (T.ρ₂ c)⁻¹ := by
    have h1 : T.ρ₂ w * T.ρ₂ c * (T.ρ₂ w)⁻¹ = (T.ρ₂ c)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hwc, map_inv]
    have h2' : T.ρ₁ w * (T.ρ₂ c)⁻¹ * (T.ρ₁ w)⁻¹ = (T.ρ₂ c)⁻¹ := by
      have h := T.comm w c⁻¹
      rw [map_inv] at h
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    calc (T.ρ₁ w * T.ρ₂ w) * T.ρ₂ c * (T.ρ₁ w * T.ρ₂ w)⁻¹
        = T.ρ₁ w * (T.ρ₂ w * T.ρ₂ c * (T.ρ₂ w)⁻¹) * (T.ρ₁ w)⁻¹ := by group
      _ = (T.ρ₂ c)⁻¹ := by rw [h1, h2']
  have hy_w₁ : (T.ρ₁ w * T.ρ₂ w) * T.ρ₁ w * (T.ρ₁ w * T.ρ₂ w)⁻¹ = T.ρ₁ w := by
    calc (T.ρ₁ w * T.ρ₂ w) * T.ρ₁ w * (T.ρ₁ w * T.ρ₂ w)⁻¹
        = T.ρ₁ w * (T.ρ₂ w * T.ρ₁ w * (T.ρ₂ w)⁻¹) * (T.ρ₁ w)⁻¹ := by group
      _ = T.ρ₁ w := by rw [conj₂₁]; group
  have hy_w₂ : (T.ρ₁ w * T.ρ₂ w) * T.ρ₂ w * (T.ρ₁ w * T.ρ₂ w)⁻¹ = T.ρ₂ w := by
    calc (T.ρ₁ w * T.ρ₂ w) * T.ρ₂ w * (T.ρ₁ w * T.ρ₂ w)⁻¹
        = T.ρ₁ w * (T.ρ₂ w * T.ρ₂ w * (T.ρ₂ w)⁻¹) * (T.ρ₁ w)⁻¹ := by group
      _ = T.ρ₂ w := by
        rw [mul_assoc (T.ρ₂ w), mul_inv_cancel, mul_one, T.comm w w, mul_assoc, mul_inv_cancel, mul_one]
  have hg_c₁ : T.g * T.ρ₁ c * T.g⁻¹ = (T.ρ₁ c)⁻¹ := by rw [T.conj₁, hcδ, map_inv]
  have hg_c₂ : T.g * T.ρ₂ c * T.g⁻¹ = (T.ρ₂ c)⁻¹ := by rw [T.conj₂, hcδ, map_inv]
  have hg_w₁ : T.g * T.ρ₁ w * T.g⁻¹ = (T.ρ₁ c) ^ s * T.ρ₁ w := by
    rw [T.conj₁, hwδ, map_mul, map_pow]
  have hg_w₂ : T.g * T.ρ₂ w * T.g⁻¹ = (T.ρ₂ c) ^ s * T.ρ₂ w := by
    rw [T.conj₂, hwδ, map_mul, map_pow]
  have hconj : ∀ x y : G, (T.g * x) * y * (T.g * x)⁻¹ = T.g * (x * y * x⁻¹) * T.g⁻¹ := by
    intro x y; group
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hc, map_one]
  · rw [← map_pow, hc, map_one]
  · rw [hz₁]; intro h; exact neg_one_ne_one h2 (T.inj₁ (by rw [h, map_one]))
  · rw [hz₂, hz₁]
  · rw [hww₁, hz₁]
  · rw [hww₂, hz₁]
  · rw [← map_mul, ← map_inv, ← map_mul, hwc, map_inv]
  · rw [← map_mul, ← map_inv, ← map_mul, hwc, map_inv]
  · exact T.comm c c
  · exact T.comm c w
  · exact T.comm w c
  · exact T.comm w w
  · apply mul_inv_eq_iff_eq_mul.1
    rw [hconj, hy_c₁]
    calc T.g * (T.ρ₁ c)⁻¹ * T.g⁻¹ = (T.g * T.ρ₁ c * T.g⁻¹)⁻¹ := by group
      _ = T.ρ₁ c := by rw [hg_c₁, inv_inv]
  · apply mul_inv_eq_iff_eq_mul.1
    rw [hconj, hy_c₂]
    calc T.g * (T.ρ₂ c)⁻¹ * T.g⁻¹ = (T.g * T.ρ₂ c * T.g⁻¹)⁻¹ := by group
      _ = T.ρ₂ c := by rw [hg_c₂, inv_inv]
  · rw [hconj, hy_w₁, hg_w₁]
  · rw [hconj, hy_w₂, hg_w₂]
  · have hcomm : T.ρ₁ w * T.ρ₂ c ^ s = T.ρ₂ c ^ s * T.ρ₁ w := by
      have := T.comm w (c ^ s)
      rwa [map_pow] at this
    have hgy : T.g * (T.ρ₁ w * T.ρ₂ w) * T.g⁻¹ =
        T.ρ₁ c ^ s * T.ρ₂ c ^ s * (T.ρ₁ w * T.ρ₂ w) := by
      calc T.g * (T.ρ₁ w * T.ρ₂ w) * T.g⁻¹
          = (T.g * T.ρ₁ w * T.g⁻¹) * (T.g * T.ρ₂ w * T.g⁻¹) := by group
        _ = (T.ρ₁ c ^ s * T.ρ₁ w) * (T.ρ₂ c ^ s * T.ρ₂ w) := by rw [hg_w₁, hg_w₂]
        _ = T.ρ₁ c ^ s * (T.ρ₁ w * T.ρ₂ c ^ s) * T.ρ₂ w := by group
        _ = T.ρ₁ c ^ s * (T.ρ₂ c ^ s * T.ρ₁ w) * T.ρ₂ w := by rw [hcomm]
        _ = T.ρ₁ c ^ s * T.ρ₂ c ^ s * (T.ρ₁ w * T.ρ₂ w) := by group
    calc (T.g * (T.ρ₁ w * T.ρ₂ w)) * (T.g * (T.ρ₁ w * T.ρ₂ w))
        = (T.g * (T.ρ₁ w * T.ρ₂ w) * T.g⁻¹) * (T.g * T.g) * (T.ρ₁ w * T.ρ₂ w) := by group
      _ = (T.ρ₁ c ^ s * T.ρ₂ c ^ s * (T.ρ₁ w * T.ρ₂ w)) * 1 * (T.ρ₁ w * T.ρ₂ w) := by rw [hgy, hg2]
      _ = T.ρ₁ c ^ s * T.ρ₂ c ^ s * ((T.ρ₁ w * T.ρ₂ w) * (T.ρ₁ w * T.ρ₂ w)) := by group
      _ = T.ρ₁ c ^ s * T.ρ₂ c ^ s := by rw [hy2, mul_one]
  · exact T.inter_le hc2
  · intro hmem
    have hle : Subgroup.closure ({T.ρ₁ c, T.ρ₂ c} : Set G) ≤ T.mu.range := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact T.rho₁_mem_range c
      · exact T.rho₂_mem_range c
    have hy : T.ρ₁ w * T.ρ₂ w ∈ T.mu.range := T.mu.range.mul_mem (T.rho₁_mem_range w) (T.rho₂_mem_range w)
    apply T.g_notMem_range
    have := T.mu.range.mul_mem (hle hmem) (T.mu.range.inv_mem hy)
    rwa [mul_inv_cancel_right] at this

end TwistedPair

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
