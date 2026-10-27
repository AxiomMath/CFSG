module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuLayerA

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
open scoped MatrixGroups

section GroupA

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (SLayer isQuasisimple_of_equiv)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {ω : K}

local notation "σ₀" => unitaryInvolution K p f

variable (h : AData K p f ω)

theorem AData.omega_ne_neg (h : AData K p f ω) : ω ≠ -ω := by
  intro e
  have h2ω : (2 : K) * ω = 0 := by linear_combination e
  rcases mul_eq_zero.mp h2ω with h' | h'
  · exact h.h2 h'
  · have := h.hω
    rw [h', zero_mul] at this
    exact absurd (show (0 : K) = 1 by linear_combination (-1) * this) zero_ne_one

theorem conj_mem_of_comm {g : Su K p f 4} (hg : g * u0 K p f = u0 K p f * g) {q : Su K p f 4}
    (hq : q ∈ (iotaA h).range) : g * q * g⁻¹ ∈ (iotaA h).range := by
  obtain ⟨B₁, rfl⟩ := hq
  have hYY := Ya_mul_Yai h.h2 h.hω
  have hYiY := Yai_mul_Ya h.h2 h.hω
  have hGcomm : suMat g * suMat (u0 K p f) = suMat (u0 K p f) * suMat g := by
    have := congrArg suMat hg
    rwa [suMat_mul, suMat_mul] at this
  set M := Yai ω * suMat g * Ya ω with hM
  set M' := Yai ω * suMat g⁻¹ * Ya ω with hM'
  have hMΔ : M * Matrix.diagonal ![ω, ω, -ω, -ω] = Matrix.diagonal ![ω, ω, -ω, -ω] * M := by
    calc M * Matrix.diagonal ![ω, ω, -ω, -ω]
        = Yai ω * suMat g * (Ya ω * Matrix.diagonal ![ω, ω, -ω, -ω]) := by
          rw [hM]
          simp only [Matrix.mul_assoc]
      _ = Yai ω * suMat g * (suMat (u0 K p f) * Ya ω) := by rw [suMat_u0_Ya h]
      _ = Yai ω * (suMat g * suMat (u0 K p f)) * Ya ω := by simp only [Matrix.mul_assoc]
      _ = Yai ω * (suMat (u0 K p f) * suMat g) * Ya ω := by rw [hGcomm]
      _ = (Yai ω * suMat (u0 K p f)) * suMat g * Ya ω := by simp only [Matrix.mul_assoc]
      _ = (Matrix.diagonal ![ω, ω, -ω, -ω] * Yai ω) * suMat g * Ya ω := by
          rw [Yai_suMat_u0 h]
      _ = Matrix.diagonal ![ω, ω, -ω, -ω] * M := by
          rw [hM]
          simp only [Matrix.mul_assoc]
  obtain ⟨A, B, hAB⟩ := eq_Lev_of_comm h.omega_ne_neg hMΔ
  have hMunit : conjTr σ₀ M * Gam * M = Gam :=
    unitary_conj_inv σ₀ h.h2 hYY (conjTr_Ya_mul _ h.hω h.hσω) (g.2.2)
  rw [hAB, conjTr_Lev, Matrix.mul_assoc, Gam_Lev, ← Matrix.mul_assoc, Lev_mul] at hMunit
  have hL1 : Lev (conjTr σ₀ A * B) (conjTr σ₀ B * A) = 1 := by
    calc Lev (conjTr σ₀ A * B) (conjTr σ₀ B * A)
        = Lev (conjTr σ₀ A * B) (conjTr σ₀ B * A) * Gam * Gam := by
          rw [Matrix.mul_assoc, Gam_mul_Gam, Matrix.mul_one]
      _ = Gam * Gam := by rw [hMunit]
      _ = 1 := Gam_mul_Gam
  obtain ⟨hAB1, hAB2⟩ := Lev_inj (hL1.trans Lev_one.symm)
  have hN : M * Lev (conjTr σ₀ B) (conjTr σ₀ A) = 1 := by
    rw [hAB, Lev_mul, mul_eq_one_comm.mp hAB2, mul_eq_one_comm.mp hAB1, Lev_one]
  have hM'M : M' * M = 1 := by
    calc M' * M = Yai ω * (suMat g⁻¹ * (Ya ω * Yai ω) * suMat g) * Ya ω := by
          rw [hM, hM']
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hYY, Matrix.mul_one, suMat_inv_mul_suMat, Matrix.mul_one, hYiY]
  have hM'N : M' = Lev (conjTr σ₀ B) (conjTr σ₀ A) := by
    calc M' = M' * (M * Lev (conjTr σ₀ B) (conjTr σ₀ A)) := by rw [hN, Matrix.mul_one]
      _ = (M' * M) * Lev (conjTr σ₀ B) (conjTr σ₀ A) := (Matrix.mul_assoc _ _ _).symm
      _ = Lev (conjTr σ₀ B) (conjTr σ₀ A) := by rw [hM'M, Matrix.one_mul]
  obtain ⟨B₂, hB₂⟩ := exists_conj_levS h.hσσ hAB2 B₁
  have hGM : suMat g = Ya ω * M * Yai ω := by
    rw [hM]
    calc suMat g = (Ya ω * Yai ω) * suMat g * (Ya ω * Yai ω) := by
          rw [hYY, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hGiM : suMat g⁻¹ = Ya ω * M' * Yai ω := by
    rw [hM']
    calc suMat g⁻¹ = (Ya ω * Yai ω) * suMat g⁻¹ * (Ya ω * Yai ω) := by
          rw [hYY, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨B₂, ?_⟩
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_iotaA, suMat_iotaA, hGM, hGiM, ← hB₂, hAB, hM'N]
  symm
  calc Ya ω * Lev A B * Yai ω * (Ya ω * levS σ₀ B₁ * Yai ω) *
        (Ya ω * Lev (conjTr σ₀ B) (conjTr σ₀ A) * Yai ω)
      = Ya ω * Lev A B * (Yai ω * Ya ω) * levS σ₀ B₁ * (Yai ω * Ya ω) *
        Lev (conjTr σ₀ B) (conjTr σ₀ A) * Yai ω := by simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hYiY]
        simp only [Matrix.mul_assoc, Matrix.mul_one]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem Gam_mul_Delta (ω : K) :
    (Gam : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![ω, ω, -ω, -ω] =
      -(Matrix.diagonal ![ω, ω, -ω, -ω] * Gam) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gam, Matrix.mul_diagonal, Matrix.diagonal_mul]

@[expose] noncomputable def c1A : Su K p f 4 :=
  mkSU K p f (Ya ω * Gam * Yai ω)
    (by rw [det_conj (Ya_mul_Yai h.h2 h.hω), det_Gam])
    (unitary_conj _ h.h2 (Ya_mul_Yai h.h2 h.hω) (conjTr_Ya_mul _ h.hω h.hσω)
      (by rw [conjTr_Gam, Gam_mul_Gam, Matrix.one_mul]))

theorem suMat_c1A : suMat (c1A h) = Ya ω * Gam * Yai ω := rfl

theorem c1A_mul_self : c1A h * c1A h = 1 := by
  apply suMat_injective
  rw [suMat_mul, suMat_c1A, suMat_one]
  calc Ya ω * Gam * Yai ω * (Ya ω * Gam * Yai ω)
      = Ya ω * (Gam * (Yai ω * Ya ω) * Gam) * Yai ω := by simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Yai_mul_Ya h.h2 h.hω, Matrix.mul_one, Gam_mul_Gam, Matrix.mul_one,
          Ya_mul_Yai h.h2 h.hω]

theorem c1A_mul_u0 : c1A h * u0 K p f = (zneg K p f * u0 K p f) * c1A h := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_mul, suMat_c1A, suMat_zneg]
  calc Ya ω * Gam * Yai ω * suMat (u0 K p f)
      = Ya ω * Gam * (Yai ω * suMat (u0 K p f)) := by rw [Matrix.mul_assoc]
    _ = Ya ω * (Gam * Matrix.diagonal ![ω, ω, -ω, -ω]) * Yai ω := by
        rw [Yai_suMat_u0 h]
        simp only [Matrix.mul_assoc]
    _ = -(Ya ω * Matrix.diagonal ![ω, ω, -ω, -ω] * Gam * Yai ω) := by
        rw [Gam_mul_Delta]
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(suMat (u0 K p f) * Ya ω * Gam * Yai ω) := by rw [suMat_u0_Ya h]
    _ = (-1 * suMat (u0 K p f)) * (Ya ω * Gam * Yai ω) := by
        simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc]

theorem conj_mem_c1A {q : Su K p f 4} (hq : q ∈ (iotaA h).range) :
    c1A h * q * (c1A h)⁻¹ ∈ (iotaA h).range := by
  obtain ⟨B, rfl⟩ := hq
  obtain ⟨B', hB'⟩ := exists_Gam_levS h.hσσ B
  refine ⟨B', ?_⟩
  have hinv : (c1A h)⁻¹ = c1A h := inv_eq_of_mul_eq_one_right (c1A_mul_self h)
  apply suMat_injective
  rw [hinv, suMat_mul, suMat_mul, suMat_iotaA, suMat_iotaA, suMat_c1A, ← hB']
  calc Ya ω * (Gam * levS σ₀ B * Gam) * Yai ω
      = Ya ω * Gam * (Yai ω * Ya ω) * levS σ₀ B * (Yai ω * Ya ω) * Gam * Yai ω := by
        rw [Yai_mul_Ya h.h2 h.hω]
        simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem AData.four_le (h : AData K p f ω) (hq : 5 ≤ p ^ f) : 4 ≤ Nat.card K := by
  rw [h.hK]
  nlinarith

theorem slayer_u0_A (hq : 5 ≤ p ^ f) : SLayer (u0 K p f) (iotaA h).range := by
  have hQS : CFSG.IsQuasisimple SL(2, K) := InnerL4.isQuasisimple_sl2 (h.four_le hq)
  have : Group.IsPerfect SL(2, K) := hQS.1
  have hperf : Group.IsPerfect (iotaA h).range := Group.IsPerfect.range (iotaA h)
  have hcc : c1A h * c1A h = 1 := c1A_mul_self h
  have hcc' : (c1A h)⁻¹ * (c1A h)⁻¹ = 1 := by rw [← _root_.mul_inv_rev, hcc, inv_one]
  have hz : ∀ y : Su K p f 4, y * zneg K p f = zneg K p f * y := fun y =>
    Subgroup.mem_center_iff.mp zneg_mem_center y
  refine ⟨fun q hq' => ?_, fun g hg q hq' => ?_,
    (Subgroup.commutator_eq_self (H := (iotaA h).range)).symm.le, ?_⟩
  · obtain ⟨B, rfl⟩ := hq'
    exact iotaA_comm_u0 h B
  · rcases conj_cases h.hK (u0 K p f) g (zneg K p f) u0_mul_self (Or.inr rfl) hg with e | e
    · exact conj_mem_of_comm h (mul_inv_eq_iff_eq_mul.mp e) hq'
    · set c := c1A h with hc
      have e1 : g * u0 K p f = zneg K p f * u0 K p f * g := mul_inv_eq_iff_eq_mul.mp e
      have hg' : (c * g) * u0 K p f = u0 K p f * (c * g) := by
        calc c * g * u0 K p f = c * (zneg K p f * u0 K p f * g) := by rw [mul_assoc, e1, mul_assoc]
          _ = (c * zneg K p f) * u0 K p f * g := by group
          _ = (zneg K p f * c) * u0 K p f * g := by rw [hz c]
          _ = zneg K p f * (c * u0 K p f) * g := by group
          _ = zneg K p f * (zneg K p f * u0 K p f * c) * g := by rw [c1A_mul_u0 h]
          _ = (zneg K p f * zneg K p f) * u0 K p f * (c * g) := by group
          _ = u0 K p f * (c * g) := by rw [zneg_mul_self, one_mul]
      have h1 := conj_mem_of_comm h hg' hq'
      have h2' := conj_mem_c1A h h1
      have eq : c * (c * g * q * (c * g)⁻¹) * c⁻¹ = g * q * g⁻¹ := by
        calc c * (c * g * q * (c * g)⁻¹) * c⁻¹ = (c * c) * g * q * g⁻¹ * (c⁻¹ * c⁻¹) := by group
          _ = g * q * g⁻¹ := by rw [hcc, hcc']; group
      rwa [eq] at h2'
  · refine ⟨{(iotaA h).range}, ?_, ?_⟩
    · intro H hH
      rw [Set.mem_singleton_iff] at hH
      subst hH
      refine ⟨le_rfl,
        isQuasisimple_of_equiv (MonoidHom.ofInjective (iotaA_injective h)) hQS, ?_⟩
      intro p' hp h' hh
      exact (iotaA h).range.mul_mem ((iotaA h).range.mul_mem hp hh)
        ((iotaA h).range.inv_mem hp)
    · exact le_iSup₂_of_le _ rfl le_rfl

theorem t0_mem_range_A : t0 K p f ∈ (iotaA h).range := by
  refine ⟨tSL h.hω, ?_⟩
  apply suMat_injective
  rw [suMat_iotaA, levS_tSL h.hω h.hσω]
  have e : suMat (t0 K p f) * Ya ω = Ya ω * Matrix.diagonal ![-ω, ω, ω, -ω] := by
    rw [t0, suMat_mul, suMat_x0, suMat_u0]
    exact T0_mul_Ya h.hω
  rw [← e, Matrix.mul_assoc, Ya_mul_Yai h.h2 h.hω, Matrix.mul_one]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem h0_up : ∀ s w : K, s ≠ 0 → w ≠ 0 → ∀ z : K,
    Matrix.diagonal ![s, w, s, w] *
        (!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -1, 1] : Matrix (Fin 4) (Fin 4) K) =
      z • ((!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -1, 1] : Matrix (Fin 4) (Fin 4) K) *
        Matrix.diagonal ![s, w, s, w]) → s = w := by
  intro s w hs hw z hz
  have e00 := congrFun (congrFun hz 0) 0
  have e01 := congrFun (congrFun hz 0) 1
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at e00 e01
  simp at e00 e01
  have hz1 : z = 1 := by
    have h1 : s * (1 - z) = 0 := by linear_combination e00
    have h3 := (mul_eq_zero.mp h1).resolve_left hs
    linear_combination -h3
  rw [hz1] at e01
  linear_combination e01

theorem iotaA_upSL_mul_Ya :
    suMat (iotaA h upSL) * Ya ω =
      Ya ω * (!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -1, 1] : Matrix (Fin 4) (Fin 4) K) := by
  rw [suMat_iotaA, Matrix.mul_assoc (Ya ω * levS σ₀ upSL), Yai_mul_Ya h.h2 h.hω, Matrix.mul_one,
    levS_upSL]

theorem exists_layer_u0_of_pos (h : AData K p f ω) (hq : 5 ≤ p ^ f) :
    ∃ Q : Subgroup (Su K p f 4), SLayer (u0 K p f) Q ∧ t0 K p f ∈ Q ∧
      ∃ m ∈ Q, MixProp (suMat m) := by
  refine ⟨(iotaA h).range, slayer_u0_A h hq, t0_mem_range_A h, iotaA h upSL, ⟨upSL, rfl⟩, ?_⟩
  exact mixProp_of_conj (Yai_mul_Ya h.h2 h.hω) (fun s w => diag4_mul_Ya s w)
    (iotaA_upSL_mul_Ya h) h0_up

end GroupA

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
