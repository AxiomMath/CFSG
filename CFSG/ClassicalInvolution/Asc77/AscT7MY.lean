module

public import CFSG.ClassicalInvolution.Asc77.AscT7MX
public import CFSG.ClassicalInvolution.Asc77.AscT7MW

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem dMat_one_eq : (dMat 1 : Matrix (Fin 4) (Fin 4) K) =
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [dMat, sgn]

theorem conjTr_cols (σ : K ≃+* K) {i w c : K} (hi : i * i = -1) (hσi : σ i = -i)
    (hw : 2 * (σ w * w) = 1) (hc : 2 * (σ c * c) = 1) :
    conjTr σ !![w, c; -(i * w), i * c] * !![w, c; -(i * w), i * c] = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, map_mul, hσi]
  · linear_combination hw - (σ w * w) * hi
  · linear_combination (σ w * c) * hi
  · linear_combination (σ c * w) * hi
  · linear_combination hc - (σ c * c) * hi

theorem exists_su2_cols {i w c : K} (hi : i * i = -1)
    (hσi : unitaryInvolution K p f i = -i) (hw : 2 * (unitaryInvolution K p f w * w) = 1)
    (hc : 2 * (unitaryInvolution K p f c * c) = 1) (hdet : 2 * i * w * c = 1) :
    ∃ A : Su K p f 2, suMat A = !![w, c; -(i * w), i * c] := by
  refine ⟨mkSU K p f !![w, c; -(i * w), i * c] ?_ (conjTr_cols _ hi hσi hw hc), suMat_mkSU _ _⟩
  rw [Matrix.det_fin_two_of]
  linear_combination hdet

theorem exists_su2_diag (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) {a b : K}
    (hb : b ≠ 0) (na : unitaryInvolution K p f a * a = 1)
    (nb : unitaryInvolution K p f b * b = 1) (hab : a * a = -(b * b)) :
    ∃ A : Su K p f 2,
      suMat (blockEmb K p f 4 2 0 (by norm_num) (jSU K p f)) *
        (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] : Matrix (Fin 4) (Fin 4) K) *
        suMat (blockEmb K p f 4 2 0 (by norm_num) A) =
      suMat (blockEmb K p f 4 2 0 (by norm_num) A) * (b • (dMat 1 : Matrix (Fin 4) (Fin 4) K)) := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hσb : unitaryInvolution K p f b ≠ 0 := left_ne_zero_of_mul_eq_one nb
  obtain ⟨i, hi, hni, hai⟩ : ∃ i : K, i * i = -1 ∧ unitaryInvolution K p f i * i = 1 ∧
      a = i * b := by
    refine ⟨a * b⁻¹, ?_, ?_, by field_simp⟩
    · field_simp
      linear_combination hab
    · rw [map_mul, map_inv₀]
      have ha : unitaryInvolution K p f a ≠ 0 := left_ne_zero_of_mul_eq_one na
      calc unitaryInvolution K p f a * (unitaryInvolution K p f b)⁻¹ * (a * b⁻¹)
          = (unitaryInvolution K p f a * a) * (unitaryInvolution K p f b * b)⁻¹ := by
            field_simp
        _ = 1 := by rw [na, nb]; simp
  subst hai
  set σ := unitaryInvolution K p f with hσdef
  have hσi : σ i = -i := by linear_combination (-i) * hni + (σ i) * hi
  obtain ⟨c, hcn⟩ := hσ.exists_norm (d := (2 : K)⁻¹) (by rw [map_inv₀, map_ofNat])
  have hc : 2 * (σ c * c) = 1 := by rw [hcn]; field_simp
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hσc0 : σ c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hσi0 : σ i ≠ 0 := by
    intro h
    rw [h] at hni
    simp at hni
  set w : K := (2 * i * c)⁻¹ with hwdef
  have hdet : 2 * i * w * c = 1 := by
    rw [hwdef]
    field_simp
  have hσw : σ w = (2 * (-i) * σ c)⁻¹ := by
    rw [hwdef, map_inv₀, map_mul, map_mul, map_ofNat, hσi]
  have hw : 2 * (σ w * w) = 1 := by
    rw [hσw, hwdef]
    field_simp
    linear_combination hc - 2 * (σ c * c) * hi
  obtain ⟨A, hA⟩ := exists_su2_cols hi hσi hw hc hdet
  refine ⟨A, ?_⟩
  rw [suMat_blockEmb_zero, suMat_blockEmb_zero, hA, suMat_jSU, dMat_one_eq]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | ring1 | linear_combination (-(b * w)) * hi | linear_combination (b * c) * hi

theorem actsAsM_conj_inv (g : Su K p f 4) :
    ActsAsM (MulAut.conj (QuotientGroup.mk g : PU K p f))⁻¹ (suMat g⁻¹) (suMat g) := by
  have h := actsAsM_conj g⁻¹
  rwa [inv_inv, QuotientGroup.mk_inv, map_inv] at h

theorem ActsAsM.actsAsD_of_smul {φ : MulAut (PU K p f)} {M Mi : Matrix (Fin 4) (Fin 4) K} {b : K}
    {j : Fin 4} (hφ : ActsAsM φ M Mi) (hb : b ≠ 0) (hM : M = b • dMat j) :
    ActsAsD K p f φ j := by
  rw [actsAsD_iff]
  obtain ⟨h1, h2, h3⟩ := hφ
  have hMi : Mi = b⁻¹ • (dMat j : Matrix (Fin 4) (Fin 4) K) := by
    have e : M * (b⁻¹ • (dMat j : Matrix (Fin 4) (Fin 4) K)) = 1 := by
      rw [hM, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hb, one_smul,
        dMat_mul_self]
    calc Mi = Mi * (M * (b⁻¹ • (dMat j : Matrix (Fin 4) (Fin 4) K))) := by
          rw [e, Matrix.mul_one]
      _ = (Mi * M) * (b⁻¹ • (dMat j : Matrix (Fin 4) (Fin 4) K)) := by rw [Matrix.mul_assoc]
      _ = b⁻¹ • (dMat j : Matrix (Fin 4) (Fin 4) K) := by rw [h2, Matrix.one_mul]
  refine ⟨dMat_mul_self j, dMat_mul_self j, fun h => ?_⟩
  obtain ⟨h', hh', hm⟩ := h3 h
  refine ⟨h', hh', ?_⟩
  rw [hm, hM, hMi]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem sU_conj_d1 :
    suMat (sU K p f) * dMat 1 * suMat (sU K p f)⁻¹ = (dMat 3 : Matrix (Fin 4) (Fin 4) K) := by
  rw [suMat_sU, suMat_sU_inv, dMat_one_eq, dMat_three_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem exists_Gamma_U (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4)) {k : Su K p f 4} (hkR : k ∈ R)
    (hkk : (QuotientGroup.mk k : PU K p f) * QuotientGroup.mk k = QuotientGroup.mk x)
    {φ : MulAut (PU K p f)} (hφ : ∀ r ∈ R, φ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hφ' : ∀ r ∈ R', φ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hφ2 : φ * φ = MulAut.conj (QuotientGroup.mk x : PU K p f)) :
    ∃ Γ : Su K p f 4,
      ActsAsD K p f ((MulAut.conj (QuotientGroup.mk Γ : PU K p f))⁻¹ *
        (MulAut.conj (QuotientGroup.mk k : PU K p f) * φ) *
        MulAut.conj (QuotientGroup.mk Γ : PU K p f)) 3 ∧
      (QuotientGroup.mk x : PU K p f) =
        MulAut.conj (QuotientGroup.mk Γ : PU K p f) (QuotientGroup.mk (zA K p f)) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨g, hRg, hR'g, hxg, hkg⟩ :=
    twin_std_ku hK hp hq hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc hkR hkk
  set c : MulAut (PU K p f) := MulAut.conj (QuotientGroup.mk g) with hcdef
  have hcp : ∀ s : Su K p f 4, c (QuotientGroup.mk s) = QuotientGroup.mk (g * s * g⁻¹) :=
    fun s => by
      rw [hcdef, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
  set α : MulAut (PU K p f) := c⁻¹ * φ * c with hα
  have hfixα : ∀ (S S0 : Subgroup (Su K p f 4)), S = S0.map (MulAut.conj g).toMonoidHom →
      (∀ r ∈ S, φ (QuotientGroup.mk r) = QuotientGroup.mk r) →
      ∀ r ∈ S0, α (QuotientGroup.mk r) = QuotientGroup.mk r := by
    intro S S0 hS hSfix r hr
    have hmem : g * r * g⁻¹ ∈ S := by
      rw [hS]
      exact ⟨r, hr, rfl⟩
    show (c⁻¹) (φ (c (QuotientGroup.mk r))) = QuotientGroup.mk r
    rw [hcp, hSfix _ hmem, ← hcp]
    simp
  have hfix0 := hfixα R (InnerSu.R0 K p f) hRg hφ
  have hfix2 := hfixα R' (InnerSu.R0' K p f) hR'g hφ'
  have hα2 : α * α = MulAut.conj (QuotientGroup.mk (rootInvSU K p f (show 2 ≤ 4 by norm_num)) :
      PU K p f) := by
    have h1 : α * α = c⁻¹ * (φ * φ) * c := by rw [hα]; group
    have hconj : MulAut.conj (QuotientGroup.mk (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) *
        g⁻¹) : PU K p f) = c * MulAut.conj (QuotientGroup.mk (rootInvSU K p f
          (show 2 ≤ 4 by norm_num)) : PU K p f) * c⁻¹ := by
      rw [hcdef]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    rw [h1, hφ2, hxg, hconj]
    group
  obtain ⟨a, b, ha, hb, na, nb, hab, hαM⟩ :=
    su4_sq_blocks hK hp hq α (fun A => hfix0 _ ⟨A, rfl⟩) (fun A => hfix2 _ ⟨A, rfl⟩) hα2
  obtain ⟨A, hA⟩ := exists_su2_diag hK h2 hb na nb hab
  set U : Su K p f 4 := blockEmb K p f 4 2 0 (by norm_num) A with hU
  set k0 : Su K p f 4 := blockEmb K p f 4 2 0 (by norm_num) (jSU K p f) with hk0
  refine ⟨g * U * (sU K p f)⁻¹, ?_, ?_⟩
  ·
    have hψ₁ := (actsAsM_conj k0).mul hαM
    have hψ₂ := ((actsAsM_conj_inv U).mul hψ₁).mul (actsAsM_conj U)
    have hM₂ : suMat U⁻¹ * (suMat k0 * !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) *
        suMat U = b • (dMat 1 : Matrix (Fin 4) (Fin 4) K) := by
      have hA' : suMat k0 * (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] :
          Matrix (Fin 4) (Fin 4) K) * suMat U =
          suMat U * (b • (dMat 1 : Matrix (Fin 4) (Fin 4) K)) :=
        hA
      rw [Matrix.mul_assoc, hA', ← Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.one_mul]
    rw [hM₂] at hψ₂
    have hψ₃ := ((actsAsM_sU.mul hψ₂).mul actsAsM_sU_inv)
    have hM₃ : suMat (sU K p f) * (b • (dMat 1 : Matrix (Fin 4) (Fin 4) K)) *
        suMat (sU K p f)⁻¹ = b • (dMat 3 : Matrix (Fin 4) (Fin 4) K) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, sU_conj_d1]
    rw [hM₃] at hψ₃
    have hD := hψ₃.actsAsD_of_smul hb rfl
    have heq : (MulAut.conj (QuotientGroup.mk (g * U * (sU K p f)⁻¹) : PU K p f))⁻¹ *
        (MulAut.conj (QuotientGroup.mk k : PU K p f) * φ) *
        MulAut.conj (QuotientGroup.mk (g * U * (sU K p f)⁻¹) : PU K p f) =
        MulAut.conj (QuotientGroup.mk (sU K p f) : PU K p f) *
          ((MulAut.conj (QuotientGroup.mk U : PU K p f))⁻¹ *
            (MulAut.conj (QuotientGroup.mk k0 : PU K p f) * α) *
              MulAut.conj (QuotientGroup.mk U : PU K p f)) *
          (MulAut.conj (QuotientGroup.mk (sU K p f) : PU K p f))⁻¹ := by
      have hkc : MulAut.conj (QuotientGroup.mk k : PU K p f) =
          c * MulAut.conj (QuotientGroup.mk k0 : PU K p f) * c⁻¹ := by
        rw [hkg, hcdef]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
      have hφc : φ = c * α * c⁻¹ := by rw [hα]; group
      rw [hkc, hφc, hcdef]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
      group
    rw [heq]
    exact hD
  · have hUx : U * InnerSu.x0 K p f = InnerSu.x0 K p f * U := blockEmb_zero_comm_x0 A
    have hΓ : g * U * (sU K p f)⁻¹ * zA K p f * (g * U * (sU K p f)⁻¹)⁻¹ = x := by
      have hzA : zA K p f = sU K p f * InnerSu.x0 K p f * (sU K p f)⁻¹ := rfl
      rw [hxg, hzA]
      calc g * U * (sU K p f)⁻¹ * (sU K p f * InnerSu.x0 K p f * (sU K p f)⁻¹) *
            (g * U * (sU K p f)⁻¹)⁻¹ = g * (U * InnerSu.x0 K p f) * U⁻¹ * g⁻¹ := by group
        _ = g * (InnerSu.x0 K p f * U) * U⁻¹ * g⁻¹ := by rw [hUx]
        _ = g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹ := by
          show g * (InnerSu.x0 K p f * U) * U⁻¹ * g⁻¹ = g * InnerSu.x0 K p f * g⁻¹
          group
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      hΓ]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
