module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5Graph
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowConj

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_comm_conj_of_cols' (h : UnitaryFieldData p f K) {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε) {c : K} (hc : c ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (v : κ → HypIndex r ε → K) {b : K}
    (hv : ∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (v i a)) =
      b⁻¹ • v i)
    {Gi : Matrix κ κ K}
    (hGi : Gi * (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v) = 1)
    (hGi' : (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v) * Gi = 1)
    (hGbar : (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v).map h.bar =
      c • (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v))
    {H : Type*} [Group H] (Y : H →* Matrix κ κ K) (hYbar : ∀ x, (Y x).map h.bar = Y x)
    (hY : ∀ x, ((Y x).map h.bar)ᵀ * (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v) * Y x =
      ((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v)
    (hYd : ∀ x, (Y x).det = 1) :
    ∃ ψ : H →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ (x : H) (c' : K), ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = c' • 1 →
        Y x = c' • 1 := by
  set E := colMat v with hE
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h hGi hGi' Y hY hYd
  have hFE : Gi * (E.map h.bar)ᵀ * hypGram r ε K * E = 1 := by
    rw [← hGi]
    simp only [Matrix.mul_assoc]
  have hAE : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * E.map h.bar =
      E * (b⁻¹ • (1 : Matrix κ κ K)) := by
    rw [hE, map_colMat, mul_colMat, colMat_mul_smul_one]
    congr 1
    funext i
    exact hv i
  have hD : (b⁻¹ • (1 : Matrix κ κ K))ᵀ * ((E.map h.bar)ᵀ * hypGram r ε K * E).map h.bar =
      c • (((E.map h.bar)ᵀ * hypGram r ε K * E) * (b⁻¹ • (1 : Matrix κ κ K))) := by
    rw [hGbar, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_comm]
  have hFA := suppF_mul_of_semilinear h.bar_bar hc (hypGram_map h.bar) (mem_hypUnitary.mp hA)
    hAA hAE hD hGi hGi'
  refine ⟨ψ, fun x => ?_, fun x c' hc' => ?_⟩
  · rw [hψ x, suppMat_map h.bar]
    refine mul_suppMat hAE hFA ?_
    rw [hYbar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · rw [hψ] at hc'
    exact eq_smul_one_of_suppMat hFE hc'

theorem signDiag_bar (h : UnitaryFieldData p f K) (x : Fin 4 → ↥(signGroup K)) (i : Fin 5) :
    h.bar (signDiag x i) = signDiag x i := by
  have h1 := signDiag_sq x i
  rcases mul_self_eq_one_iff.mp h1 with h2 | h2 <;> rw [h2]
  · exact map_one _
  · rw [map_neg, map_one]

theorem exists_signs_comm_of_bar (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hn : 2 * r + ε = 5)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K} (hc : c ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) :
    ∃ ψ : (Fin 4 → ↥(signGroup K)) →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ x, hypProj h r ε (ψ x) = 1 → x = 1 := by
  have := h.finite
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have hn1 : 1 ≤ finrank K (HypIndex r ε → K) := by
    rw [finrank_hypIndex_fun]
    omega
  have hμ : ∀ v, conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) v) =
        ((Units.mk0 c hc : Kˣ) : K) • v := conjOp_conjOp hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hn1 (hypForm_isSymm h) (hypForm_separatingLeft h) _ (conjOp_bijective hc hAA)
    (hypForm_conjOp hA) (Units.mk0 c hc) hμ
  obtain ⟨-, hfin, -, hsym, halt⟩ := hall b t hb ht
  rw [finrank_hypIndex_fun] at hfin
  have hfix : ∀ w ∈ conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)),
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (w a)) =
        ((b : K))⁻¹ • w := fun w hw => by
    have h1 : (b : K) • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        fun a => h.bar (w a)) = w := mem_conjFixed.mp hw
    rw [← h1, smul_smul, inv_mul_cancel₀ b.ne_zero, one_smul, h1]
  rcases hμ1 with hμ1 | hμ1
  · have hc1 : c = 1 := by
      have := congrArg Units.val hμ1
      simpa using this
    subst hc1
    obtain ⟨B, hBH, hBs, hBnd, -⟩ := hsym hμ1
    have h2k : (2 : h.fixedField) ≠ 0 := fun h0 => two_ne_zero_of_odd h hp (by
      rw [← map_ofNat h.fixedField.subtype 2, h0, map_zero])
    have : Invertible (2 : h.fixedField) := invertibleOfNonzero h2k
    obtain ⟨vb, hvb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
      ⟨fun x y => hBs.eq x y⟩
    have hbo : B.iIsOrtho vb := hvb
    have hd0 := hbo.not_isOrtho_basis_self_of_nondegenerate hBnd
    have h5 : finrank h.fixedField
        (conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) = 5 := by
      rw [hfin]
      exact hn
    set w : Fin 5 → HypIndex r ε → K := fun i => (vb (Fin.cast h5.symm i) : HypIndex r ε → K)
      with hw
    set d : Fin 5 → h.fixedField := fun i => B (vb (Fin.cast h5.symm i)) (vb (Fin.cast h5.symm i))
      with hd
    have hww : ∀ i j, hypForm h r ε (w i) (w j) = if i = j then (d i : K) else 0 := by
      intro i j
      rw [← hBH]
      by_cases hij : i = j
      · subst hij
        simp [hd]
      · rw [hvb (fun h0 => hij (by simpa using h0))]
        simp [hij]
    have hd0' : ∀ i, (d i : K) ≠ 0 := fun i h0 =>
      hd0 (Fin.cast h5.symm i) (Subtype.ext h0)
    have hG : ((colMat w).map h.bar)ᵀ * hypGram r ε K * colMat w = diagonal fun i => (d i : K) := by
      rw [gram_colMat_eq_hypForm]
      ext i j
      rw [of_apply, diagonal_apply, hww]
    let Y : (Fin 4 → ↥(signGroup K)) →* Matrix (Fin 5) (Fin 5) K :=
      (Units.coeHom (Matrix (Fin 5) (Fin 5) K)).comp signGL
    have hYd : ∀ x, (Y x).det = 1 := fun x => det_signGL x
    have hYbar : ∀ x, (Y x).map h.bar = Y x := fun x => by
      show (diagonal (signDiag x)).map h.bar = diagonal (signDiag x)
      rw [diagonal_map (map_zero _)]
      congr 1
      funext i
      exact signDiag_bar h x i
    obtain ⟨ψ, hψc, hψs⟩ := exists_comm_conj_of_cols' h hA one_ne_zero hAA w
      (fun i => hfix _ (vb _).2) (Gi := diagonal fun i => (d i : K)⁻¹) (by
        rw [hG, diagonal_mul_diagonal]
        simp [inv_mul_cancel₀ (hd0' _)]) (by
        rw [hG, diagonal_mul_diagonal]
        simp [mul_inv_cancel₀ (hd0' _)]) (by
        rw [hG, one_smul, diagonal_map (map_zero _)]
        simp [h.mem_fixedField.mp (d _).2]) Y hYbar (by
        intro x
        rw [hG, hYbar x]
        show ((diagonal (signDiag x))ᵀ) * diagonal (fun i => (d i : K)) * diagonal (signDiag x) = _
        rw [diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        calc signDiag x i * (d i : K) * signDiag x i = (signDiag x i * signDiag x i) * (d i : K) := by
              ring
          _ = (d i : K) := by rw [signDiag_sq, one_mul]) hYd
    refine ⟨ψ, hψc, fun x hx => ?_⟩
    rw [← MonoidHom.mem_ker, ker_hypProj] at hx
    obtain ⟨c', hc'⟩ := exists_eq_smul_one_of_mem_hypScalars hx
    have hY1 := hψs x c' hc'
    exact eq_one_of_signGL_scalar (by
      show (Y x) = _
      rw [hY1, smul_one_eq_diagonal]
      rfl)
  · exfalso
    obtain ⟨-, -, -, -, heven, -⟩ := halt hμ1
    rw [finrank_hypIndex_fun, hn] at heven
    exact absurd heven (by decide)

theorem two_le_card_signGroup [Finite K] (hK : ringChar K ≠ 2) : 2 ≤ Nat.card ↥(signGroup K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have h1 : (1 : Kˣ) ≠ -1 := by
    intro h
    have := congrArg Units.val h
    simp only [Units.val_one, Units.val_neg] at this
    have h2' : (2 : K) = 0 := by linear_combination this
    exact h2 h2'
  have : 1 < Nat.card ↥(signGroup K) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    refine ⟨⟨⟨1, (signGroup K).one_mem⟩, ⟨-1, mem_signGroup.2 (by simp)⟩, fun h => h1 ?_⟩⟩
    exact congrArg Subtype.val h
  omega

theorem elemAbelian_range_of_signs [Finite K] (hK : ringChar K ≠ 2) {G : Type*} [Group G]
    (θ : (Fin 4 → ↥(signGroup K)) →* G) (hinj : Function.Injective θ) :
    (∀ e ∈ θ.range, ∀ e' ∈ θ.range, e * e' = e' * e) ∧ (∀ e ∈ θ.range, e * e = 1) ∧
      2 ^ 4 ≤ Nat.card ↥θ.range := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := by
      funext i
      have := mem_signGroup.1 (x i).2
      exact Subtype.ext (by simpa using this)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left (two_le_card_signGroup hK) 4

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
