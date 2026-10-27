module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryDelta
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem deltaCentral_unitary {n m : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ m) ^ 2) (hU : UnitaryFieldData 2 m K)
    {e : rankTwoQuot A ≃* StatedProj (StatedSU n (2 ^ m) K)} (hZ : Odd (Nat.card (center ↥A)))
    (hsep : QuadSep hU.bar) {p : G} {ℓ0 : ℕ} (hp : IsInvolutionOfRank e p ℓ0) :
    DeltaCentral A p (alphaGroup e p) := by
  have : CharP K 2 := hU.charP
  have : Finite K := hU.finite
  obtain ⟨hp2, M, hpM, hM2, -⟩ := hp
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  set σ := hU.bar with hσdef
  have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
  have hσq : ∀ x, σ x = x ^ 2 ^ m := hU.bar_apply
  have htr : ∀ c, σ c = c → ∃ d, d + σ d = c := by
    intro c hc
    obtain ⟨d, hd⟩ := hU.traceLin_surjective ⟨c, (hU.mem_fixedField).mpr hc⟩
    exact ⟨d, congrArg Subtype.val hd⟩
  have hMu := adjM_mul_self_of_mem_statedSU hσ hσq hpM.2.1
  have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
    rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
  have hMadj : adjM σ (M : Matrix (Fin n) (Fin n) K) = M := by
    calc adjM σ (M : Matrix (Fin n) (Fin n) K) =
        adjM σ (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
      _ = M := by rw [← mul_assoc, hMu, one_mul]
  have hNh : adjM σ ((M : Matrix (Fin n) (Fin n) K) - 1) =
      (M : Matrix (Fin n) (Fin n) K) - 1 := by
    rw [adjM_sub, hMadj, adjM_one]
  have hN := sub_one_mul_self_eq_zero hM2
  have hM1 : M ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hM2
    omega
  have hN0 := sub_one_ne_zero hM1
  obtain ⟨z, hz, hz1⟩ := exists_norm_one_ne_one hK
  have hz' : σ z * z = 1 := by rw [hσq]; exact hz
  obtain ⟨θ, hθ⟩ := hU.exists_bar_ne
  obtain ⟨ℓ, r, φ, hℓ0, hn', hφN, -, hunit⟩ := exists_unitary_adapted hU hN hNh hN0
  have hφM : φ (M : Matrix (Fin n) (Fin n) K) = 1 + sqZeroStd ℓ r := by
    rw [show (M : Matrix (Fin n) (Fin n) K) = 1 + ((M : Matrix (Fin n) (Fin n) K) - 1) from
      (add_sub_cancel 1 _).symm, map_add, map_one, hφN]
  show DeltaCentral A p (alphaGroup e p)
  refine deltaCentral_alpha_of hZ hp2' hpM hM2 fun X hX hXM hXg => ?_
  have hBS : Commute (φ (X : Matrix (Fin n) (Fin n) K)) (sqZeroStd ℓ r) := by
    have h1 : (X : Matrix (Fin n) (Fin n) K) * M = M * X := by
      rw [← Units.val_mul, hXM, Units.val_mul]
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, hφM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h2
    exact add_left_cancel h2
  have hC : ∀ P : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K, P * P = 0 →
      adjM σ P * unitGram K ℓ r = unitGram K ℓ r * P →
      Commute (P * sqZeroStd ℓ r + sqZeroStd ℓ r * P + P * sqZeroStd ℓ r * P)
        (sqZeroStd ℓ r) →
      Commute (φ (X : Matrix (Fin n) (Fin n) K))
        (P * sqZeroStd ℓ r + sqZeroStd ℓ r * P + P * sqZeroStd ℓ r * P) := by
    intro P hP2 hPJ hCS
    have hE : φ.symm P * φ.symm P = 0 := by rw [← map_mul, hP2, map_zero]
    set g := unipGL (φ.symm P) hE 1 with hg
    have hgv : (g : Matrix (Fin n) (Fin n) K) = φ.symm (1 + P) := by
      rw [hg, coe_unipGL, one_smul, map_add, map_one]
    have hgφ : φ (g : Matrix (Fin n) (Fin n) K) = 1 + P := by
      rw [hgv, AlgEquiv.apply_symm_apply]
    have hgSU : g ∈ StatedSU n (2 ^ m) K := mem_statedSU_of hσq (det_unipGL hE 1) (by
      rw [hgv]
      exact hunit (1 + P) (adjM_one_add_mul_unitGram hPJ hP2))
    have hginv : g⁻¹ = g := by
      have h1 := unipGL_sq hE (1 : K)
      rw [sq] at h1
      exact inv_eq_of_mul_eq_one_right h1
    generalize hCdef : P * sqZeroStd ℓ r + sqZeroStd ℓ r * P + P * sqZeroStd ℓ r * P = C
      at hCS ⊢
    have hconj : φ ((g * M * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (1 + sqZeroStd ℓ r) + C := by
      rw [hginv, Units.val_mul, Units.val_mul, map_mul, map_mul, hgφ, hφM, ← hCdef]
      exact one_add_mul_one_add_mul_one_add hP2
    have hcomm : g * M * g⁻¹ * M = M * (g * M * g⁻¹) := by
      apply Units.ext
      apply φ.injective
      rw [Units.val_mul (g * M * g⁻¹) M, Units.val_mul M (g * M * g⁻¹), map_mul, map_mul,
        hconj, hφM]
      have hCS' : C * sqZeroStd ℓ r = sqZeroStd ℓ r * C := hCS
      calc (1 + sqZeroStd ℓ r + C) * (1 + sqZeroStd ℓ r) =
          (1 + sqZeroStd ℓ r) * (1 + sqZeroStd ℓ r) + (C + C * sqZeroStd ℓ r) := by
            noncomm_ring
        _ = (1 + sqZeroStd ℓ r) * (1 + sqZeroStd ℓ r) + (C + sqZeroStd ℓ r * C) := by
            rw [hCS']
        _ = (1 + sqZeroStd ℓ r) * (1 + sqZeroStd ℓ r + C) := by noncomm_ring
    have hXc := hXg g hgSU hcomm
    have h3 : φ (X : Matrix (Fin n) (Fin n) K) * ((1 + sqZeroStd ℓ r) + C) =
        ((1 + sqZeroStd ℓ r) + C) * φ (X : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun Y : GL (Fin n) K => φ (Y : Matrix (Fin n) (Fin n) K)) hXc
      rwa [Units.val_mul X (g * M * g⁻¹), Units.val_mul (g * M * g⁻¹) X, map_mul, map_mul,
        hconj] at h
    have h4 : φ (X : Matrix (Fin n) (Fin n) K) * (1 + sqZeroStd ℓ r) =
        (1 + sqZeroStd ℓ r) * φ (X : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hBS.eq]
    rw [Matrix.mul_add, Matrix.add_mul, h4] at h3
    exact add_left_cancel h3
  obtain ⟨c, d, hcd⟩ := eq_of_commute_unitary_conj hσ hℓ0 (by omega) hBS hC hz' hz1 hsep hθ
    htr
  set N := (M : Matrix (Fin n) (Fin n) K) - 1 with hNdef
  have hXcd : (X : Matrix (Fin n) (Fin n) K) = c • 1 + d • N := by
    apply φ.injective
    rw [hcd, map_add, map_smul, map_smul, map_one, hφN]
  have hXu := adjM_mul_self_of_mem_statedSU hσ hσq hX
  rw [hXcd, adjM_add, adjM_smul, adjM_smul, adjM_one, hNh] at hXu
  have hexp : (σ c • (1 : Matrix (Fin n) (Fin n) K) + σ d • N) * (c • 1 + d • N) =
      (σ c * c) • 1 + (σ c * d + σ d * c) • N := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hN, smul_zero, add_zero, smul_smul]
    module
  rw [hexp] at hXu
  have hcc : σ c * c = 1 := by
    have h1 := congrArg (fun Y => Y * N) hXu
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hN, smul_zero,
      add_zero] at h1
    have h2 : (σ c * c - 1) • N = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hN0
  have hcd' : σ c * d + σ d * c = 0 := by
    rw [hcc, one_smul] at hXu
    rcases smul_eq_zero.mp (add_eq_left.mp hXu) with h | h
    · exact h
    · exact absurd h hN0
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcc
    exact zero_ne_one hcc
  have hσc0 : σ c ≠ 0 := (map_ne_zero σ).mpr hc0
  have haσ : σ (d / c) = d / c := by
    rw [map_div₀, div_eq_div_iff hσc0 hc0]
    have h1 : σ d * c = σ c * d := by
      rw [← CharTwo.neg_eq (σ c * d)]
      exact eq_neg_of_add_eq_zero_right hcd'
    rw [h1, mul_comm]
  have hYSU : unipGL N hN (d / c) ∈ StatedSU n (2 ^ m) K := by
    refine mem_statedSU_of hσq (det_unipGL hN _) ?_
    have h1 : adjM σ (unipGL N hN (d / c) : Matrix (Fin n) (Fin n) K) =
        unipGL N hN (d / c) := by
      rw [coe_unipGL, adjM_add, adjM_one, adjM_smul, haσ, hNh]
    rw [h1, ← Units.val_mul, ← sq, unipGL_sq, Units.val_one]
  refine ⟨unipGL N hN (d / c), hYSU, ⟨Units.mk0 c hc0, Units.ext ?_⟩, d / c,
    by rw [coe_unipGL, add_sub_cancel_left]⟩
  rw [hXcd, Units.val_mul, coe_unipGL, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, add_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
  have hcd'' : c * (d / c) = d := by field_simp
  rw [hcd'']

theorem deltaAlpha_unitary : DeltaAlpha .unitary := by
  intro G _ _ A D hD _ hZ hq p hp
  cases D with
  | unitary n m hn hm K hK e =>
    have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨ℓ0, hpℓ⟩ := hp
    obtain ⟨μ, hμσ, hμ0, hμ1⟩ : ∃ μ : K, hU.bar μ = μ ∧ μ ≠ 0 ∧ μ ≠ 1 := by
      have : Finite K := hU.finite
      have h4 : 4 ≤ 2 ^ m := hq
      obtain ⟨μ₀, h0, h1⟩ := exists_scalar_ne_zero_ne_one (K := hU.fixedField)
        (by rw [hU.card_fixedField]; omega)
      refine ⟨μ₀, (hU.mem_fixedField).mp μ₀.2, fun h => h0 ?_, fun h => h1 ?_⟩
      · exact Subtype.ext h
      · exact Subtype.ext h
    exact deltaCentral_unitary hn hK hU hZ (quadSep_of_fixed hμσ hμ0 hμ1) hpℓ
  | linear => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
