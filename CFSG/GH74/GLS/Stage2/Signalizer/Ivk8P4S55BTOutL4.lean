module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOutL
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Matrix Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace OutL4

variable {K : Type} [Field K] {n : ℕ}

theorem conjAut_mem_range_of_det (A : GL (Fin n) K) (μ : Kˣ)
    (h : GeneralLinearGroup.det A = μ ^ n) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have hs : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) μ) = μ ^ n := by
    ext
    simp [GeneralLinearGroup.scalar]
  set B := (GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * A with hB
  have hdetB : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, map_inv, hs, h, inv_mul_cancel]
  have hBmem : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) hdetB
    simpa using this
  let g' : SpecialLinearGroup (Fin n) K := ⟨(B : Matrix (Fin n) (Fin n) K), hBmem⟩
  refine ⟨proj n K g', ?_⟩
  rw [← conjAut_toGL]
  have hAB : A = GeneralLinearGroup.scalar (Fin n) μ * B := by rw [hB]; group
  have hg' : SpecialLinearGroup.toGL g' = B := by
    ext1
    rfl
  rw [hg']
  conv_rhs => rw [hAB, map_mul, conjAut_scalar, one_mul]

theorem det_map (σ : K ≃+* K) (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) B) =
      Units.map (σ : K →* K) (GeneralLinearGroup.det B) := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply]
  change Matrix.det ((σ : K →+* K).mapMatrix (B : Matrix (Fin n) (Fin n) K)) = _
  rw [← RingHom.map_det]
  rfl

theorem det_inverseTranspose (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

variable [Finite K]

theorem exists_odd_zpow (h2 : (2 : K) ≠ 0) (σ : K ≃+* K) :
    ∃ m : ℤ, Odd m ∧ ∀ x : Kˣ, Units.map (σ : K →* K) x = x ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (Units.map (σ : K →* K))
  refine ⟨m, ?_, hm⟩
  by_contra hev
  rw [Int.not_odd_iff_even] at hev
  obtain ⟨t, rfl⟩ := hev
  have h1 := hm (-1)
  have hneg : Units.map (σ : K →* K) (-1) = -1 := Units.ext (by simp)
  rw [hneg, show t + t = 2 * t by ring, _root_.zpow_mul, show ((-1 : Kˣ) ^ (2 : ℤ)) = 1 by simp,
    _root_.one_zpow] at h1
  have h3 := congrArg (fun x : Kˣ => (x : K)) h1
  simp only [Units.val_neg, Units.val_one] at h3
  exact h2 (by linear_combination -h3)

theorem exists_det_zpow (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) (α : MulAut (projectiveSL n K)) :
    ∃ j : ℤ, Odd j ∧ ∀ B : GL (Fin n) K, ∃ B' : GL (Fin n) K,
      α * conjAut n K B * α⁻¹ = conjAut n K B' ∧
        GeneralLinearGroup.det B' = GeneralLinearGroup.det B ^ j := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hcc, -, hfc, hδδ, hδc, -⟩ := standard_automorphism_transport (K := K) (n := n)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  obtain ⟨m, hm, hσm⟩ := exists_odd_zpow h2 σ
  have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hδδ
  have hconjA : ∀ C : GL (Fin n) K,
      conjAut n K A * conjAut n K C * (conjAut n K A)⁻¹ = conjAut n K (A * C * A⁻¹) := by
    intro C
    rw [map_mul, map_mul, map_inv]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · refine ⟨m, hm, fun B => ⟨A * GeneralLinearGroup.map (σ : K →+* K) B * A⁻¹, ?_, ?_⟩⟩
    · rw [pow_zero, mul_one, _root_.mul_inv_rev]
      calc conjAut n K A * fieldAut n K σ * conjAut n K B *
            ((fieldAut n K σ)⁻¹ * (conjAut n K A)⁻¹)
          = conjAut n K A * (fieldAut n K σ * conjAut n K B * (fieldAut n K σ)⁻¹) *
            (conjAut n K A)⁻¹ := by group
        _ = _ := by rw [hfc, hconjA]
    · rw [map_mul, map_mul, map_inv, det_map, hσm, mul_comm, ← mul_assoc, inv_mul_cancel,
        one_mul]
  · refine ⟨-m, hm.neg, fun B => ⟨A * GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose B) * A⁻¹, ?_, ?_⟩⟩
    · rw [pow_one, _root_.mul_inv_rev, _root_.mul_inv_rev, hδinv]
      calc conjAut n K A * fieldAut n K σ * dualAut n K * conjAut n K B *
            (dualAut n K * ((fieldAut n K σ)⁻¹ * (conjAut n K A)⁻¹))
          = conjAut n K A * (fieldAut n K σ * (dualAut n K * conjAut n K B * dualAut n K) *
            (fieldAut n K σ)⁻¹) * (conjAut n K A)⁻¹ := by group
        _ = _ := by rw [hδc, hfc, hconjA]
    · rw [map_mul, map_mul, map_inv, det_map, hσm, det_inverseTranspose, mul_comm, ← mul_assoc,
        inv_mul_cancel, one_mul, _root_.inv_zpow']

theorem outTwoNilp_l4 (h2 : (2 : K) ≠ 0) : OutTwoNilp (projectiveSL 4 K) := by
  refine OutL.outTwoNilp_of_diag (linearAutGroup 4 K) (fun δ hδ => ⟨2, ?_⟩)
    (CFSG.ClassicalInvolution.Q3.TA3.Q5L3.commutator_mem_linearAutGroup (by norm_num)) ?_
  · obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hδ
    rw [← map_pow]
    exact conjAut_mem_range_of_det _ (GeneralLinearGroup.det A) (by rw [map_pow]; norm_num)
  · intro α δ hδ
    obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hδ
    obtain ⟨j, ⟨s, rfl⟩, hjB⟩ := exists_det_zpow h2 (by norm_num) α
    obtain ⟨B', hB', hdB'⟩ := hjB B
    obtain ⟨B'', hB'', hdB''⟩ := hjB B'
    have h1 : α ^ 2 * conjAut 4 K B * (α ^ 2)⁻¹ = conjAut 4 K B'' := by
      rw [← hB'', ← hB', pow_two, _root_.mul_inv_rev]
      simp only [mul_assoc]
    rw [h1, ← map_inv, ← map_mul]
    refine conjAut_mem_range_of_det _ (GeneralLinearGroup.det B ^ (s * (s + 1))) ?_
    rw [map_mul, map_inv, hdB'', hdB']
    group

end OutL4

open OutL4 in
theorem outCell_fl4 : OutCell FL4 := by
  intro Y _ _ _ hY
  obtain ⟨p, f, hp, hf, hp2, -, hLie⟩ := hY
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rwa [ringChar.eq F p])
  exact OutL.outTwoNilp_of_equiv e (outTwoNilp_l4 h2)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
