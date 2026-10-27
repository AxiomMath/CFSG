module

public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UHerm
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

open Matrix
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open CFSG.LieType.Universal.Unitary

namespace CFSG.ClassicalGroups.Unitary

theorem exists_singer_SUid {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) {q : ℕ}
    (hq : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) {p : ℕ} [Fact p.Prime]
    (hpq : p ∣ q ^ 2 - q + 1) :
    ∃ τ ρ : GL (Fin 3) K, τ ∈ CFSG.LieType.Universal.Unitary.SUid σ 3 ∧
      ρ ∈ CFSG.LieType.Universal.Unitary.SUid σ 3 ∧ orderOf τ = p ∧
        ρ * τ * ρ⁻¹ = τ ^ (q ^ 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  have hqpos : 0 < q := by
    have h : 0 < q ^ 2 := by rw [← hq]; exact Nat.card_pos
    exact Nat.pos_of_ne_zero (by rintro rfl; norm_num at h)
  have hq1 : 1 ≤ q := hqpos
  have hex : ∃ f : ℕ, q = 2 ^ f := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hq2 : q ^ 2 = 2 ^ (n : ℕ) := by rw [← hq, Nat.card_eq_fintype_card, hn]
    have hdvd : q ∣ 2 ^ (n : ℕ) := ⟨q, by rw [pow_two] at hq2; exact hq2.symm⟩
    obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hex
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f := by
    ext c
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← hf, hσ]
  have hIU : IsUnitaryInvolution σ := by
    have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [← hf]; exact hq
    rw [hσeq]
    exact isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  let E := FiniteField.Extension K 2 3
  haveI hCE : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  haveI hEE : ExpChar E 2 := expChar_prime (R := E) 2
  letI : Fintype E := Fintype.ofFinite E
  have hfin : Module.finrank K E = 3 := FiniteField.finrank_extension K 2 3
  have hcardE : Nat.card E = q ^ 6 := by
    rw [FiniteField.natCard_extension K 2 3, hq]
    ring
  let β : E ≃+* E := iterateFrobeniusEquiv E 2 (3 * f)
  have hβapp : ∀ x : E, β x = x ^ (q ^ 3) := by
    intro x
    rw [show β x = (iterateFrobenius E 2 (3 * f)) x from rfl, iterateFrobenius_def, hf]
    ring_nf
  have hββ : ∀ x : E, β (β x) = x := by
    intro x
    rw [hβapp, hβapp, ← pow_mul]
    have h : q ^ 3 * q ^ 3 = q ^ 6 := by ring
    rw [h]
    have hc' : Fintype.card E = q ^ 6 := by rw [← Nat.card_eq_fintype_card, hcardE]
    rw [← hc']
    exact FiniteField.pow_card x
  have hpowK : ∀ c : K, c ^ (q ^ 2) = c := by
    intro c
    have hc' : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hq
    rw [← hc']
    exact FiniteField.pow_card c
  have hβK : ∀ c : K, β (algebraMap K E c) = algebraMap K E (σ c) := by
    intro c
    rw [hβapp, ← map_pow, show q ^ 3 = q ^ 2 * q by ring, pow_mul, hpowK, hσ]
  let φ : E ≃ₐ[K] E := FiniteField.frobeniusAlgEquivOfAlgebraic K E
  have hφapp : ∀ x : E, φ x = x ^ (q ^ 2) := by
    intro x
    show (FiniteField.frobeniusAlgEquivOfAlgebraic K E) x = x ^ (q ^ 2)
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    have hc : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hq
    rw [hc]
  let B : E →ₛₗ[(σ : K →+* K)] E →ₗ[K] K := hermForm σ β hβK
  have hBform : ∀ x y : E, B x y = Algebra.trace K E (β x * y) := fun x y => rfl
  have hBsymm : B.IsSymm := LinearMap.IsSymm.mk (hermForm_symm σ hβK hββ)
  have hBnondegR : ∀ y : E, (∀ x : E, B x y = 0) → y = 0 :=
    fun y => hermForm_nondeg σ hβK hββ
  have hBsep : B.SeparatingLeft := by
    rw [LinearMap.separatingLeft_iff_linear_nontrivial]
    intro x hx
    apply hBnondegR x
    intro y
    have hxy0 : B x y = 0 := by
      have := congrArg (fun f : E →ₗ[K] K => f y) hx
      simpa using this
    have h := hermForm_symm σ hβK hββ y x
    apply σ.injective
    rw [h, hxy0, map_zero]
  obtain ⟨c₀, hc₀⟩ := hIU.exists_ne
  obtain ⟨e, he⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_orthonormal_basis_of_norm
    (B := B) hBsymm hBsep hc₀ hIU.norm_surj
  let e3 : Module.Basis (Fin 3) K E := e.reindex (finCongr hfin)
  have he3 : ∀ i j : Fin 3, B (e3 i) (e3 j) = if i = j then 1 else 0 := by
    intro i j
    rw [show e3 i = e ((finCongr hfin).symm i) from Module.Basis.reindex_apply e (finCongr hfin) i]
    rw [show e3 j = e ((finCongr hfin).symm j) from Module.Basis.reindex_apply e (finCongr hfin) j]
    rw [he]
    simp [finCongr]
  have hgram : gram σ hβK e3 = 1 := by
    ext i j
    rw [CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.gram_apply, he3]
    by_cases h : i = j
    · rw [if_pos h, Matrix.one_apply, if_pos h]
    · rw [if_neg h, Matrix.one_apply, if_neg h]
  have hqle : q ≤ q ^ 2 := by nlinarith
  have hq3fac : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    zify [hq1, hqle]
    ring
  have hp3 : p ∣ q ^ 3 + 1 := by
    rw [hq3fac]
    exact dvd_mul_of_dvd_right hpq (q + 1)
  have hq4fac : q ^ 4 + q ^ 2 + 1 = (q ^ 2 + q + 1) * (q ^ 2 - q + 1) := by
    zify [hq1, hqle]
    ring
  have hpn : p ∣ q ^ 4 + q ^ 2 + 1 := by
    rw [hq4fac]
    exact dvd_mul_of_dvd_right hpq (q ^ 2 + q + 1)
  have hpL : p ∣ Nat.card Eˣ := by
    rw [Nat.card_units, hcardE]
    have hdvd : q ^ 3 + 1 ∣ q ^ 6 - 1 := by
      have hq3ge : 1 ≤ q ^ 3 := by nlinarith
      have hq6ge : 1 ≤ q ^ 6 := by nlinarith
      have h : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
        zify [hq1, hq3ge, hq6ge]
        ring
      rw [h]
      exact dvd_mul_left _ _
    exact hp3.trans hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpL
  have hy_pow_of_dvd : ∀ {m : ℕ}, p ∣ m → (y : E) ^ m = 1 := by
    intro m hm
    have h : y ^ m = 1 := by
      exact orderOf_dvd_iff_pow_eq_one.mp (by rwa [hy])
    simpa using congrArg (fun u : Eˣ => (u : E)) h
  have hβy : β (y : E) * (y : E) = 1 := by
    rw [hβapp, ← pow_succ]
    exact hy_pow_of_dvd hp3
  have hnorm : Algebra.norm K (y : E) = 1 := by
    apply (algebraMap K E).injective
    rw [FiniteField.algebraMap_norm_eq_pow_sum K E]
    rw [hfin]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [pow_zero, pow_one, pow_two, pow_three, zero_add, add_zero, one_mul,
      mul_one]
    rw [hq]
    have hexp : q ^ 2 * q ^ 2 = q ^ 4 := by ring
    rw [hexp]
    rw [show 1 + q ^ 2 + q ^ 4 = q ^ 4 + q ^ 2 + 1 by ring]
    rw [hy_pow_of_dvd hpn, map_one]
  let L : Matrix (Fin 3) (Fin 3) K := Algebra.leftMulMatrix e3 (y : E)
  have hLdet : L.det = 1 := by
    change (Algebra.leftMulMatrix e3 (y : E)).det = 1
    rw [← Algebra.norm_eq_matrix_det, hnorm]
  let τ : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero L (by rw [hLdet]; exact one_ne_zero)
  have hLiso : ∀ x z : E, B (Algebra.lmul K E (y : E) x) (Algebra.lmul K E (y : E) z) =
      B x z := by
    intro x z
    change B (y * x) (y * z) = B x z
    calc B (y * x) (y * z) = Algebra.trace K E (β (y * x) * ((y : E) * z)) := hBform _ _
      _ = Algebra.trace K E ((β (y : E) * β x) * ((y : E) * z)) := by
            rw [map_mul β (y : E) x]
      _ = Algebra.trace K E (β x * z) := by
            congr 1
            calc (β (y : E) * β x) * ((y : E) * z) =
                (β (y : E) * (y : E)) * (β x * z) := by ring
              _ = β x * z := by rw [hβy, one_mul]
      _ = B x z := (hBform _ _).symm
  have hLgram : conjTr σ L * L = 1 := by
    have hiso : ∀ x z, hermForm σ β hβK (Algebra.lmul K E (y : E) x)
        (Algebra.lmul K E (y : E) z) = hermForm σ β hβK x z := by
      intro x z
      simpa only [B] using hLiso x z
    have h := conjTr_mul_gram_mul (σ := σ) (β := β) (hβK := hβK) (b := e3)
      (T := Algebra.lmul K E (y : E)) hiso
    have hmat : LinearMap.toMatrix e3 e3 (Algebra.lmul K E (y : E)) = L := by
      rw [← Algebra.leftMulMatrix_apply]
    rw [hgram, hmat] at h
    simpa using h
  have hτmem : τ ∈ SUid σ 3 := by
    rw [mem_SUid]
    constructor
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hLdet
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hLgram
  have hτpow : ∀ m : ℕ, ((τ ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Algebra.leftMulMatrix e3 ((y : E) ^ m) := by
    intro m
    rw [← Units.val_pow_eq_pow_val]
    change L ^ m = Algebra.leftMulMatrix e3 ((y : E) ^ m)
    rw [show L = Algebra.leftMulMatrix e3 (y : E) from rfl, ← map_pow]
  have hτord : orderOf τ = p := by
    rw [← hy]
    apply orderOf_eq_orderOf_iff.mpr
    intro m
    constructor
    · intro h
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      have h' : ((τ ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [h]
        rfl
      rw [hτpow] at h'
      refine Algebra.leftMulMatrix_injective e3 ?_
      simpa using h'
    · intro h
      apply Units.ext
      rw [hτpow]
      have hm : (y : E) ^ m = 1 := by
        rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
      rw [hm, map_one]
      rfl
  have hβφ : ∀ x : E, β (φ x) = φ (β x) := by
    intro x
    rw [hβapp, hφapp, hφapp, hβapp, ← pow_mul, ← pow_mul]
    congr 1
    ring
  let M : Matrix (Fin 3) (Fin 3) K := LinearMap.toMatrix e3 e3 φ.toLinearMap
  have hφiso : ∀ x z : E, B (φ x) (φ z) = B x z := by
    intro x z
    calc B (φ x) (φ z) = Algebra.trace K E (β (φ x) * φ z) := hBform _ _
      _ = Algebra.trace K E (φ (β x) * φ z) := by rw [hβφ]
      _ = Algebra.trace K E (φ (β x * z)) := by rw [← map_mul]
      _ = Algebra.trace K E (β x * z) := Algebra.trace_eq_of_algEquiv φ (β x * z)
      _ = B x z := (hBform _ _).symm
  have hφgram : conjTr σ M * M = 1 := by
    have hiso : ∀ x z, hermForm σ β hβK (φ x) (φ z) = hermForm σ β hβK x z := by
      intro x z
      simpa only [B] using hφiso x z
    have h := conjTr_mul_gram_mul (σ := σ) (β := β) (hβK := hβK) (b := e3)
      (T := φ.toLinearMap) hiso
    rw [hgram] at h
    have hmat : LinearMap.toMatrix e3 e3 φ.toLinearMap = M := rfl
    rw [hmat] at h
    simpa using h
  have hφeq : φ.toLinearMap = (FiniteField.frobeniusAlgHom K E).toLinearMap := by
    ext x
    show φ x = (FiniteField.frobeniusAlgHom K E) x
    rw [hφapp, FiniteField.coe_frobeniusAlgHom]
    have hc : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hq
    rw [hc]
  have hmin : minpoly K φ.toLinearMap = Polynomial.X ^ 3 - 1 := by
    rw [hφeq]
    simpa [hfin] using FiniteField.minpoly_frobeniusAlgHom K E
  have hchar : φ.toLinearMap.charpoly = Polynomial.X ^ 3 - 1 := by
    have hdvd := LinearMap.minpoly_dvd_charpoly φ.toLinearMap
    rw [hmin] at hdvd
    have hdeg : φ.toLinearMap.charpoly.natDegree ≤
        (Polynomial.X ^ 3 - 1 : Polynomial K).natDegree := by
      rw [LinearMap.charpoly_natDegree, hfin]
      rw [show (Polynomial.X ^ 3 - 1 : Polynomial K).natDegree = 3 by
        simpa using (Polynomial.natDegree_X_pow_sub_C (n := 3) (r := (1 : K)))]
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (Polynomial.monic_X_pow_sub_C (1 : K) (by norm_num : (3 : ℕ) ≠ 0))
      (LinearMap.charpoly_monic _) hdvd hdeg
  have hdet : LinearMap.det φ.toLinearMap = 1 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, hchar, hfin]
    norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_one]
  have hMdet : M.det = 1 := by
    change (LinearMap.toMatrix e3 e3 φ.toLinearMap).det = 1
    rw [LinearMap.det_toMatrix, hdet]
  let ρ : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero)
  have hρmem : ρ ∈ SUid σ 3 := by
    rw [mem_SUid]
    constructor
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hMdet
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hφgram
  have hSL : M * L = Algebra.leftMulMatrix e3 ((y : E) ^ (q ^ 2)) * M := by
    have hlin : φ.toLinearMap * Algebra.lmul K E (y : E) =
        Algebra.lmul K E ((y : E) ^ (q ^ 2)) * φ.toLinearMap := by
      apply LinearMap.ext
      intro x
      change φ ((y : E) * x) = (y : E) ^ (q ^ 2) * φ x
      rw [map_mul, hφapp]
    have h := congrArg (LinearMap.toMatrix e3 e3) hlin
    simpa [M, L, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_mul] using h
  have hcomm : ρ * τ = τ ^ (q ^ 2) * ρ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    rw [show (ρ : Matrix (Fin 3) (Fin 3) K) = M from
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero M _]
    rw [show (τ : Matrix (Fin 3) (Fin 3) K) = L from
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero L _]
    rw [hτpow (q ^ 2)]
    exact hSL
  have hrel : ρ * τ * ρ⁻¹ = τ ^ (q ^ 2) := by
    rw [hcomm]
    group
  exact ⟨τ, ρ, hτmem, hρmem, hτord, hrel⟩

end CFSG.ClassicalGroups.Unitary

end
