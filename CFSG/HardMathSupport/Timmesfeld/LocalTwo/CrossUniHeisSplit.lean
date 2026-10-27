module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeisPair
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeisCount
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeisTau
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeisField

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryPair CFSG.RankThree.PartOne.KCUnitaryGt
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem mulVec_pow_eigen {m : ℕ} {Xm : Matrix (Fin m) (Fin m) K} {v : Fin m → K} {lam : K}
    (hv : Xm *ᵥ v = lam • v) (k : ℕ) : Xm ^ k *ᵥ v = lam ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]

theorem mulVec_pow_shift {m : ℕ} {Xm Ym : Matrix (Fin m) (Fin m) K} {κ : K}
    (hXY : Xm * Ym = κ • (Ym * Xm)) {v : Fin m → K} {lam : K} (hv : Xm *ᵥ v = lam • v) (k : ℕ) :
    Xm *ᵥ (Ym ^ k *ᵥ v) = (κ ^ k * lam) • (Ym ^ k *ᵥ v) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    calc Xm *ᵥ (Ym ^ (k + 1) *ᵥ v) = Xm *ᵥ (Ym *ᵥ (Ym ^ k *ᵥ v)) := by
          rw [pow_succ']
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (Xm * Ym) *ᵥ (Ym ^ k *ᵥ v) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = κ • (Ym *ᵥ (Xm *ᵥ (Ym ^ k *ᵥ v))) := by
          rw [hXY, Matrix.smul_mulVec]
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = κ • (Ym *ᵥ ((κ ^ k * lam) • (Ym ^ k *ᵥ v))) := by rw [ih]
      _ = (κ ^ (k + 1) * lam) • (Ym ^ (k + 1) *ᵥ v) := by
          rw [Matrix.mulVec_smul, smul_smul, pow_succ' Ym k, ← Matrix.mulVec_mulVec]
          congr 1
          ring

theorem mulVec_pow_ne_zero {m : ℕ} {Ym : Matrix (Fin m) (Fin m) K} (hY : IsUnit Ym) (k : ℕ)
    {v : Fin m → K} (hv : v ≠ 0) : Ym ^ k *ᵥ v ≠ 0 := by
  intro h0
  apply hv
  have := (Matrix.mulVec_injective_iff_isUnit.2 (hY.pow k)) (a₁ := v) (a₂ := 0)
    (by rw [h0, Matrix.mulVec_zero])
  exact this

theorem eq_one_of_mem_localDeltaIn_heis (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq3 : 3 < ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hn2p : 2 * p ≤ n)
    {A B : primeFormUnitary h (idGram K n)} {c : Kˣ} (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hAB : (A : GL (Fin n) K) * B = B * A * GeneralLinearGroup.scalar (Fin n) c)
    (hA : A ^ p = 1) (hA1 : primeFormConjHom h (idGram K n) A ≠ 1)
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    (hAE : primeFormConjHom h (idGram K n) A ∈ E) (hBE : primeFormConjHom h (idGram K n) B ∈ E)
    {g : MulAut (primeFormP h (idGram K n))} (hg : g ∈ localDeltaIn p H E) : g = 1 := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hpℓ : p ≠ ℓ := ne_char_of_dvd_add_one hp hpq h.one_le
  have hn0 : 0 < n := by omega
  obtain ⟨b, μ, μB, hbON, hAe, -⟩ :=
    exists_orthonormal_eigenbasis_pair hp hpq (A := A) (B := 1) (by simp) hA (by simp)
  have hb0 : ∀ i, b i ≠ 0 := fun i => b.ne_zero i
  have hμp : ∀ i, μ i ^ p = 1 := fun i => eigenvalue_pow_eq_one hA (hb0 i) (hAe i)
  obtain ⟨ζ, hζ, hζn⟩ := exists_norm_one_primitiveRoot (h := h) hp hpq
  have hζ' := exists_norm_one_ne_one_sq_ne_one (h := h) hp hp2 hpq
  have hcK : IsPrimitiveRoot (c : K) p := by
    refine IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime ?_ ?_)
    · rw [← Units.val_pow_eq_pow_val, hcp, Units.val_one]
    · exact fun h' => hc1 (Units.ext h')
  have hcn : h.norm (c : K) = 1 := by
    rw [← pow_succ_eq_one_iff_norm h]
    obtain ⟨r, hr⟩ := hpq
    rw [hr, pow_mul, hcp, one_pow]
  have hc2 : (c : K) ^ 2 ≠ 1 := by
    intro h2
    have := hcK.dvd_of_pow_eq_one 2 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hABm := gl_comm_matrix hAB
  have hpartner : ∀ i, ∃ j, j ≠ i ∧ μ j = μ i := by
    intro i
    refine exists_partner (a := ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (b := b) hAe
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K) (toLinU h n B)) hp hcK
      ?_ hμp ?_ i
    · intro v
      rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
      change ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (((toLinU h n B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v) = (c : K) • ((toLinU h n B : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) (((toLinU h n A :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v)
      rw [toLinU_apply_eq, toLinU_apply_eq, toLinU_apply_eq, toLinU_apply_eq, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hABm, Matrix.smul_mulVec]
    · simpa using hn2p
  obtain ⟨⟨M', τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn hne g
  set Ψ := primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M', τ⟩ with hΨ
  have hgA := commute_of_mem_localDeltaIn hg hAE
  have hgB := commute_of_mem_localDeltaIn hg hBE
  have hτc : τ (c : K) = c := tau_fixes_of_commute hn hne hAB hgA hgB
  have hMunit : IsUnit ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := (M' : GL (Fin n) K).isUnit
  have hAs : (A : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hA
    simpa using this
  have H0 := primaryData_of_pow_eq_scalar hp hpℓ hAs
  have hcert : ∀ i j : Fin n, i ≠ j → μ i = μ j →
      h.bar (μ i) * μ i = 1 ∧
      ∃ (hmem : (X - C (μ i) : K[X]) ∈ primaryFactors ((toLinU h n A :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))),
        IsGoodBlock h (toLinU h n A) ⟨X - C (μ i), hmem⟩ ∧
        TorusComm h ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) τ (b i) (b j) ∧
        ∀ Y ∈ gBlock h A (X - C (μ i)), Ψ * primeFormConjHom h (idGram K n) Y =
          primeFormConjHom h (idGram K n) Y * Ψ := by
    intro i j hij hμij
    have hμ : h.bar (μ i) * μ i = 1 := bar_eq_inv_of_pow_eq_one h hpq (hμp i)
    have hx₁ := hAe i
    have hx₂ : ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b j) = μ i • b j := by rw [hμij]; exact hAe j
    obtain ⟨hmem, hgood⟩ := isGoodBlock_of_eigenpair (h := h) hq3 (hbON.pair hij) hx₁ hx₂
    have hβ : ∀ Y ∈ gBlock h A (X - C (μ i)), Ψ * primeFormConjHom h (idGram K n) Y =
        primeFormConjHom h (idGram K n) Y * Ψ :=
      commute_of_mem_localDeltaIn_gBlock hp hn hne hq2 H0 ⟨X - C (μ i), hmem⟩ hgood hH hg hAE hA1
        (dvd_card_map_gBlock_of_torus hp hp2 hn hne H0 hμ hmem (hbON.pair hij) hx₁ hx₂ hζ hζn)
    exact ⟨hμ, hmem, hgood, torusComm_of_block hn hne hq2 H0 hμ hmem hgood (hbON.pair hij) hx₁ hx₂
      M' τ hβ, hβ⟩
  have hτ : τ = RingEquiv.refl K := by
    obtain ⟨i0, -⟩ : ∃ i0 : Fin n, True := ⟨⟨0, hn0⟩, trivial⟩
    obtain ⟨j0, hj0, hμj0⟩ := hpartner i0
    obtain ⟨-, -, -, hTC, -⟩ := hcert i0 j0 (Ne.symm hj0) hμj0.symm
    exact tau_eq_one_of_pair hMunit (hbON.pair (Ne.symm hj0)) hTC (c := c) c.ne_zero hcn hc2 hτc
  subst hτ
  have hmat1 := hmat_refl (n := n) (K := K)
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hTC : ∀ i j : Fin n, i ≠ j → μ i = μ j →
      TorusComm h ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (RingEquiv.refl K) (b i) (b j) :=
    fun i j hij hμ => (hcert i j hij hμ).2.choose_spec.2.1
  have hdiag : ∀ i, ∃ d : K, ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i =
      d • b i := by
    intro i
    obtain ⟨j, hj, hμj⟩ := hpartner i
    exact (exists_smul_of_torusComm (hbON.pair hj.symm) (hTC i j hj.symm hμj.symm) hζ').1
  have hMM : M' * A = A * M' := by
    apply toLinU_injective (h := h) (n := n)
    apply Units.ext
    refine b.ext fun l => ?_
    obtain ⟨d, hd⟩ := hdiag l
    have e1 : ((toLinU h n M' : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (b l) = d • b l := by rw [toLinU_apply_eq]; exact hd
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply,
      Module.End.mul_apply, hAe, e1, map_smul, map_smul, hAe, e1, smul_smul, smul_smul, mul_comm]
  have hscal : ∀ i, ∃ d : K, ∀ v : Fin n → K,
      ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v =
        μ i • v → ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = d • v := by
    intro i
    obtain ⟨j, hj, hμj⟩ := hpartner i
    obtain ⟨hμ, hmem, hgood, hTC', hβ⟩ := hcert i j (Ne.symm hj) hμj.symm
    have hF : Group.IsPerfect (gBlock h A (X - C (μ i))) :=
      (isQuasisimple_gBlock hq2 H0 ⟨X - C (μ i), hmem⟩ hgood).1
    have hblock' : ∀ g ∈ gBlock h A (X - C (μ i)), M' * g = g * M' := by
      intro g hg
      have := matrix_comm_of_perfect hn hne hF M' (RingEquiv.refl K) hβ g hg
      rw [hmat1] at this
      exact Subtype.ext (Units.ext this)
    exact exists_scalar_of_commute_gBlock_X_sub_C hq2 H0 hmem hgood M' hMM hblock'
  have hΨρ : Ψ = primeFormConjHom h (idGram K n) M' := hΨ.trans (psi_refl_eq M')
  obtain ⟨e, he⟩ := exists_scalar_of_conj_commute hn hne (A := M') (B := B)
    (by rw [← hΨρ]; exact hgB)
  have hMB := gl_comm_matrix he
  have hAv : ∀ i, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = μ i • b i := fun i => by
    have := hAe i
    rwa [toLinU_apply_eq] at this
  have hscal' : ∀ i, ∃ d : K, ∀ v : Fin n → K,
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = μ i • v →
        ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = d • v := by
    intro i
    obtain ⟨d, hd⟩ := hscal i
    exact ⟨d, fun v hv => hd v (by rw [toLinU_apply_eq]; exact hv)⟩
  have hBunit : IsUnit ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := (B : GL (Fin n) K).isUnit
  have hlam0p : ∀ i, μ i ^ p = 1 := hμp
  obtain ⟨d0, hd0⟩ := hscal' ⟨0, hn0⟩
  have hv0 : b ⟨0, hn0⟩ ≠ 0 := hb0 _
  have hMv0 : ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b ⟨0, hn0⟩ =
      d0 • b ⟨0, hn0⟩ := hd0 _ (hAv _)
  have hd00 : d0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hMv0
    exact hv0 ((Matrix.mulVec_injective_iff_isUnit.2 hMunit) (a₁ := b ⟨0, hn0⟩) (a₂ := 0)
      (by rw [hMv0, Matrix.mulVec_zero]))
  have hshiftA := fun k => mulVec_pow_shift hABm (hAv ⟨0, hn0⟩) k
  have hshiftM := fun k => mulVec_pow_shift hMB hMv0 k
  have hcpK : (c : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hcp, Units.val_one]
  have hep : (e : K) ^ p = 1 := by
    have hw0 := mulVec_pow_ne_zero hBunit p hv0
    have h1 := hd0 _ (by rw [hshiftA p, hcpK, one_mul])
    rw [hshiftM p] at h1
    have h2 := smul_left_injective K hw0 h1
    exact mul_right_cancel₀ hd00 (by rw [h2, one_mul])
  obtain ⟨j, hj, hjc⟩ := hcK.eq_pow_of_pow_eq_one hep
  have hdi : ∀ i, ∃ k : ℕ, k < p ∧ μ i = (c : K) ^ k * μ ⟨0, hn0⟩ ∧ ∀ v,
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = μ i • v →
        ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ((e : K) ^ k * d0) • v := by
    intro i
    have hl0 : μ ⟨0, hn0⟩ ≠ 0 := by
      intro h0
      have := hlam0p ⟨0, hn0⟩
      rw [h0, zero_pow hp.ne_zero] at this
      exact zero_ne_one this
    have h1 : (μ i / μ ⟨0, hn0⟩) ^ p = 1 := by rw [div_pow, hlam0p i, hlam0p, div_one]
    obtain ⟨k, hk, hk'⟩ := hcK.eq_pow_of_pow_eq_one h1
    have hμi : μ i = (c : K) ^ k * μ ⟨0, hn0⟩ := by rw [hk', div_mul_cancel₀ _ hl0]
    obtain ⟨di, hdi⟩ := hscal' i
    have hw0 := mulVec_pow_ne_zero hBunit k hv0
    have h2 := hdi _ (by rw [hshiftA k, hμi])
    rw [hshiftM k] at h2
    have h3 := smul_left_injective K hw0 h2
    refine ⟨k, hk, hμi, fun v hv => ?_⟩
    rw [hdi v hv, ← h3]
  set M'' : primeFormUnitary h (idGram K n) := M' * A ^ (p - j) with hM''
  have hM''b : ∀ i, ((M'' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i =
      (μ ⟨0, hn0⟩ ^ (p - j) * d0) • b i := by
    intro i
    obtain ⟨k, hk, hμk, hMk⟩ := hdi i
    rw [hM'', Subgroup.coe_mul, Units.val_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val,
      ← Matrix.mulVec_mulVec, mulVec_pow_eigen (hAv i), Matrix.mulVec_smul, hMk _ (hAv i),
      smul_smul]
    congr 1
    rw [hμk, ← hjc, mul_pow, ← pow_mul, ← pow_mul]
    have h1 : (c : K) ^ (k * (p - j)) * (c : K) ^ (j * k) = 1 := by
      have : k * (p - j) + j * k = p * k := by
        calc k * (p - j) + j * k = k * ((p - j) + j) := by ring
          _ = k * p := by rw [Nat.sub_add_cancel hj.le]
          _ = p * k := mul_comm _ _
      rw [← pow_add, this, pow_mul, hcpK, one_pow]
    linear_combination (μ ⟨0, hn0⟩ ^ (p - j) * d0) * h1
  have hlin : Matrix.toLin' ((M'' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (μ ⟨0, hn0⟩ ^ (p - j) * d0) • LinearMap.id := by
    refine b.ext fun i => ?_
    rw [Matrix.toLin'_apply, hM''b]
    simp
  have hρM'' : primeFormConjHom h (idGram K n) M'' = 1 := by
    have h1 := psi_eq_one_of_scalar hn hne M'' (μ ⟨0, hn0⟩ ^ (p - j) * d0) (fun v => by
      have := LinearMap.congr_fun hlin v
      simpa [Matrix.toLin'_apply] using this)
    rwa [psi_refl_eq] at h1
  have hM'eq : M' = M'' * A ^ j := by
    rw [hM'', mul_assoc, ← pow_add, Nat.sub_add_cancel hj.le, hA, mul_one]
  have hΨA : Ψ = primeFormConjHom h (idGram K n) A ^ j := by
    rw [hΨρ, hM'eq, map_mul, hρM'', one_mul, map_pow]
  have hcop := coprime_orderOf_of_mem_localDeltaIn hp hg hAE hA1
  have hΨp : Ψ ^ p = 1 := by
    rw [hΨA, ← pow_mul, mul_comm, pow_mul, ← map_pow, hA, map_one, one_pow]
  have hdvd : orderOf Ψ ∣ p := orderOf_dvd_of_pow_eq_one hΨp
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
