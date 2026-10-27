module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Frame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Comb
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DGood
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DNonsplit
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryBlock

variable {ℓ f n m : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Tau

theorem tau_apply_eq_inv (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {τ : K ≃+* K} (hτ : τ ≠ RingEquiv.refl K) {ν : K}
    (hν : ν ^ 3 = 1) : τ ν = ν⁻¹ := by
  by_cases hν1 : ν = 1
  · rw [hν1, map_one, inv_one]
  have hν0 : ν ≠ 0 := by
    rintro rfl
    norm_num at hν
  have hτν : τ ν ≠ ν := fun hfix => hτ (ringEquiv_eq_one_of_fix h hq hν0 hν1 hfix)
  have hτν3 : (τ ν) ^ 3 = 1 := by rw [← map_pow, hν, map_one]
  have hτν1 : τ ν ≠ 1 := fun h1 => hν1 (τ.injective (by rw [h1, map_one]))
  have e1 : ν ^ 2 + ν + 1 = 0 := by
    have : (ν - 1) * (ν ^ 2 + ν + 1) = 0 := by linear_combination hν
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hν1)
  have e2 : (τ ν) ^ 2 + τ ν + 1 = 0 := by
    have : (τ ν - 1) * ((τ ν) ^ 2 + τ ν + 1) = 0 := by linear_combination hτν3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hτν1)
  have e3 : ν + τ ν + 1 = 0 := by
    have : (ν - τ ν) * (ν + τ ν + 1) = 0 := by linear_combination e1 - e2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hτν))
  refine eq_inv_of_mul_eq_one_right ?_
  linear_combination (-1 : K) * e1 + ν * e3

end Tau

section Semilinear

theorem exists_semilinear_scalar (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {x M : primeFormUnitary h (idGram K n)} {τ : K ≃+* K}
    (hcomm : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) x =
      primeFormConjHom h (idGram K n) x *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    ∃ c : Kˣ, c ^ (ℓ ^ f + 1) = 1 ∧
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
        (c : K) • (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  set w : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
    (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K) := ⟨M, τ⟩ with hw
  have h1 := primeFormPsi_conj_primeFormConjHom (h := h) (n := n) w x
  have h2 : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) w *
      primeFormConjHom h (idGram K n) x *
        (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) w)⁻¹ =
      primeFormConjHom h (idGram K n) x := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2] at h1
  have h3 : primeFormConjHom h (idGram K n) (idUAction h n w x * x⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1, mul_inv_cancel]
  obtain ⟨c, hc, hcs⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).1 h3
  refine ⟨c, hc, ?_⟩
  have h4 : (M : GL (Fin n) K) * glAut τ (x : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹ *
      (x : GL (Fin n) K)⁻¹ = GeneralLinearGroup.scalar (Fin n) c := by
    have : ((idUAction h n w x * x⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hcs
    rw [hw, idUAction_mk] at this
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU] using this
  have h5 : (M : GL (Fin n) K) * glAut τ (x : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c * (x : GL (Fin n) K) * (M : GL (Fin n) K) := by
    have h6 : (M : GL (Fin n) K) * glAut τ (x : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) c * (x : GL (Fin n) K) := by
      rw [← h4]; group
    calc (M : GL (Fin n) K) * glAut τ (x : GL (Fin n) K)
        = (M : GL (Fin n) K) * glAut τ (x : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹ *
            (M : GL (Fin n) K) := by group
      _ = _ := by rw [h6]
  have h7 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h5
  simp only [Units.val_mul, coe_glAut, scalar_coe_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul] at h7
  exact h7

end Semilinear

section Eigenbasis

theorem exists_eigenbasis (hq : ℓ ^ f = 2) {x : primeFormUnitary h (idGram K n)}
    (hx : x ^ 3 = 1) :
    ∃ (b : Fin n → Fin n → K) (c : Fin n → K), IsOrthonormalFamily h b ∧
      ∀ i, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = c i • b i := by
  classical
  have hfin := h.finite
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  obtain ⟨ζ, hζ⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h Nat.prime_three hpq
  have : NeZero 3 := ⟨by norm_num⟩
  set T : Module.End K (Fin n → K) := ((toLinU h n x :
    LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) with hT
  have hpow : T ^ 3 = 1 := by
    have h1 : (toLinU h n x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) h1
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h2
  have hiso : ∀ v w, idForm h n (T v) (T w) = idForm h n v w := fun v w =>
    mem_sesqUnitaryGroup.mp (toLinU_mem x) v w
  obtain ⟨b, μ, hbμ, hbo⟩ := exists_orthonormal_common_eigenbasis h hζ hpq (idForm_isSymm h n)
    (idForm_separatingLeft h n) (fun _ : Unit => T) (fun _ _ => Commute.refl T)
    (fun _ => hpow) (fun _ v w => hiso v w)
  refine ⟨fun i => b.reindex (finCongr (Module.finrank_fin_fun K)) i,
    fun i => μ () ((finCongr (Module.finrank_fin_fun K)).symm i), fun i j => ?_, fun i => ?_⟩
  · simp only [Module.Basis.reindex_apply]
    rw [hbo]
    simp
  · simp only [Module.Basis.reindex_apply]
    exact hbμ () _

end Eigenbasis

section Torus

theorem torusMat_apply_perp (h : UnitaryFieldData ℓ f K) {b₁ b₂ : Fin n → K} (c : K)
    {v : Fin n → K} (h1 : idForm h n b₁ v = 0) (h2 : idForm h n b₂ v = 0) :
    torusMat h b₁ b₂ c *ᵥ v = v := by
  rw [torusMat_mulVec, h1, h2]
  simp

theorem projMat_mul_of_fix (h : UnitaryFieldData ℓ f K) {b : Fin n → K}
    {Y : Matrix (Fin n) (Fin n) K} (hY : Y *ᵥ b = b) : Y * projMat h b = projMat h b := by
  rw [projMat, Matrix.mul_vecMulVec, hY]

theorem mul_projMat_of_fix (h : UnitaryFieldData ℓ f K) {b : Fin n → K}
    {Y : Matrix (Fin n) (Fin n) K} (hY : adj h Y *ᵥ b = b) : projMat h b * Y = projMat h b := by
  rw [projMat, Matrix.vecMulVec_mul]
  congr 1
  funext k
  have := congrFun hY k
  simp only [Matrix.mulVec, dotProduct, adj, Matrix.transpose_apply, Matrix.map_apply] at this
  have h2 := congrArg h.bar this
  simp only [map_sum, map_mul, h.bar_bar] at h2
  simp only [Matrix.vecMul, dotProduct]
  rw [← h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem comm_torusMat_of_fix (h : UnitaryFieldData ℓ f K) {b₁ b₂ : Fin n → K} (c : K)
    {Y : Matrix (Fin n) (Fin n) K} (h1 : Y *ᵥ b₁ = b₁) (h2 : Y *ᵥ b₂ = b₂)
    (h1' : adj h Y *ᵥ b₁ = b₁) (h2' : adj h Y *ᵥ b₂ = b₂) :
    Y * torusMat h b₁ b₂ c = torusMat h b₁ b₂ c * Y := by
  unfold torusMat
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, projMat_mul_of_fix h h1, projMat_mul_of_fix h h2, mul_projMat_of_fix h h1',
    mul_projMat_of_fix h h2']

theorem eigen_orth (h : UnitaryFieldData ℓ f K) {x : primeFormUnitary h (idGram K n)} {μ μ' : K}
    (hμ : h.bar μ * μ = 1) (hne : μ ≠ μ') {a b : Fin n → K}
    (ha : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a = μ • a)
    (hb : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b = μ' • b) :
    idForm h n a b = 0 := by
  have h1 := idForm_apply_of_eigen h (toLinU_mem x) hμ (b := a) (by
    show ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a = μ • a
    exact ha) b
  have h2 : idForm h n a (((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b) = μ' * idForm h n a b := by
    show idForm h n a (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b) = _
    rw [hb, map_smul, smul_eq_mul]
  rw [h2] at h1
  have h3 : (μ' - μ) * idForm h n a b = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm hne))

theorem torusMat_comm_eigen (h : UnitaryFieldData ℓ f K) {x : primeFormUnitary h (idGram K n)}
    {ν : K} (hν : h.bar ν * ν = 1) {u₁ u₂ : Fin n → K}
    (h₁ : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u₁ = ν • u₁)
    (h₂ : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u₂ = ν • u₂) (c : K) :
    torusMat h u₁ u₂ c * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * torusMat h u₁ u₂ c := by
  have key : ∀ v, (torusMat h u₁ u₂ c * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ v =
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * torusMat h u₁ u₂ c) *ᵥ v := by
    intro v
    have e1 : idForm h n u₁ (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        ν * idForm h n u₁ v :=
      idForm_apply_of_eigen h (toLinU_mem x) hν (b := u₁) h₁ v
    have e2 : idForm h n u₂ (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        ν * idForm h n u₂ v :=
      idForm_apply_of_eigen h (toLinU_mem x) hν (b := u₂) h₂ v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, torusMat_mulVec, torusMat_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h₁, h₂, e1, e2]
    module
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using key v)

theorem torusMat_pow_three (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {b₁ b₂ : Fin n → K}
    (hb : IsONPair h b₁ b₂) (c : Kˣ) :
    torusMat h b₁ b₂ c * torusMat h b₁ b₂ c * torusMat h b₁ b₂ c = 1 := by
  rw [torusMat_mul h hb, torusMat_mul h hb]
  have : ((c : K) * c * c) = 1 := by
    have := unit_pow_three_eq_one h hq c
    have h3 : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    linear_combination h3
  rw [this, torusMat_one]

end Torus

section NonFixed

theorem tau_tau (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {τ : K ≃+* K}
    (hτ : τ ≠ RingEquiv.refl K) (a : K) : τ (τ a) = a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  have h3 : a ^ 3 = 1 := pow_three_eq_one h hq ha
  rw [tau_apply_eq_inv h hq hτ h3, map_inv₀, tau_apply_eq_inv h hq hτ h3, inv_inv]

theorem mulVec_map_tau (τ : K ≃+* K) (hττ : ∀ a, τ (τ a) = a) (A : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) : A.map τ *ᵥ w = fun k => τ ((A *ᵥ fun j => τ (w j)) k) := by
  funext k
  have h1 := RingHom.map_mulVec (τ : K →+* K) A (fun j => τ (w j)) k
  have h2 : ((τ : K →+* K) ∘ fun j => τ (w j)) = w := by
    funext j
    exact hττ (w j)
  rw [h2] at h1
  exact h1.symm

theorem eigen_of_semilinear {xm Mm Mi : Matrix (Fin n) (Fin n) K} {τ : K ≃+* K}
    (hττ : ∀ a, τ (τ a) = a) {lam : K} (hrel : Mm * xm.map τ = lam • (xm * Mm))
    (hMMi : Mm * Mi = 1) (hMiM : Mi * Mm = 1) {ν : K} {u : Fin n → K} (hu : xm *ᵥ u = ν • u) :
    xm *ᵥ (fun k => τ ((Mi *ᵥ u) k)) = τ (lam * ν) • (fun k => τ ((Mi *ᵥ u) k)) := by
  set w : Fin n → K := Mi *ᵥ u with hw
  have h1 : xm.map τ = lam • (Mi * xm * Mm) := by
    calc xm.map τ = (Mi * Mm) * xm.map τ := by rw [hMiM, Matrix.one_mul]
      _ = Mi * (Mm * xm.map τ) := by rw [Matrix.mul_assoc]
      _ = lam • (Mi * xm * Mm) := by rw [hrel, Matrix.mul_smul, Matrix.mul_assoc]
  have h2 : xm.map τ *ᵥ w = (lam * ν) • w := by
    have hMw : Mm *ᵥ w = u := by rw [hw, Matrix.mulVec_mulVec, hMMi, Matrix.one_mulVec]
    rw [h1, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMw, hu,
      Matrix.mulVec_smul, smul_smul]
  have h3 := mulVec_map_tau τ hττ xm w
  rw [h2] at h3
  funext k
  have h4 := congrFun h3 k
  simp only [Pi.smul_apply, smul_eq_mul] at h4 ⊢
  have h5 := congrArg τ h4
  rw [hττ] at h5
  rw [← h5, map_mul]

theorem torus_contradiction (hn : 4 ≤ n) (hq : ℓ ^ f = 2)
    {D H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range ≤ H)
    {x M : primeFormUnitary h (idGram K n)}
    (hxD : primeFormConjHom h (idGram K n) x ∈ D) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1)
    {τ : K ≃+* K} (hτ : τ ≠ RingEquiv.refl K)
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ ∈
      localDeltaIn 3 H D)
    {lam : K} (hlam3 : lam ^ 3 = 1)
    (hrel : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
      lam • (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {ν : K} (hν3 : ν ^ 3 = 1) (hνlam : ν ≠ lam) {u₁ u₂ : Fin n → K} (hb : IsONPair h u₁ u₂)
    (h₁ : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u₁ = ν • u₁)
    (h₂ : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u₂ = ν • u₂) : False := by
  classical
  have hfin := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hν0 : ν ≠ 0 := by rintro rfl; norm_num at hν3
  have hlam0 : lam ≠ 0 := by rintro rfl; norm_num at hlam3
  have hνb : h.bar ν * ν = 1 := bar_eq_inv_of_pow_eq_one h hpq hν3
  have hττ := tau_tau h hq hτ
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set Mg : GL (Fin n) K := (M : GL (Fin n) K) with hMg
  set Mm : Matrix (Fin n) (Fin n) K := (Mg : Matrix (Fin n) (Fin n) K) with hMm
  set Mi : Matrix (Fin n) (Fin n) K := ((Mg⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have hMMi : Mm * Mi = 1 := Units.mul_inv Mg
  have hMiM : Mi * Mm = 1 := Units.inv_mul Mg
  obtain ⟨ω, hω1⟩ : ∃ ω : Kˣ, ω ≠ 1 := by
    have h3 : Nat.card Kˣ = 3 := card_units_eq_three h hq
    have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 (by rw [h3]; norm_num)
    exact exists_ne 1
  have hωnorm := norm_eq_one_of_unit h hq ω
  have hω3 : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, unit_pow_three_eq_one h hq ω, Units.val_one]
  set y : primeFormUnitary h (idGram K n) := torusUnitary h hb ω hωnorm with hy
  have hym : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = torusMat h u₁ u₂ ω := rfl
  have hySU : (y : GL (Fin n) K) ∈ gramSU h (idGram K n) :=
    (mem_gramSU_iff_unitary h).2 ⟨y.2, det_torusUnitary h hb ω hωnorm⟩
  have hρyH : primeFormConjHom h (idGram K n) y ∈ H := by
    have := primeFormConjHom_eq_conj h (idGram K n) ⟨(y : GL (Fin n) K), hySU⟩
    have h2 : primeFormConjHom h (idGram K n) y = MulAut.conj
        ((⟨(y : GL (Fin n) K), hySU⟩ : gramSU h (idGram K n)) : primeFormP h (idGram K n)) := this
    rw [h2]
    exact hH ⟨_, rfl⟩
  have hyx : y * x = x * y :=
    Subtype.ext (Units.ext (torusMat_comm_eigen h hνb h₁ h₂ ω))
  have hρcomm : primeFormConjHom h (idGram K n) y * primeFormConjHom h (idGram K n) x =
      primeFormConjHom h (idGram K n) x * primeFormConjHom h (idGram K n) y := by
    rw [← map_mul, ← map_mul, hyx]
  have hTT := coprime_orderOf_commutator_of_mem_localDeltaIn hg hxD hx1 hρyH hρcomm
  rw [primeFormPsi_conj_primeFormConjHom, ← map_inv, ← map_mul] at hTT
  set y' : primeFormUnitary h (idGram K n) := idUAction h n ⟨M, τ⟩ y with hy'
  have hy'm : ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Mm * (torusMat h u₁ u₂ ω).map τ * Mi := by
    rw [hy', idUAction_mk]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_primeFormFieldU, coe_glAut,
      hym]
    rfl
  have hfix : ∀ u : Fin n → K, xm *ᵥ u = ν • u →
      ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u := by
    intro u hu
    set w : Fin n → K := Mi *ᵥ u with hw
    set w' : Fin n → K := fun k => τ (w k) with hw'
    have hw'e : xm *ᵥ w' = τ (lam * ν) • w' := eigen_of_semilinear hττ hrel hMMi hMiM hu
    have hne' : ν ≠ τ (lam * ν) := by
      intro hh
      rw [map_mul, tau_apply_eq_inv h hq hτ hlam3, tau_apply_eq_inv h hq hτ hν3] at hh
      apply hνlam
      have e : lam * ν ^ 2 = 1 := by
        calc lam * ν ^ 2 = lam * ν * ν := by ring
          _ = lam * ν * (lam⁻¹ * ν⁻¹) := by rw [← hh]
          _ = 1 := by field_simp
      calc ν = 1 * ν := by ring
        _ = (lam * ν ^ 2) * ν := by rw [e]
        _ = lam * ν ^ 3 := by ring
        _ = lam := by rw [hν3, mul_one]
    have o1 : idForm h n u₁ w' = 0 := eigen_orth h hνb hne' h₁ hw'e
    have o2 : idForm h n u₂ w' = 0 := eigen_orth h hνb hne' h₂ hw'e
    have hyw' : torusMat h u₁ u₂ ω *ᵥ w' = w' := torusMat_apply_perp h ω o1 o2
    have hyτ : (torusMat h u₁ u₂ ω).map τ *ᵥ w = w := by
      rw [mulVec_map_tau τ hττ]
      funext k
      show τ ((torusMat h u₁ u₂ ω *ᵥ w') k) = w k
      rw [hyw']
      exact hττ (w k)
    rw [hy'm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hyτ, hw, Matrix.mulVec_mulVec, hMMi,
      Matrix.one_mulVec]
  have hy'unit : adj h ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := mem_primeFormUnitary_iff_adj.1 y'.2
  have hy'adj : ∀ u : Fin n → K, ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u →
      adj h ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u := by
    intro u hu
    calc adj h ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u
        = adj h ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) := by rw [hu]
      _ = (adj h ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((y' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ u := by
          rw [Matrix.mulVec_mulVec]
      _ = u := by rw [hy'unit, Matrix.one_mulVec]
  have hcommy : y' * y = y * y' := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hym]
    exact comm_torusMat_of_fix h ω (hfix _ h₁) (hfix _ h₂) (hy'adj _ (hfix _ h₁))
      (hy'adj _ (hfix _ h₂))
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hym, Subgroup.coe_one, Units.val_one,
      pow_succ, pow_succ, pow_one]
    exact torusMat_pow_three h hq hb ω
  have hy'3 : y' ^ 3 = 1 := by rw [hy', ← map_pow, hy3, map_one]
  have hz3 : (y' * y⁻¹) ^ 3 = 1 := by
    have hc : Commute y' y⁻¹ := (show Commute y' y from hcommy).inv_right
    rw [hc.mul_pow, hy'3, inv_pow, hy3, inv_one, one_mul]
  have hu₁0 : u₁ ≠ 0 := hb.ne_zero_left
  have hu₂0 : u₂ ≠ 0 := by
    rintro rfl
    have := hb.self₂
    simp at this
  have hzu₁ : ((y' * y⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K).val.mulVec u₁ =
      ((ω⁻¹ : Kˣ) : K) • u₁ := by
    have e1 : ((y⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K).val =
        torusMat h u₁ u₂ ((ω⁻¹ : Kˣ) : K) := rfl
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    erw [e1]
    rw [torus_apply_first h hb, Matrix.mulVec_smul, hfix u₁ h₁]
  have hzu₂ : ((y' * y⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K).val.mulVec u₂ =
      (ω : K) • u₂ := by
    have e1 : ((y⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K).val =
        torusMat h u₁ u₂ ((ω⁻¹ : Kˣ) : K) := rfl
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    erw [e1]
    rw [torus_apply_second h hb, Matrix.mulVec_smul]
    have : (((ω⁻¹ : Kˣ) : K))⁻¹ = (ω : K) := by simp
    rw [this, hfix u₂ h₂]
  have hρz : primeFormConjHom h (idGram K n) (y' * y⁻¹) ≠ 1 := by
    intro h1
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne _).1 h1
    have hzm : ((y' * y⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K).val =
        (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [hc, scalar_coe_eq_smul_one]
    rw [hzm, smul_one_mulVec] at hzu₁ hzu₂
    have hc1 : (c : K) = ((ω⁻¹ : Kˣ) : K) := smul_left_injective K hu₁0 hzu₁
    have hc2 : (c : K) = (ω : K) := smul_left_injective K hu₂0 hzu₂
    have hωω : (ω : K) * ω = 1 := by
      have e : (ω : K) = ((ω⁻¹ : Kˣ) : K) := hc2.symm.trans hc1
      calc (ω : K) * ω = (ω : K) * ((ω⁻¹ : Kˣ) : K) := by rw [← e]
        _ = 1 := by simp
    apply hω1
    apply Units.ext
    rw [Units.val_one]
    calc (ω : K) = ω * (ω * ω) := by rw [hωω, mul_one]
      _ = (ω : K) ^ 3 := by ring
      _ = 1 := hω3
  have hord : orderOf (primeFormConjHom h (idGram K n) (y' * y⁻¹)) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hz3, map_one]) hρz
  rw [hord] at hTT
  exact absurd hTT (by norm_num)

end NonFixed

section Basis

variable [DecidableEq K]

theorem det_eq_prod_of_eigenbasis {xm : Matrix (Fin n) (Fin n) K} {b : Fin n → Fin n → K}
    (hb : IsOrthonormalFamily h b) {cc : Fin n → K} (hbe : ∀ i, xm *ᵥ b i = cc i • b i) :
    xm.det = ∏ i, cc i := by
  have hBA := frameAdj_mul_frameMat hb
  have hAB : frameMat b * frameAdj h b = 1 := mul_eq_one_comm.1 hBA
  have h1 : xm * frameMat b = frameMat b * Matrix.diagonal cc := by
    ext k i
    rw [mul_frameMat_apply, hbe i]
    simp [frameMat, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  have h2 : xm = frameMat b * Matrix.diagonal cc * frameAdj h b := by
    calc xm = xm * (frameMat b * frameAdj h b) := by rw [hAB, Matrix.mul_one]
      _ = (xm * frameMat b) * frameAdj h b := by rw [Matrix.mul_assoc]
      _ = _ := by rw [h1]
  rw [h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  calc (frameMat b).det * (∏ i, cc i) * (frameAdj h b).det
      = (∏ i, cc i) * ((frameMat b * frameAdj h b).det) := by rw [Matrix.det_mul]; ring
    _ = ∏ i, cc i := by rw [hAB, Matrix.det_one, mul_one]

theorem span_range_orthonormal_basis {b : Fin n → Fin n → K} (hb : IsOrthonormalFamily h b) :
    Submodule.span K (Set.range b) = ⊤ :=
  span_eq_of_orthonormal hb (fun i => Submodule.mem_top) (by rw [finrank_top, Module.finrank_fin_fun])

theorem frameMat_mulVec_eq_sum (u : Fin m → Fin n → K) (a : Fin m → K) :
    frameMat u *ᵥ a = ∑ i, a i • u i := by
  funext k
  simp [Matrix.mulVec, dotProduct, frameMat, mul_comm]

theorem frameAdj_mulVec_apply (u : Fin m → Fin n → K) (v : Fin n → K) (i : Fin m) :
    (frameAdj h u *ᵥ v) i = idForm h n (u i) v := by
  rw [idForm_eq_dotProduct]
  rfl

theorem card_le_finrank_of_eigen {b : Fin n → Fin n → K} (hb : IsOrthonormalFamily h b)
    {cc : Fin n → K} {ν : K} (W : Submodule K (Fin n → K)) (hW : ∀ i, cc i = ν → b i ∈ W) :
    (Finset.univ.filter fun i => cc i = ν).card ≤ Module.finrank K W := by
  have hli : LinearIndependent K (fun i : {i // cc i = ν} => (⟨b i, hW i i.2⟩ : W)) := by
    apply LinearIndependent.of_comp W.subtype
    exact hb.linearIndependent.comp (fun i : {i // cc i = ν} => (i : Fin n)) Subtype.val_injective
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_subtype] at this

theorem finrank_ker_le_card (x : primeFormUnitary h (idGram K n)) {b : Fin n → Fin n → K}
    (hb : IsOrthonormalFamily h b) {cc : Fin n → K}
    (hbe : ∀ i, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = cc i • b i)
    (hcc : ∀ i, h.bar (cc i) * cc i = 1) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' ((x : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) - 1)) ≤ (Finset.univ.filter fun i => cc i = 1).card := by
  classical
  set S1 : Finset (Fin n) := Finset.univ.filter fun i => cc i = 1 with hS1
  have hle : LinearMap.ker (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) ≤
      Submodule.span K ((S1.image b : Finset (Fin n → K)) : Set (Fin n → K)) := by
    intro v hv
    have hv1 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = (1 : K) • v := by
      have := LinearMap.mem_ker.1 hv
      simpa [sub_eq_zero] using this
    have hexp := frame_expand hb (span_range_orthonormal_basis hb ▸ Submodule.mem_top (x := v))
    rw [frameMat_mulVec_eq_sum] at hexp
    have hzero : ∀ i ∉ S1, (frameAdj h b *ᵥ v) i • b i = 0 := by
      intro i hi
      have hci : cc i ≠ 1 := by simpa [hS1] using hi
      rw [frameAdj_mulVec_apply, eigen_orth h (hcc i) hci (hbe i) hv1, zero_smul]
    rw [← hexp, ← Finset.sum_subset (Finset.subset_univ S1) (fun i _ hi => hzero i hi)]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (by simpa using Finset.mem_image_of_mem b hi)
  exact (Submodule.finrank_mono hle).trans
    ((finrank_span_finset_le_card _).trans Finset.card_image_le)

end Basis

section Pattern

variable [DecidableEq K]

theorem outer_pattern (hn : 4 ≤ n) (hq : ℓ ^ f = 2)
    {D H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range ≤ H)
    {x : primeFormUnitary h (idGram K n)} (hx : x ^ 3 = 1)
    (hxD : primeFormConjHom h (idGram K n) x ∈ D) (hx1 : primeFormConjHom h (idGram K n) x ≠ 1)
    {M : primeFormUnitary h (idGram K n)} {τ : K ≃+* K} (hτ : τ ≠ RingEquiv.refl K)
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ ∈
      localDeltaIn 3 H D) :
    n ≤ 5 ∧ (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 →
      Module.finrank K (LinearMap.ker (Matrix.toLin' ((x : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1)) = n - 2) := by
  classical
  have hfin := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hK4 : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, h.card, pow_mul', hq]
    norm_num
  have hcomm := commute_of_mem_localDeltaIn hg hxD
  obtain ⟨c, hc, hrel⟩ := exists_semilinear_scalar hn3 hne hcomm
  have hlam3 : ((c : Kˣ) : K) ^ 3 = 1 := by
    have : c ^ 3 = 1 := by rwa [hq] at hc
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hlam0 : ((c : Kˣ) : K) ≠ 0 := c.ne_zero
  obtain ⟨b, cc, hb, hbe⟩ := exists_eigenbasis hq hx
  have hb0 : ∀ i, b i ≠ 0 := fun i hi => by
    have := hb i i
    rw [hi] at this
    simp at this
  have hcc3 : ∀ i, cc i ^ 3 = 1 := fun i => eigenvalue_pow_eq_one hx (hb0 i) (hbe i)
  have hcc0 : ∀ i, cc i ≠ 0 := fun i hi => by
    have := hcc3 i
    rw [hi] at this
    norm_num at this
  have hccb : ∀ i, h.bar (cc i) * cc i = 1 := fun i => bar_eq_inv_of_pow_eq_one h hpq (hcc3 i)
  have h1 : ∀ ν : K, ν ≠ 0 → ν ≠ (c : K) → (Finset.univ.filter fun i => cc i = ν).card ≤ 1 := by
    intro ν hν0 hνl
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    have hci : cc i = ν := (Finset.mem_filter.1 hi).2
    have hcj : cc j = ν := (Finset.mem_filter.1 hj).2
    exact torus_contradiction hn hq hH hxD hx1 hτ hg hlam3 hrel (pow_three_eq_one h hq hν0) hνl
      (hb.pair hij) (by rw [hbe i, hci]) (by rw [hbe j, hcj])
  have h3 : (Finset.univ.filter fun i => cc i = (c : K)).card ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have hmem : ∀ i, cc i = (c : K) → b i ∈ primaryComponent
        ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
        (X - C (c : K)) := fun i hi => by
      rw [mem_primaryComponent_X_sub_C]
      show ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = _
      rw [hbe i, hi]
    have hdim := (card_le_finrank_of_eigen hb _ hmem)
    exact hτ (good_eigen_tau (ν := (c : K)) hn3 hne hq hx (by omega) hH hg hxD hx1)
  obtain ⟨hn5, hpat⟩ := comb_pattern hK4 cc hcc0 hlam0 h1 h3
  refine ⟨hn5, fun hdet => ?_⟩
  have h3n : ¬ 3 ∣ n := by omega
  have hdetM : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (M : GL (Fin n) K).isUnit).ne_zero
  have hlamn : ((c : Kˣ) : K) ^ n = 1 := by
    have h1 := congrArg Matrix.det hrel
    have h2 : (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ).det = 1 := by
      rw [show ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
        (τ : K →+* K).mapMatrix ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) from rfl,
        ← RingHom.map_det, hdet, map_one]
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hdet, h2, Fintype.card_fin] at h1
    have h3 : (((c : Kˣ) : K) ^ n - 1) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 0 := by
      linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hdetM)
  have hlam1 : ((c : Kˣ) : K) = 1 := by
    have := pow_gcd_eq_one.2 ⟨hlam3, hlamn⟩
    have hcop : Nat.gcd 3 n = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3n
    rwa [hcop, pow_one] at this
  have hprod : ∏ i, cc i = 1 := by
    rw [← det_eq_prod_of_eigenbasis hb hbe]
    exact hdet
  have hcard := hpat hn hlam1 hprod
  apply le_antisymm
  · exact (finrank_ker_le_card x hb hbe hccb).trans hcard.le
  · rw [← hcard]
    refine card_le_finrank_of_eigen hb _ (fun i hi => ?_)
    rw [LinearMap.mem_ker]
    simp [Matrix.toLin'_apply, hbe i, hi]

end Pattern

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
