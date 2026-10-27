module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Fixed

theorem exists_fixed_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : MulAut G) (hφ : φ ^ p = 1) (hdvd : p ∣ Nat.card G) :
    ∃ g : G, orderOf g = p ∧ φ g = g := by
  classical
  have := Fintype.ofFinite G
  let σ : Equiv.Perm G := MulAut.toPerm G φ
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    have : σ ^ p = MulAut.toPerm G (φ ^ p) := (map_pow (MulAut.toPerm G) φ p).symm
    rw [this, hφ, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  let H : Subgroup G := MonoidHom.eqLocus (φ : G →* G) (MonoidHom.id G)
  have hHcard : Nat.card H = (Equiv.Perm.support σ)ᶜ.card := by
    rw [Nat.card_eq_fintype_card]
    refine (Fintype.card_congr ?_).trans (Fintype.card_coe _)
    refine Equiv.subtypeEquivRight fun g => ?_
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    exact Iff.rfl
  have hdvdH : p ∣ Nat.card H := by
    have h1 : Nat.card H ≡ Nat.card G [MOD p] := by
      rw [hHcard, Nat.card_eq_fintype_card]
      exact hmod
    exact (Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2 hdvd)))
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdvdH
  refine ⟨(g : G), ?_, g.2⟩
  rw [← hg]
  exact Subgroup.orderOf_coe g

end Fixed

section Blocks

variable {ℓ f : ℕ} {K : Type} [Field K] {e r n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isPrimeFormGram_one' {n : ℕ} : IsPrimeFormGram (1 : GL (Fin n) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem blkMat_barTranspose_mul (hU : UnitaryFieldData ℓ f K) (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n)
    (X : ι → Matrix (Fin e) (Fin e) K) (hX : ∀ t, ((X t).map hU.bar)ᵀ * X t = 1) :
    ((blkMat σ X).map hU.bar)ᵀ * blkMat σ X = 1 := by
  have h1 : ((blkMat σ X).map hU.bar)ᵀ = blkMat σ (fun t => ((X t).map hU.bar)ᵀ) := by
    rw [blkMat_apply, blkMat_apply, reindex_apply, reindex_apply]
    change ((fromBlocks (blockDiagonal X) 0 0 1).map hU.bar)ᵀ.submatrix σ.symm σ.symm = _
    congr 1
    rw [fromBlocks_map, fromBlocks_transpose, blockDiagonal_map _ _ (map_zero _),
      blockDiagonal_transpose]
    simp
  rw [h1, ← map_mul]
  have h2 : (fun t => ((X t).map hU.bar)ᵀ) * X = 1 := by
    funext t
    exact hX t
  rw [h2, map_one]

@[expose] noncomputable def blkGL (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    (ι → GL (Fin e) K) →* GL (Fin n) K :=
  (Units.map (blkMat (F := K) σ)).comp
    (MulEquiv.piUnits (M := fun _ : ι => Matrix (Fin e) (Fin e) K)).symm.toMonoidHom

theorem coe_blkGL (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) (h : ι → GL (Fin e) K) :
    ((blkGL σ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blkMat σ (fun t => (h t : Matrix (Fin e) (Fin e) K)) := rfl

theorem blkGL_injective (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    Function.Injective (blkGL (K := K) σ) := by
  intro h k hhk
  have h1 := blkMat_injective σ
    (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hhk)
  funext t
  exact Units.ext (congrFun h1 t)

theorem blkGL_mem_gramSU (hU : UnitaryFieldData ℓ f K) (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n)
    (h : ι → GL (Fin e) K) (hh : ∀ t, h t ∈ gramSU hU (1 : Matrix (Fin e) (Fin e) K)) :
    blkGL σ h ∈ gramSU hU (1 : Matrix (Fin n) (Fin n) K) := by
  have h' := fun t => mem_gramSU.1 (hh t)
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Matrix.mul_one, coe_blkGL]
    refine blkMat_barTranspose_mul hU σ _ fun t => ?_
    have := (h' t).1
    rwa [Matrix.mul_one] at this
  · rw [coe_blkGL, det_blkMat]
    exact Finset.prod_eq_one fun t _ => (h' t).2

@[expose] noncomputable def blkSU (hU : UnitaryFieldData ℓ f K)
    (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    (ι → gramSU hU (1 : Matrix (Fin e) (Fin e) K)) →*
      gramSU hU (1 : Matrix (Fin n) (Fin n) K) :=
  ((blkGL σ).comp (MonoidHom.compLeft (gramSU hU (1 : Matrix (Fin e) (Fin e) K)).subtype ι)).codRestrict
    (gramSU hU (1 : Matrix (Fin n) (Fin n) K)) fun h => blkGL_mem_gramSU hU σ _ fun t => (h t).2

theorem blkSU_injective (hU : UnitaryFieldData ℓ f K) (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n) :
    Function.Injective (blkSU hU σ) := by
  intro h k hhk
  have h1 := blkGL_injective σ (congrArg Subtype.val hhk)
  funext t
  exact Subtype.ext (congrFun h1 t)

theorem coe_blkSU (hU : UnitaryFieldData ℓ f K) (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n)
    (h : ι → gramSU hU (1 : Matrix (Fin e) (Fin e) K)) :
    ((blkSU hU σ h : gramSU hU (1 : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
      blkGL σ (fun t => ((h t : gramSU hU (1 : Matrix (Fin e) (Fin e) K)) : GL (Fin e) K)) :=
  rfl

end Blocks

section TwoIndep

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem coe_primeFormFieldSU (hU : UnitaryFieldData ℓ f K) {n : ℕ} {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (φ : K ≃+* K) (y : gramSU hU (C : Matrix (Fin n) (Fin n) K)) :
    ((primeFormFieldSU hU hC φ y : gramSU hU (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
      glAut φ (y : GL (Fin n) K) := rfl

@[expose] noncomputable def fldSU (hU : UnitaryFieldData ℓ f K) {n : ℕ} {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) :
    (K ≃+* K) →* MulAut (gramSU hU (C : Matrix (Fin n) (Fin n) K)) where
  toFun := primeFormFieldSU hU hC
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    change glAut 1 (g : GL (Fin n) K) = g
    rw [map_one]
    rfl)
  map_mul' φ ψ := MulEquiv.ext fun g => Subtype.ext (by
    change glAut (φ * ψ) (g : GL (Fin n) K) = glAut φ (glAut ψ (g : GL (Fin n) K))
    rw [map_mul]
    rfl)

theorem eq_one_of_mem_normOneScalars_of_pow_eq_one (hU : UnitaryFieldData ℓ f K) {n p : ℕ}
    (hp : p.Prime) (hp1 : ¬ p ∣ ℓ ^ f + 1) (hn : 0 < n)
    {y : gramSU hU (1 : Matrix (Fin n) (Fin n) K)}
    (hy : y ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin n) (Fin n) K)) n)
    (hyp : y ^ p = 1) : y = 1 := by
  obtain ⟨c, hcN, -, hyc⟩ := hy
  have hcp : c ^ p = 1 := by
    have h1 : ((y : GL (Fin n) K)) ^ p = 1 := by
      have := congrArg Subtype.val hyp
      simpa using this
    rw [hyc, ← map_pow] at h1
    have h2 := congrArg
      (fun g : GL (Fin n) K => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext h2
  have hcq : c ^ (ℓ ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, mul_comm, ← hU.bar_apply]
    exact hcN
  have hcop : Nat.Coprime p (ℓ ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 hp1
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hcp, hcq⟩
    rwa [hcop, pow_one] at this
  apply Subtype.ext
  rw [hyc, hc1, map_one]
  rfl

theorem exists_two_indep_fixed_unitary (hU : UnitaryFieldData ℓ f K) {p e n : ℕ} (hp : p.Prime)
    (hp1 : ¬ p ∣ ℓ ^ f + 1) (hdvd : p ∣ Nat.card (gramSU hU (1 : Matrix (Fin e) (Fin e) K)))
    (hn : 2 * e ≤ n) (hn0 : 0 < n) (τ : K ≃+* K) (hτ : τ ^ p = 1) :
    ∃ x₁ x₂ : primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      primeFormFieldHom hU (isPrimeFormGram_one' (n := n)) τ x₁ = x₁ ∧
      primeFormFieldHom hU (isPrimeFormGram_one' (n := n)) τ x₂ = x₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := hU.finite
  have hfin : Finite (gramSU hU (1 : Matrix (Fin e) (Fin e) K)) := inferInstance
  obtain ⟨g, hg, hgτ⟩ := exists_fixed_orderOf_eq_prime
    (fldSU hU (isPrimeFormGram_one' (n := e)) τ)
    (by rw [← map_pow, hτ, map_one]) hdvd
  let σ₂ : (Fin e × Fin 2) ⊕ Fin (n - 2 * e) ≃ Fin n :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  let π := QuotientGroup.mk'
    (normOneScalars hU (gramSU hU (1 : Matrix (Fin n) (Fin n) K)) n)
  have hker : ∀ y : gramSU hU (1 : Matrix (Fin n) (Fin n) K), π y = 1 → y ^ p = 1 → y = 1 :=
    fun y hy hyp => eq_one_of_mem_normOneScalars_of_pow_eq_one hU hp hp1 hn0
      ((QuotientGroup.eq_one_iff y).1 hy) hyp
  obtain ⟨hc, h0, h1, hi⟩ := two_indep_of_blockHom (blkSU hU σ₂) (blkSU_injective hU σ₂) π hg hker
  have hgmat : ((g : GL (Fin e) K) : Matrix (Fin e) (Fin e) K).map τ =
      ((g : GL (Fin e) K) : Matrix (Fin e) (Fin e) K) := by
    have := congrArg (fun x : gramSU hU (1 : Matrix (Fin e) (Fin e) K) =>
      ((x : GL (Fin e) K) : Matrix (Fin e) (Fin e) K)) hgτ
    exact this
  have hfix : ∀ t : Fin 2, primeFormFieldSU hU (isPrimeFormGram_one' (n := n)) τ
      (blkSU hU σ₂ (Pi.mulSingle t g)) = blkSU hU σ₂ (Pi.mulSingle t g) := by
    intro t
    apply Subtype.ext
    rw [coe_primeFormFieldSU, coe_blkSU]
    apply Units.ext
    rw [coe_glAut, coe_blkGL]
    refine (blkMat_map (τ : K →+* K) σ₂ _).trans ?_
    congr 1
    funext s
    by_cases hst : s = t
    · subst hst
      simp only [Pi.mulSingle_eq_same]
      exact hgmat
    · simp only [Pi.mulSingle_eq_of_ne hst]
      change (1 : Matrix (Fin e) (Fin e) K).map τ = 1
      exact Matrix.map_one _ (map_zero τ) (map_one τ)
  have hfld : ∀ t : Fin 2, primeFormFieldHom hU (isPrimeFormGram_one' (n := n)) τ
      (π (blkSU hU σ₂ (Pi.mulSingle t g))) = π (blkSU hU σ₂ (Pi.mulSingle t g)) := by
    intro t
    change primeFormFieldAut hU (isPrimeFormGram_one' (n := n)) τ
      ((blkSU hU σ₂ (Pi.mulSingle t g) : gramSU hU _ ) : primeFormP hU _) = _
    rw [primeFormFieldAut_mk, hfix t]
    rfl
  exact ⟨_, _, hc, h0, h1, hi, hfld 0, hfld 1⟩

end TwoIndep

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
