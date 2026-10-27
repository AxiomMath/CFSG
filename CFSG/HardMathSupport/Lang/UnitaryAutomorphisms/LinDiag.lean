module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinNil
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinGlue
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.DiagCube

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

open Module Module.End in
theorem exists_eigenbasis_of_pow_three {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (A : Matrix (Fin n) (Fin n) K) (hA : A ^ 3 = 1) :
    ∃ (b : Basis (Fin n) K (Fin n → K)) (μ : Fin n → K),
      (∀ j, A *ᵥ b j = μ j • b j) ∧ ∀ j, μ j ^ 3 = 1 := by
  classical
  set g : End K (Fin n → K) := Matrix.toLin' A with hg
  have hg3 : g ^ 3 = 1 := by
    have := congrArg (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)) hA
    rw [map_pow, map_one] at this
    exact this
  have hss := CFSG.RankThree.PartOne.isSemisimple_of_pow_eq_one hζ hg3
  have htop : ⨆ μ, g.eigenspace μ = ⊤ :=
    CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hζ hg3
  have hint : DirectSum.IsInternal (fun μ => g.eigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top g.eigenspaces_iSupIndep htop
  let e : ∀ μ : K, Basis (Fin (finrank K (g.eigenspace μ))) K (g.eigenspace μ) :=
    fun μ => Module.finBasis K (g.eigenspace μ)
  let b₀ := hint.collectedBasis e
  have : Finite (Σ μ : K, Fin (finrank K (g.eigenspace μ))) := Module.Finite.finite_basis b₀
  let e₀ : (Σ μ : K, Fin (finrank K (g.eigenspace μ))) ≃ Fin n :=
    (Finite.equivFin _).trans (finCongr ((finrank_eq_nat_card_basis b₀).symm.trans
      (by simp)))
  have hmem : ∀ j, b₀ (e₀.symm j) ∈ g.eigenspace (e₀.symm j).1 :=
    fun j => hint.collectedBasis_mem e (e₀.symm j)
  refine ⟨b₀.reindex e₀, fun j => (e₀.symm j).1, fun j => ?_, fun j => ?_⟩
  · rw [Basis.reindex_apply]
    have := mem_eigenspace_iff.mp (hmem j)
    simpa [hg] using this
  · show (e₀.symm j).1 ^ 3 = 1
    have hne : b₀ (e₀.symm j) ≠ 0 := b₀.ne_zero _
    have hev : g.HasEigenvector (e₀.symm j).1 (b₀ (e₀.symm j)) := ⟨hmem j, hne⟩
    have h1 := hev.pow_apply 3
    rw [hg3, Module.End.one_apply] at h1
    have h2 : ((e₀.symm j).1 ^ 3 - 1) • b₀ (e₀.symm j) = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hne)

@[expose] noncomputable def coordVec (b : Module.Basis (Fin n) K (Fin n → K)) (j : Fin n) : Fin n → K :=
  fun k => b.coord j (Pi.single k 1)

theorem coordVec_dotProduct (b : Module.Basis (Fin n) K (Fin n → K)) (j : Fin n) (v : Fin n → K) :
    coordVec b j ⬝ᵥ v = b.coord j v := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin n → K) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, coordVec, mul_comm]

theorem coord_mulVec_of_eigen (b : Module.Basis (Fin n) K (Fin n → K)) (μ : Fin n → K)
    (A : Matrix (Fin n) (Fin n) K) (hb : ∀ j, A *ᵥ b j = μ j • b j) (j : Fin n)
    (v : Fin n → K) : b.coord j (A *ᵥ v) = μ j * b.coord j v := by
  have : (b.coord j).comp (Matrix.mulVecLin A) = μ j • b.coord j := by
    apply b.ext
    intro i
    by_cases h : i = j
    · subst h
      simp [hb]
    · simp [hb, Module.Basis.coord_apply, Ne.symm h]
  exact congrArg (fun F => F v) this

theorem vecMulVec_comm_of_eigen (A : Matrix (Fin n) (Fin n) K) (u ψ : Fin n → K) (s : K)
    (hu : A *ᵥ u = s • u) (hψ : ψ ᵥ* A = s • ψ) (a : K) :
    A * rk1 u ψ a = rk1 u ψ a * A := by
  rw [rk1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hu, hψ, Matrix.smul_vecMulVec,
    Matrix.vecMulVec_smul]

theorem exists_primitiveRoot_three [Finite K] {q : ℕ} (hK : Nat.card K = q) (h3 : 3 ∣ q - 1) :
    ∃ ω : K, IsPrimitiveRoot ω 3 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
    exact h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  have hprim : IsPrimitiveRoot x 3 := hx ▸ IsPrimitiveRoot.orderOf x
  refine ⟨(x : K), ?_⟩
  have := IsPrimitiveRoot.map_of_injective (f := Units.coeHom K) hprim Units.val_injective
  exact this

theorem hasFixedThreePair_conjAut_of_pow_three {ℓ f : ℕ} [Finite K] [hℓ : Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (h3 : 3 ∣ Nat.card K - 1) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (hA : A ^ 3 = 1)
    (hdet : n = 3 → ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 1) :
    HasFixedThreePair (conjAut n K A) := by
  classical
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_three (K := K) rfl h3
  have hA3 : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hA, Units.val_one]
  obtain ⟨b, μ, hb, hμ⟩ := exists_eigenbasis_of_pow_three hω _ hA3
  have hdet' : n = 3 → ∏ k, μ k ≠ 1 := by
    intro hn3 hprod
    apply hdet hn3
    have hmat : LinearMap.toMatrix b b (Matrix.toLin' ((A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) = Matrix.diagonal μ := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb, map_smul]
      by_cases h : r = c
      · subst h; simp [Module.Basis.repr_self]
      · simp [Module.Basis.repr_self, h]
    have := LinearMap.det_toMatrix b (Matrix.toLin' ((A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))
    rw [hmat, Matrix.det_diagonal, LinearMap.det_toLin'] at this
    rw [← this, hprod]
  obtain ⟨i, j, hij, hμij⟩ := exists_ne_eq_of_pow_three hn μ hμ hdet'
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    rw [hK] at h3
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h2 := Nat.dvd_sub h1 h3
    have hp := Nat.one_le_pow f 3 (by norm_num)
    have e : 3 ^ f - (3 ^ f - 1) = 1 := by omega
    rw [e] at h2
    omega
  have h3K : (3 : K) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K ℓ] at this
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_three).1 this)
  set Am : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hψ : ∀ k, coordVec b k ᵥ* Am = μ k • coordVec b k := by
    intro k
    ext c
    rw [← dotProduct_single_one (coordVec b k ᵥ* Am) c, ← Matrix.dotProduct_mulVec,
      coordVec_dotProduct, coord_mulVec_of_eigen b μ Am hb, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc : ∀ k l, coordVec b k ⬝ᵥ b l = if k = l then 1 else 0 := by
    intro k l
    rw [coordVec_dotProduct]
    by_cases h : k = l
    · subst h; simp [Module.Basis.coord_apply]
    · simp [Module.Basis.coord_apply, h]
  have h1 : coordVec b j ⬝ᵥ b i = 0 := by rw [hc]; simp [hij.symm]
  have h2 : coordVec b i ⬝ᵥ b j = 0 := by rw [hc]; simp [hij]
  have h3' : coordVec b j ⬝ᵥ b j = 1 := by rw [hc]; simp
  have h4 : coordVec b i ⬝ᵥ b i = 1 := by rw [hc]; simp
  have hab : (1 : K) * (-3) = -3 := one_mul _
  refine hasFixedThreePair_of_sl_pair (conjAut n K A) (rk1SL h1 1) (rk1SL h2 (-3)) ℓ hℓ.out hℓ3
    ?_ ?_ ?_ ?_ ?_ ?_
  · refine fixed_conjAut_of_commute A _ ?_
    rw [coe_rk1SL]
    refine vecMulVec_comm_of_eigen Am _ _ (μ i) (hb i) ?_ 1
    rw [hψ, hμij]
  · refine fixed_conjAut_of_commute A _ ?_
    rw [coe_rk1SL]
    refine vecMulVec_comm_of_eigen Am _ _ (μ i) (by rw [hb, hμij]) (hψ i) (-3)
  · exact Subtype.ext (rk1_pow_char h1 1 ℓ)
  · exact Subtype.ext (rk1_pow_char h2 (-3) ℓ)
  · refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, coe_rk1SL,
      coe_rk1SL]
    exact rk1_pair_cube h1 h2 h3' h4 hab
  · intro s
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rk1SL, coe_rk1SL]
    exact rk1_pair_not_scalar h1 h2 h3' h4 hab h3K hn s

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
