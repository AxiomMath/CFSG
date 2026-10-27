module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.LinearAlgebra.PID
public import Mathlib.RingTheory.Trace.Basic

public section

open Module Polynomial Matrix

namespace CFSG.Fischer.Classification.SRG

theorem trace_eq_finrank_nsmul_trace {K F M : Type*} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]
    [FiniteDimensional F M] (x : F) (T : M →ₗ[K] M) (hT : ∀ m, T m = x • m) :
    LinearMap.trace K M T = finrank F M • Algebra.trace K F x := by
  classical
  let b := Module.finBasis K F
  let c := Module.finBasis F M
  rw [LinearMap.trace_eq_matrix_trace K (b.smulTower c), Algebra.trace_eq_matrix_trace b,
    Matrix.trace, Matrix.trace, Fintype.sum_prod_type_right]
  have h : ∀ i j, (LinearMap.toMatrix (b.smulTower c) (b.smulTower c) T).diag (i, j) =
      (Algebra.leftMulMatrix b x).diag i := by
    intro i j
    simp only [Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, hT,
      Module.Basis.smulTower_repr_mk, Algebra.leftMulMatrix_eq_repr_mul, smul_smul, map_smul,
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem even_finrank_and_two_mul_trace {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (T : M →ₗ[K] M) (a c : K) (hT : ∀ m, T (T m) = a • T m + c • m)
    (hroot : ∀ r : K, r * r ≠ a * r + c) :
    Even (finrank K M) ∧ 2 * LinearMap.trace K M T = finrank K M * a := by
  classical
  set p : K[X] := X ^ 2 - C a * X - C c with hp
  have hdeg : p.natDegree = 2 := by rw [hp]; compute_degree!
  have hmonic : p.Monic := by rw [hp]; monicity!
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have hirr : Irreducible p := Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hdeg]; decide) fun r hr => hroot r (by
      simp only [hp, IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at hr
      linear_combination hr)
  have : Fact (Irreducible p) := ⟨hirr⟩
  have hpT : aeval T p = 0 := by
    ext m
    simp [hp, sq, hT]
  let φ : AdjoinRoot p →ₐ[K] Module.End K M := Ideal.Quotient.liftₐ (Ideal.span {p}) (aeval T)
    fun q hq => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hq
      rw [map_mul, hpT, mul_zero]
  let _ : Module (AdjoinRoot p) M := Module.compHom M φ.toRingHom
  have : IsScalarTower K (AdjoinRoot p) M := ⟨fun r x m => by
    show φ (r • x) m = r • φ x m
    rw [map_smul]; rfl⟩
  have : FiniteDimensional (AdjoinRoot p) M := Module.Finite.of_restrictScalars_finite K _ M
  have : FiniteDimensional K (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  have h2 : finrank K (AdjoinRoot p) = 2 := by
    rw [(AdjoinRoot.powerBasis hp0).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hdim := Module.finrank_mul_finrank K (AdjoinRoot p) M
  rw [h2] at hdim
  have hφ : φ (AdjoinRoot.root p) = T := aeval_X T
  have htr := trace_eq_finrank_nsmul_trace (AdjoinRoot.root p) T (fun m => by
    show T m = φ (AdjoinRoot.root p) m
    rw [hφ])
  have hroot_tr : Algebra.trace K (AdjoinRoot p) (AdjoinRoot.root p) = a := by
    rw [← AdjoinRoot.powerBasis_gen hp0, PowerBasis.trace_gen_eq_nextCoeff_minpoly,
      AdjoinRoot.powerBasis_gen hp0, AdjoinRoot.minpoly_root hp0, hmonic.leadingCoeff, inv_one,
      C_1, mul_one, nextCoeff_of_natDegree_pos (by rw [hdeg]; norm_num), hdeg]
    simp [hp, coeff_C]
  refine ⟨⟨finrank (AdjoinRoot p) M, by omega⟩, ?_⟩
  rw [htr, hroot_tr, ← hdim]
  push_cast
  ring

theorem exists_add_eq_finrank_and_trace {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (T : M →ₗ[K] M) (r s : K) (hrs : r ≠ s)
    (hT : ∀ m, T (T m) = (r + s) • T m - (r * s) • m) :
    ∃ f g : ℕ, f + g = finrank K M ∧ LinearMap.trace K M T = f * r + g * s := by
  set Q : M →ₗ[K] M := T - s • LinearMap.id with hQ
  have hQQ : Q * Q = (r - s) • Q := by
    ext m
    simp only [hQ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul, hT]
    module
  set P : M →ₗ[K] M := (r - s)⁻¹ • Q with hP
  have hrs' : r - s ≠ 0 := sub_ne_zero.2 hrs
  have hPP : IsIdempotentElem P := by
    rw [IsIdempotentElem, hP, smul_mul_smul_comm, hQQ, smul_smul, mul_assoc, inv_mul_cancel₀ hrs',
      mul_one]
  have htr := (LinearMap.IsIdempotentElem.isProj_range P hPP).trace
  have hf : finrank K (LinearMap.range P) ≤ finrank K M := Submodule.finrank_le _
  refine ⟨finrank K (LinearMap.range P), finrank K M - finrank K (LinearMap.range P), by omega, ?_⟩
  have hTP : T = s • LinearMap.id + (r - s) • P := by
    rw [hP, smul_smul, mul_inv_cancel₀ hrs', one_smul, hQ]
    abel
  rw [hTP, map_add, map_smul, map_smul, LinearMap.trace_id, htr, Nat.cast_sub hf]
  simp only [smul_eq_mul]
  ring

end CFSG.Fischer.Classification.SRG

namespace SimpleGraph

open CFSG.Fischer.Classification.SRG

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {n k ℓ μ : ℕ}

theorem IsSRGWith.exists_restrict_sumZero (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    ∃ (W : Submodule ℚ (V → ℚ)) (T : W →ₗ[ℚ] W), finrank ℚ W = n - 1 ∧
      LinearMap.trace ℚ W T = -k ∧ ∀ u, T (T u) = ((ℓ : ℚ) - μ) • T u + ((k : ℚ) - μ) • u := by
  classical
  set A := G.adjMatrix ℚ with hA
  set J : Matrix V V ℚ := of fun _ _ => 1 with hJ
  have hA2 : A * A = ((k : ℚ) - μ) • (1 : Matrix V V ℚ) + ((ℓ : ℚ) - μ) • A + (μ : ℚ) • J := by
    have h1 := h.matrix_eq (α := ℚ)
    have h2 := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℚ
    rw [compl_adjMatrix_eq_adjMatrix_compl] at h2
    have hC : Gᶜ.adjMatrix ℚ = J - 1 - A := by
      rw [show J = of 1 from rfl, ← h2]; abel
    rw [← sq, h1, hC]
    simp only [← Nat.cast_smul_eq_nsmul ℚ]
    module
  have hAsum : ∀ u : V → ℚ, ∑ v, (A *ᵥ u) v = k * ∑ v, u v := by
    intro u
    rw [← one_dotProduct, dotProduct_mulVec, ← one_dotProduct]
    have : (1 : V → ℚ) ᵥ* A = (k : ℚ) • 1 := by
      ext w
      simp [hA, h.regular w]
    rw [this, smul_dotProduct, smul_eq_mul]
  have hJu : ∀ u : V → ℚ, J *ᵥ u = fun _ => ∑ v, u v := by
    intro u; ext w; simp [hJ, mulVec, dotProduct]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  let σ : (V → ℚ) →ₗ[ℚ] ℚ := ∑ v, LinearMap.proj v
  have hσ : ∀ u, σ u = ∑ v, u v := fun u => by simp [σ]
  let W := LinearMap.ker σ
  have hmemW : ∀ u, u ∈ W ↔ ∑ v, u v = 0 := fun u => by rw [LinearMap.mem_ker, hσ]
  have hW : finrank ℚ W = n - 1 := by
    have h1 : finrank ℚ (LinearMap.range σ) + finrank ℚ W = finrank ℚ (V → ℚ) :=
      LinearMap.finrank_range_add_finrank_ker σ
    obtain ⟨v₀⟩ : Nonempty V := by rw [← Fintype.card_pos_iff, h.card]; exact hn
    have hsurj : LinearMap.range σ = ⊤ :=
      LinearMap.range_eq_top.2 fun t => ⟨Pi.single v₀ t, by simp [hσ]⟩
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card, h.card] at h1
    omega
  set B : Matrix V V ℚ := A - ((k : ℚ) / n) • J with hB
  have hBW : ∀ u, Matrix.toLin' B u ∈ W := by
    intro u
    rw [hmemW, Matrix.toLin'_apply, hB, sub_mulVec, smul_mulVec, hJu]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, hAsum,
      Finset.sum_const, Finset.card_univ, h.card, nsmul_eq_mul]
    field_simp
    ring
  have hBA : ∀ u ∈ W, B *ᵥ u = A *ᵥ u := by
    intro u hu
    rw [hB, sub_mulVec, smul_mulVec, hJu, (hmemW u).1 hu]
    ext v; simp
  let T : W →ₗ[ℚ] W := (Matrix.toLin' B).restrict fun u _ => hBW u
  have hTv : ∀ u : W, (T u : V → ℚ) = A *ᵥ u := fun u => hBA u u.2
  refine ⟨W, T, hW, ?_, fun u => ?_⟩
  · rw [LinearMap.trace_restrict_eq_of_forall_mem W _ hBW, Matrix.trace_toLin'_eq, hB,
      trace_sub, trace_smul, hA, trace_adjMatrix]
    simp [hJ, Matrix.trace, h.card]
    field_simp
  · apply Subtype.ext
    rw [hTv, hTv, mulVec_mulVec, hA2]
    simp only [add_mulVec, smul_mulVec, one_mulVec, hJu, (hmemW u).1 u.2]
    simp only [Submodule.coe_add, Submodule.coe_smul, hTv]
    ext v; simp; ring

theorem IsSRGWith.conference_of_not_isSquare (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n)
    (hsq : ¬ IsSquare (((ℓ : ℤ) - μ) ^ 2 + 4 * ((k : ℤ) - μ))) :
    Even (n - 1) ∧ 2 * (k : ℤ) + ((n : ℤ) - 1) * ((ℓ : ℤ) - μ) = 0 := by
  obtain ⟨W, T, hW, htr, hT⟩ := h.exists_restrict_sumZero hn
  have hroot : ∀ r : ℚ, r * r ≠ ((ℓ : ℚ) - μ) * r + ((k : ℚ) - μ) := by
    intro r hr
    apply hsq
    rw [← Rat.isSquare_intCast_iff]
    refine ⟨2 * r - ((ℓ : ℚ) - μ), ?_⟩
    push_cast
    linear_combination -4 * hr
  obtain ⟨heven, h2⟩ := even_finrank_and_two_mul_trace T _ _ hT hroot
  rw [hW] at heven h2
  rw [htr, Nat.cast_sub hn, Nat.cast_one] at h2
  refine ⟨heven, ?_⟩
  have : (2 * (k : ℤ) + ((n : ℤ) - 1) * ((ℓ : ℤ) - μ) : ℚ) = 0 := by
    push_cast
    linear_combination -h2
  exact_mod_cast this

theorem IsSRGWith.exists_multiplicities_of_roots (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n)
    {r s : ℤ} (hrs : r ≠ s) (hsum : r + s = (ℓ : ℤ) - μ) (hprod : r * s = (μ : ℤ) - k) :
    ∃ f g : ℕ, f + g = n - 1 ∧ (k : ℤ) + f * r + g * s = 0 := by
  obtain ⟨W, T, hW, htr, hT⟩ := h.exists_restrict_sumZero hn
  have hsum' : ((r : ℚ) + s) = (ℓ : ℚ) - μ := by exact_mod_cast hsum
  have hprod' : ((r : ℚ) * s) = (μ : ℚ) - k := by exact_mod_cast hprod
  obtain ⟨f, g, hfg, htr'⟩ := exists_add_eq_finrank_and_trace T r s (by exact_mod_cast hrs)
    fun u => by rw [hT, hsum', hprod']; module
  refine ⟨f, g, hW ▸ hfg, ?_⟩
  rw [htr] at htr'
  have : ((k : ℤ) + f * r + g * s : ℚ) = 0 := by
    push_cast
    linear_combination -htr'
  exact_mod_cast this

end SimpleGraph
