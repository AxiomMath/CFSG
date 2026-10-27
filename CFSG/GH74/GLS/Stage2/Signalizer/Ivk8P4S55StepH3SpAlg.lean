module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.RankThree.SubgroupLists.SymplecticReducible

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3Sp

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.RankThree.SubgroupLists CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def glElat (W : Submodule K (ι → K)) : Subgroup (GL ι K) where
  carrier := {g | (∀ v, ((g : Matrix ι ι K) - 1) *ᵥ v ∈ W) ∧
    ∀ w ∈ W, ((g : Matrix ι ι K) - 1) *ᵥ w = 0}
  one_mem' := by
    refine ⟨fun v => ?_, fun w _ => ?_⟩ <;> simp
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    have key : ∀ v, (((g * h : GL ι K) : Matrix ι ι K) - 1) *ᵥ v =
        ((g : Matrix ι ι K) - 1) *ᵥ v + ((h : Matrix ι ι K) - 1) *ᵥ v := by
      intro v
      have e : ((g * h : GL ι K) : Matrix ι ι K) - 1 =
          ((g : Matrix ι ι K) - 1) * ((h : Matrix ι ι K) - 1) + ((g : Matrix ι ι K) - 1) +
            ((h : Matrix ι ι K) - 1) := by
        rw [Units.val_mul]
        noncomm_ring
      rw [e, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hg2 _ (hh1 v),
        zero_add]
    exact ⟨fun v => by rw [key]; exact W.add_mem (hg1 v) (hh1 v),
      fun w hw => by rw [key, hg2 w hw, hh2 w hw, add_zero]⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    set M : Matrix ι ι K := ((g⁻¹ : GL ι K) : Matrix ι ι K) with hM
    have hMg : M * (g : Matrix ι ι K) = 1 := Units.inv_mul g
    have hgw : ∀ w ∈ W, (g : Matrix ι ι K) *ᵥ w = w := fun w hw => by
      have h := hg2 w hw
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    have hMw : ∀ w ∈ W, M *ᵥ w = w := fun w hw => by
      conv_lhs => rw [← hgw w hw]
      rw [Matrix.mulVec_mulVec, hMg, Matrix.one_mulVec]
    have key : ∀ v, (M - 1) *ᵥ v = -(((g : Matrix ι ι K) - 1) *ᵥ v) := by
      intro v
      have hv : (g : Matrix ι ι K) *ᵥ v - ((g : Matrix ι ι K) - 1) *ᵥ v = v := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      have h1 : M *ᵥ ((g : Matrix ι ι K) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, hMg, Matrix.one_mulVec]
      have h2 : M *ᵥ v = v - ((g : Matrix ι ι K) - 1) *ᵥ v := by
        have h3 : M *ᵥ ((g : Matrix ι ι K) *ᵥ v - ((g : Matrix ι ι K) - 1) *ᵥ v) =
            v - ((g : Matrix ι ι K) - 1) *ᵥ v := by
          rw [Matrix.mulVec_sub, h1, hMw _ (hg1 v)]
        rwa [hv] at h3
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h2]
      abel
    exact ⟨fun v => by rw [key]; exact W.neg_mem (hg1 v),
      fun w hw => by rw [key, hg2 w hw, neg_zero]⟩

theorem one_add_pow_of_mul_self {N : Matrix ι ι K} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : K) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_assoc, hN,
      smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]
    abel

theorem pow_char_eq_one_of_mem_glElat {r : ℕ} [CharP K r] {W : Submodule K (ι → K)}
    {g : GL ι K} (hg : g ∈ glElat W) : g ^ r = 1 := by
  set N : Matrix ι ι K := (g : Matrix ι ι K) - 1 with hN
  have hNN : N * N = 0 := by
    have h : ∀ v, (N * N) *ᵥ v = 0 := fun v => by
      rw [← Matrix.mulVec_mulVec]
      exact hg.2 _ (hg.1 v)
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, h, map_zero, LinearMap.zero_apply])
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have hg' : (g : Matrix ι ι K) = 1 + N := by rw [hN]; abel
  rw [hg', one_add_pow_of_mul_self hNN, CharP.cast_eq_zero, zero_smul, add_zero]

theorem isPGroup_glElat {r : ℕ} [CharP K r] (W : Submodule K (ι → K)) :
    IsPGroup r ↥(glElat W) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_char_eq_one_of_mem_glElat g.2

theorem conj_mem_glElat {W : Submodule K (ι → K)} {A : GL ι K}
    (hA : ∀ w ∈ W, (A : Matrix ι ι K) *ᵥ w ∈ W)
    (hA' : ∀ w ∈ W, ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W) {g : GL ι K}
    (hg : g ∈ glElat W) : A * g * A⁻¹ ∈ glElat W := by
  have e : ((A * g * A⁻¹ : GL ι K) : Matrix ι ι K) - 1 =
      (A : Matrix ι ι K) * ((g : Matrix ι ι K) - 1) * ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Units.mul_inv]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hA _ (hg.1 _)
  · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg.2 _ (hA' w hw), Matrix.mulVec_zero]

@[expose] def orbI (A : Matrix ι ι K) (u : ι → K) : Submodule K (ι → K) :=
  Submodule.span K (Set.range fun j : Fin 3 => (A ^ (j : ℕ)) *ᵥ u)

theorem mem_orbI_pow (A : Matrix ι ι K) (u : ι → K) (j : Fin 3) :
    (A ^ (j : ℕ)) *ᵥ u ∈ orbI A u :=
  Submodule.subset_span ⟨j, rfl⟩

theorem self_mem_orbI (A : Matrix ι ι K) (u : ι → K) : u ∈ orbI A u := by
  simpa using mem_orbI_pow A u 0

theorem mulVec_mem_orbI {A : Matrix ι ι K} {c : K} (hA : A ^ 3 = c • (1 : Matrix ι ι K))
    (u : ι → K) {w : ι → K} (hw : w ∈ orbI A u) : A *ᵥ w ∈ orbI A u := by
  refine Submodule.span_induction (p := fun w _ => A *ᵥ w ∈ orbI A u) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, rfl⟩
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    fin_cases j
    · exact mem_orbI_pow A u 1
    · exact mem_orbI_pow A u 2
    · change (A ^ 3) *ᵥ u ∈ orbI A u
      rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact (orbI A u).smul_mem c (self_mem_orbI A u)
  · rw [Matrix.mulVec_zero]
    exact (orbI A u).zero_mem
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]
    exact (orbI A u).add_mem hx hy
  · intro a x _ hx
    rw [Matrix.mulVec_smul]
    exact (orbI A u).smul_mem a hx

theorem inv_mulVec_mem_orbI {A : GL ι K} {c : K} (hc : c ≠ 0)
    (hA : (A : Matrix ι ι K) ^ 3 = c • (1 : Matrix ι ι K)) (u : ι → K) {w : ι → K}
    (hw : w ∈ orbI (A : Matrix ι ι K) u) :
    ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w ∈ orbI (A : Matrix ι ι K) u := by
  have hinv : ((A⁻¹ : GL ι K) : Matrix ι ι K) = c⁻¹ • (A : Matrix ι ι K) ^ 2 := by
    have h3 : (A : Matrix ι ι K) * (A : Matrix ι ι K) ^ 2 = (A : Matrix ι ι K) ^ 3 :=
      (pow_succ' (A : Matrix ι ι K) 2).symm
    have h1 : (A : Matrix ι ι K) * (c⁻¹ • (A : Matrix ι ι K) ^ 2) = 1 := by
      rw [Matrix.mul_smul, h3, hA, smul_smul, inv_mul_cancel₀ hc, one_smul]
    calc ((A⁻¹ : GL ι K) : Matrix ι ι K) =
        ((A⁻¹ : GL ι K) : Matrix ι ι K) *
          ((A : Matrix ι ι K) * (c⁻¹ • (A : Matrix ι ι K) ^ 2)) := by
          rw [h1, Matrix.mul_one]
      _ = c⁻¹ • (A : Matrix ι ι K) ^ 2 := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [hinv, Matrix.smul_mulVec, pow_two, ← Matrix.mulVec_mulVec]
  exact (orbI _ u).smul_mem _ (mulVec_mem_orbI hA u (mulVec_mem_orbI hA u hw))

variable {n : ℕ}

theorem spForm_gsp_mulVec (A : gsp n K) (x y : Fin n ⊕ Fin n → K) :
    spForm n K (((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
      (((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y) =
      (multiplierUnit A : K) * spForm n K x y := by
  have hJ := multiplierUnit_spec A
  rw [spForm, Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_comm,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  change x ⬝ᵥ ((((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
    formJ n K * ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *ᵥ y) =
      _
  rw [hJ, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem spForm_antisymm (x y : Fin n ⊕ Fin n → K) : spForm n K x y = -spForm n K y x := by
  rw [spForm_apply, spForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_ne_zero_spForm_eq_zero [Finite K] (hn : 2 ≤ n)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    ∃ u : Fin n ⊕ Fin n → K, u ≠ 0 ∧ spForm n K u (M *ᵥ u) = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := spGram n K * M with hNdef
  set F : MvPolynomial (Fin n ⊕ Fin n) K :=
    ∑ i, ∑ j, MvPolynomial.C (N i j) * MvPolynomial.X i * MvPolynomial.X j with hF
  have hval : ∀ u : Fin n ⊕ Fin n → K, MvPolynomial.eval u F = spForm n K u (M *ᵥ u) := by
    intro u
    rw [spForm, Matrix.toBilin'_apply', Matrix.mulVec_mulVec, hF]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dotProduct,
      Matrix.mulVec, Finset.mul_sum, hNdef]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdeg : F.totalDegree < Fintype.card (Fin n ⊕ Fin n) := by
    have hle : F.totalDegree ≤ 2 := by
      rw [hF]
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      calc (MvPolynomial.C (N i j) * MvPolynomial.X i * MvPolynomial.X j :
            MvPolynomial (Fin n ⊕ Fin n) K).totalDegree
          ≤ (MvPolynomial.C (N i j) * MvPolynomial.X i :
              MvPolynomial (Fin n ⊕ Fin n) K).totalDegree +
            (MvPolynomial.X j : MvPolynomial (Fin n ⊕ Fin n) K).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ ≤ ((MvPolynomial.C (N i j) : MvPolynomial (Fin n ⊕ Fin n) K).totalDegree +
              (MvPolynomial.X i : MvPolynomial (Fin n ⊕ Fin n) K).totalDegree) +
            (MvPolynomial.X j : MvPolynomial (Fin n ⊕ Fin n) K).totalDegree := by
            gcongr
            exact MvPolynomial.totalDegree_mul _ _
        _ = 2 := by
            rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X,
              MvPolynomial.totalDegree_X]
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions p hdeg
  by_contra hall
  push Not at hall
  have hsub : Subsingleton { x : Fin n ⊕ Fin n → K // MvPolynomial.eval x F = 0 } := by
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hx0 : x = 0 := by
      by_contra h
      exact hall x h (by rw [← hval]; exact hx)
    have hy0 : y = 0 := by
      by_contra h
      exact hall y h (by rw [← hval]; exact hy)
    exact Subtype.ext (hx0.trans hy0.symm)
  have hne : Nonempty { x : Fin n ⊕ Fin n → K // MvPolynomial.eval x F = 0 } :=
    ⟨⟨0, by rw [hval, Matrix.mulVec_zero]; exact spForm_self 0⟩⟩
  have hcard : Fintype.card { x : Fin n ⊕ Fin n → K // MvPolynomial.eval x F = 0 } = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨hne.some, fun y => Subsingleton.elim _ _⟩
  rw [hcard] at hdvd
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp hdvd)

theorem spForm_eq_zero_of_mem_orbI (A : gsp n K) {c : K}
    (hA : ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ^ 3 =
      c • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    {u : Fin n ⊕ Fin n → K}
    (hu : spForm n K u
      (((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u) = 0)
    {x y : Fin n ⊕ Fin n → K}
    (hx : x ∈ orbI ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) u)
    (hy : y ∈ orbI ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) u) :
    spForm n K x y = 0 := by
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    ((A : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hM
  set μ : K := (multiplierUnit A : K) with hμ
  have hμ0 : μ ≠ 0 := (multiplierUnit A).ne_zero
  have hsim : ∀ a b, spForm n K (M *ᵥ a) (M *ᵥ b) = μ * spForm n K a b :=
    fun a b => spForm_gsp_mulVec A a b
  have h01 : spForm n K u (M *ᵥ u) = 0 := hu
  have h12 : spForm n K (M *ᵥ u) (M *ᵥ (M *ᵥ u)) = 0 := by rw [hsim, h01, mul_zero]
  have h02 : spForm n K u (M *ᵥ (M *ᵥ u)) = 0 := by
    have h1 : spForm n K (M *ᵥ u) (M *ᵥ (M *ᵥ (M *ᵥ u))) = 0 := by
      have h3 : M *ᵥ (M *ᵥ (M *ᵥ u)) = c • u := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', hA, Matrix.smul_mulVec,
          Matrix.one_mulVec]
      rw [h3, map_smul, smul_eq_mul, spForm_antisymm, h01, neg_zero, mul_zero]
    rw [hsim] at h1
    exact (mul_eq_zero.mp h1).resolve_left hμ0
  have hgen : ∀ i j : Fin 3, spForm n K ((M ^ (i : ℕ)) *ᵥ u) ((M ^ (j : ℕ)) *ᵥ u) = 0 := by
    have e0 : (M ^ 0) *ᵥ u = u := by rw [pow_zero, Matrix.one_mulVec]
    have e1 : (M ^ 1) *ᵥ u = M *ᵥ u := by rw [pow_one]
    have e2 : (M ^ 2) *ᵥ u = M *ᵥ (M *ᵥ u) := by rw [pow_two, Matrix.mulVec_mulVec]
    intro i j
    fin_cases i <;> fin_cases j
    · exact spForm_self _
    · show spForm n K ((M ^ 0) *ᵥ u) ((M ^ 1) *ᵥ u) = 0
      rw [e0, e1]
      exact h01
    · show spForm n K ((M ^ 0) *ᵥ u) ((M ^ 2) *ᵥ u) = 0
      rw [e0, e2]
      exact h02
    · show spForm n K ((M ^ 1) *ᵥ u) ((M ^ 0) *ᵥ u) = 0
      rw [e1, e0, spForm_antisymm, h01, neg_zero]
    · exact spForm_self _
    · show spForm n K ((M ^ 1) *ᵥ u) ((M ^ 2) *ᵥ u) = 0
      rw [e1, e2]
      exact h12
    · show spForm n K ((M ^ 2) *ᵥ u) ((M ^ 0) *ᵥ u) = 0
      rw [e2, e0, spForm_antisymm, h02, neg_zero]
    · show spForm n K ((M ^ 2) *ᵥ u) ((M ^ 1) *ᵥ u) = 0
      rw [e2, e1, spForm_antisymm, h12, neg_zero]
    · exact spForm_self _
  have hleft : ∀ i : Fin 3, orbI M u ≤ LinearMap.ker (spForm n K ((M ^ (i : ℕ)) *ᵥ u)) := by
    intro i
    rw [orbI, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hgen i j
  have hright : orbI M u ≤ LinearMap.ker ((spForm n K).flip y) := by
    rw [orbI, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hleft i hy
  exact hright hx

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3Sp
