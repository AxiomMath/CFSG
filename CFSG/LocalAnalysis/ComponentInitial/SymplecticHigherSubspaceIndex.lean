module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherProjective
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGaussian

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

variable {r : ℕ} {K : Type} [Field K]

theorem mem_orthogonal_span_range_iff {ι : Type*} {s : ι → Fin r ⊕ Fin r → K}
    {v : Fin r ⊕ Fin r → K} :
    v ∈ (pairedSympForm K r).orthogonal (span K (Set.range s)) ↔
      ∀ i, pairedSympForm K r (s i) v = 0 := by
  rw [BilinForm.mem_orthogonal_iff]
  constructor
  · exact fun h i => h _ (subset_span ⟨i, rfl⟩)
  · intro h n hn
    have : span K (Set.range s) ≤ LinearMap.ker ((pairedSympForm K r).flip v) := by
      rw [span_le]
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (h i)
    exact LinearMap.mem_ker.mp (this hn)

theorem isTotallyIsotropic_span_range {ι : Type*} {s : ι → Fin r ⊕ Fin r → K}
    (h : ∀ i j, pairedSympForm K r (s i) (s j) = 0) :
    IsTotallyIsotropic (pairedSympForm K r) (span K (Set.range s)) := by
  intro x hx y hy
  have hy' : ∀ i, pairedSympForm K r (s i) y = 0 := by
    intro i
    have : span K (Set.range s) ≤ LinearMap.ker (pairedSympForm K r (s i)) := by
      rw [span_le]
      rintro _ ⟨j, rfl⟩
      exact LinearMap.mem_ker.mpr (h i j)
    exact LinearMap.mem_ker.mp (this hy)
  exact (BilinForm.mem_orthogonal_iff.mp (mem_orthogonal_span_range_iff.mpr hy')) x hx

theorem isTotallyIsotropic_map_spAct (g : StatedSp r K) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    IsTotallyIsotropic (pairedSympForm K r) (W.map (spAct g)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
  exact hW x hx y hy

theorem orth_finCons {k : ℕ} {s : Fin k → Fin r ⊕ Fin r → K} {v : Fin r ⊕ Fin r → K}
    (hs : ∀ i j, pairedSympForm K r (s i) (s j) = 0) (hv : ∀ i, pairedSympForm K r (s i) v = 0) :
    ∀ i j, pairedSympForm K r ((Fin.cons v s : Fin (k + 1) → Fin r ⊕ Fin r → K) i)
      ((Fin.cons v s : Fin (k + 1) → Fin r ⊕ Fin r → K) j) = 0 := by
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp only [Fin.cons_zero, Fin.cons_succ]
  · exact pairedSympForm_self v
  · exact SymplecticFlag.pairedSympForm_isAlt.isRefl _ _ (hv _)
  · exact hv _
  · exact hs _ _

variable (r K) in
@[expose] def IsoFrame (k : ℕ) : Set (Fin k → Fin r ⊕ Fin r → K) :=
  {s | LinearIndependent K s ∧ ∀ i j, pairedSympForm K r (s i) (s j) = 0}

@[expose] def isoFrameSuccEquiv (k : ℕ) : IsoFrame r K (k + 1) ≃
    Σ s : IsoFrame r K k, ↥(((pairedSympForm K r).orthogonal (span K (Set.range s.1)) :
      Set (Fin r ⊕ Fin r → K)) \ (span K (Set.range s.1) : Set (Fin r ⊕ Fin r → K))) where
  toFun s := ⟨⟨Fin.tail s.1, (linearIndependent_finSucc.mp s.2.1).1,
      fun i j => s.2.2 i.succ j.succ⟩,
    ⟨s.1 0, mem_orthogonal_span_range_iff.mpr fun i => s.2.2 i.succ 0,
      (linearIndependent_finSucc.mp s.2.1).2⟩⟩
  invFun s := ⟨Fin.cons s.2.1 s.1.1, linearIndependent_finCons.mpr ⟨s.1.2.1, s.2.2.2⟩,
    orth_finCons s.1.2.2 (mem_orthogonal_span_range_iff.mp s.2.2.1)⟩
  left_inv s := Subtype.ext (Fin.cons_self_tail s.1)
  right_inv := fun ⟨_, _⟩ => rfl

theorem card_orthogonal_sdiff_span [Finite K] {k : ℕ} (s : IsoFrame r K k) :
    Nat.card ↥(((pairedSympForm K r).orthogonal (span K (Set.range s.1)) :
      Set (Fin r ⊕ Fin r → K)) \ (span K (Set.range s.1) : Set (Fin r ⊕ Fin r → K))) =
      Nat.card K ^ (2 * r - k) - Nat.card K ^ k := by
  set N := span K (Set.range s.1)
  have hN : finrank K N = k := by rw [finrank_span_eq_card s.2.1, Fintype.card_fin]
  have hNO : N ≤ (pairedSympForm K r).orthogonal N := fun x hx =>
    BilinForm.mem_orthogonal_iff.mpr fun y hy => isTotallyIsotropic_span_range s.2.2 y hy x hx
  have hO : finrank K ((pairedSympForm K r).orthogonal N) = 2 * r - k := by
    have h := BilinForm.finrank_add_finrank_orthogonal
      SymplecticFlag.pairedSympForm_isAlt.isRefl N
    rw [BilinForm.orthogonal_top_eq_bot SymplecticFlag.pairedSympForm_nondegenerate, inf_bot_eq,
      finrank_bot, add_zero, finrank_standard, hN] at h
    omega
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff (SetLike.coe_subset_coe.mpr hNO),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe,
    Module.natCard_eq_pow_finrank (K := K) (V := (pairedSympForm K r).orthogonal N),
    Module.natCard_eq_pow_finrank (K := K) (V := N), hO, hN]

theorem card_isoFrame [Finite K] {k : ℕ} (hk : k ≤ r) :
    Nat.card (IsoFrame r K k) =
      ∏ i ∈ Finset.range k, (Nat.card K ^ (2 * r - i) - Nat.card K ^ i) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩,
      ⟨⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩⟩⟩
  | succ k ih =>
    have := Fintype.ofFinite (IsoFrame r K k)
    rw [Nat.card_congr (isoFrameSuccEquiv k), Nat.card_sigma,
      Finset.sum_congr rfl fun s _ => card_orthogonal_sdiff_span s, Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, ih (by omega),
      Finset.prod_range_succ]

variable (r K) in
@[expose] def isoSubspaces (k : ℕ) : Set (Submodule K (Fin r ⊕ Fin r → K)) :=
  {W | IsTotallyIsotropic (pairedSympForm K r) W ∧ finrank K W = k}

@[expose] def isoFrameSpan {k : ℕ} (s : IsoFrame r K k) : isoSubspaces r K k :=
  ⟨span K (Set.range s.1), isTotallyIsotropic_span_range s.2.2, by
    rw [finrank_span_eq_card s.2.1, Fintype.card_fin]⟩

theorem span_range_eq_of_linearIndependent {k : ℕ} {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : finrank K W = k) {t : Fin k → W} (ht : LinearIndependent K t) :
    span K (Set.range fun i => (t i : Fin r ⊕ Fin r → K)) = W := by
  have hli : LinearIndependent K fun i => (t i : Fin r ⊕ Fin r → K) :=
    ht.map' W.subtype (ker_subtype W)
  refine eq_of_le_of_finrank_eq ?_ ?_
  · rw [span_le]
    rintro _ ⟨i, rfl⟩
    exact (t i).2
  · rw [finrank_span_eq_card hli, Fintype.card_fin, hW]

@[expose] def isoFrameFiberEquiv {k : ℕ} (W : isoSubspaces r K k) :
    {s : IsoFrame r K k // isoFrameSpan s = W} ≃ {t : Fin k → W.1 // LinearIndependent K t} where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      rw [← congrArg Subtype.val s.2]
      exact subset_span ⟨i, rfl⟩⟩,
    LinearIndependent.of_comp W.1.subtype s.1.2.1⟩
  invFun t := ⟨⟨fun i => (t.1 i : Fin r ⊕ Fin r → K), by exact t.2.map' W.1.subtype (ker_subtype _),
      fun i j => W.2.1 _ (t.1 i).2 _ (t.1 j).2⟩,
    Subtype.ext (span_range_eq_of_linearIndependent W.2.2 t.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_isoFrameFiber [Finite K] {k : ℕ} (W : isoSubspaces r K k) :
    Nat.card {s : IsoFrame r K k // isoFrameSpan s = W} =
      ∏ i ∈ Finset.range k, (Nat.card K ^ k - Nat.card K ^ i) := by
  have := Fintype.ofFinite K
  rw [Nat.card_congr (isoFrameFiberEquiv W), card_linearIndependent W.2.2.ge, W.2.2,
    Fintype.card_eq_nat_card,
    Fin.prod_univ_eq_prod_range (fun i => Nat.card K ^ k - Nat.card K ^ i)]

theorem card_isoSubspaces_mul [Finite K] (k : ℕ) :
    Nat.card (isoSubspaces r K k) * ∏ i ∈ Finset.range k, (Nat.card K ^ k - Nat.card K ^ i) =
      Nat.card (IsoFrame r K k) := by
  have : Finite (Submodule K (Fin r ⊕ Fin r → K)) :=
    Finite.of_injective _ SetLike.coe_injective
  have := Fintype.ofFinite (isoSubspaces r K k)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (isoFrameSpan (r := r) (K := K) (k := k))),
    Nat.card_sigma, Finset.sum_congr rfl fun W _ => card_isoFrameFiber W, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]

theorem card_isoSubspaces [Finite K] {q : ℕ} (hq : Nat.card K = q) {k : ℕ} (hk : k ≤ r) :
    (Nat.card (isoSubspaces r K k) : ℚ) = isoGaussian r k q := by
  have hq2 : 2 ≤ q := by
    rw [← hq]
    exact Finite.one_lt_card
  have hq0 : (q : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq2
    positivity
  have h := card_isoSubspaces_mul (r := r) (K := K) k
  rw [card_isoFrame hk, hq] at h
  have h' := congrArg (Nat.cast : ℕ → ℚ) h
  rw [Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at h'
  have hden : ∀ i ∈ Finset.range k,
      ((q ^ k - q ^ i : ℕ) : ℚ) = (q : ℚ) ^ i * ((q : ℚ) ^ (k - i) - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) hi.le), Nat.cast_pow, Nat.cast_pow,
      mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi.le]
  have hnum : ∀ i ∈ Finset.range k,
      ((q ^ (2 * r - i) - q ^ i : ℕ) : ℚ) = (q : ℚ) ^ i * ((q : ℚ) ^ (2 * (r - i)) - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (by omega)), Nat.cast_pow, Nat.cast_pow,
      mul_sub, mul_one, ← pow_add, show i + 2 * (r - i) = 2 * r - i by omega]
  rw [Finset.prod_congr rfl hden, Finset.prod_congr rfl hnum, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib] at h'
  have hD : ∏ i ∈ Finset.range k, ((q : ℚ) ^ (k - i) - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi =>
      (LinearFlag.pow_sub_one_pos hq2 (by rw [Finset.mem_range] at hi; omega)).ne'
  have hP : ∏ i ∈ Finset.range k, (q : ℚ) ^ i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hq0
  rw [isoGaussian, Finset.prod_div_distrib, eq_div_iff hD]
  refine mul_left_cancel₀ hP ?_
  linear_combination h'

theorem index_projStabilizer [Finite K] {k : ℕ} {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : W ∈ isoSubspaces r K k) :
    (projStabilizer r K W).index = Nat.card (isoSubspaces r K k) := by
  let : MulAction (StatedSp r K) (isoSubspaces r K k) :=
    { smul := fun g W => ⟨W.1.map (spAct g), isTotallyIsotropic_map_spAct g W.2.1,
        (finrank_map_spAct g W.1).trans W.2.2⟩
      one_smul := fun W => Subtype.ext (map_spAct_one W.1)
      mul_smul := fun g h W => Subtype.ext (map_spAct_mul g h W.1) }
  have : MulAction.IsPretransitive (StatedSp r K) (isoSubspaces r K k) := ⟨fun W W' => by
    obtain ⟨g, hg⟩ := exists_statedSp_map_eq W.2.1 W'.2.1 (W.2.2.trans W'.2.2.symm)
    exact ⟨g, Subtype.ext hg⟩⟩
  have hstab : MulAction.stabilizer (StatedSp r K) (⟨W, hW⟩ : isoSubspaces r K k) =
      stabilizer r K W := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_stabilizer]
    exact Subtype.ext_iff
  rw [← MulAction.index_stabilizer_of_transitive (StatedSp r K) (⟨W, hW⟩ : isoSubspaces r K k),
    hstab, ← comap_projStabilizer]
  exact (Subgroup.index_comap_of_surjective (H := projStabilizer r K W)
    (proj_surjective (r := r) (K := K))).symm

theorem isotropic_subspace_index [Finite K] {q : ℕ} (hq : Nat.card K = q) {k : ℕ} (hk : k ≤ r) :
    (Nat.card {W : Submodule K (Fin r ⊕ Fin r → K) //
      IsTotallyIsotropic (pairedSympForm K r) W ∧ finrank K W = k} : ℚ) = isoGaussian r k q ∧
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), IsTotallyIsotropic (pairedSympForm K r) W →
      finrank K W = k → ((projStabilizer r K W).index : ℚ) = isoGaussian r k q) ∧
    isoGaussian r 1 q = ((q : ℚ) ^ (2 * r) - 1) / ((q : ℚ) - 1) ∧
    isoGaussian r r q = ∏ j ∈ Finset.range r, ((q : ℚ) ^ (j + 1) + 1) := by
  have hq2 : 2 ≤ q := by
    rw [← hq]
    exact Finite.one_lt_card
  refine ⟨card_isoSubspaces hq hk, fun W hW hWk => ?_, isoGaussian_one r q,
    isoGaussian_self hq2 r⟩
  rw [index_projStabilizer (k := k) ⟨hW, hWk⟩]
  exact card_isoSubspaces hq hk

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
