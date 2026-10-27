module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIndexComparison

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Matrix
open scoped Pointwise

section Pair

variable {G : Type*} [Group G]

theorem not_isCyclic_of_not_mem_zpowers [Finite G] {Q : Subgroup G} {x y : G} (hx : x ∈ Q)
    (hy : y ∈ Q) (hxy : orderOf x = orderOf y) (hyx : y ∉ Subgroup.zpowers x) : ¬ IsCyclic Q := by
  intro hc
  have hcard : Nat.card (Subgroup.zpowers (⟨x, hx⟩ : Q)) =
      Nat.card (Subgroup.zpowers (⟨y, hy⟩ : Q)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxy]
  have heq := (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  have hmem : (⟨y, hy⟩ : Q) ∈ Subgroup.zpowers (⟨x, hx⟩ : Q) := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact hyx (Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)

theorem isPGroup_closure_pair_twistedA {x y : G} (hxy : Commute x y) {m : ℕ} (hx : x ^ m = 1)
    (hy : y ^ m = 1) : IsPGroup m (Subgroup.closure ({x, y} : Set G)) := by
  have hcent : Subgroup.closure ({x, y} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.closure_le]
    rintro g (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      rintro z (rfl | rfl)
    exacts [rfl, hxy.symm.eq, hxy.eq, rfl]
  have key : ∀ g (hg : g ∈ Subgroup.closure ({x, y} : Set G)), g ^ m = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => rcases hg with rfl | rfl <;> assumption
    | one => exact one_pow m
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := Subgroup.mem_centralizer_iff.mp (hcent hb) a ha
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by rw [pow_one]; exact key g g.2)⟩

end Pair

section Diag

variable {K : Type} [Field K]

@[expose] noncomputable def diagFirst {η : K} (hη : η ≠ 0) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![η, η⁻¹, 1], by simp [det_diagonal, Fin.prod_univ_three, hη]⟩

@[expose] noncomputable def diagSecond {η : K} (hη : η ≠ 0) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![1, η, η⁻¹], by simp [det_diagonal, Fin.prod_univ_three, hη]⟩

theorem commute_diagFirst_diagSecond {η : K} (hη : η ≠ 0) :
    Commute (diagFirst hη) (diagSecond hη) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change (diagonal ![η, η⁻¹, 1] * diagonal ![1, η, η⁻¹]) i j =
    (diagonal ![1, η, η⁻¹] * diagonal ![η, η⁻¹, 1]) i j
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  funext k
  exact mul_comm _ _

theorem diagFirst_pow {η : K} (hη : η ≠ 0) (n : ℕ) :
    ((diagFirst hη ^ n : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![η ^ n, η⁻¹ ^ n, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, diagFirst]
  change diagonal ![η, η⁻¹, 1] ^ n = _
  rw [diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagSecond_pow {η : K} (hη : η ≠ 0) (n : ℕ) :
    ((diagSecond hη ^ n : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![1, η ^ n, η⁻¹ ^ n] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, diagSecond]
  change diagonal ![1, η, η⁻¹] ^ n = _
  rw [diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagFirst_diagSecond_facts {m : ℕ} (hm : m.Prime) {η : K} (hη : IsPrimitiveRoot η m)
    (hη0 : η ≠ 0) :
    orderOf (diagFirst hη0) = m ∧ orderOf (diagSecond hη0) = m ∧
      ∀ n : ℕ, diagFirst hη0 ^ n ≠ diagSecond hη0 := by
  have : Fact m.Prime := ⟨hm⟩
  have hη1 : η ≠ 1 := hη.ne_one hm.one_lt
  have hηi : η⁻¹ ≠ 1 := fun h => hη1 (inv_eq_one.mp h)
  refine ⟨orderOf_eq_prime ?_ ?_, orderOf_eq_prime ?_ ?_, fun n hn => ?_⟩
  · refine Subtype.ext ?_
    rw [diagFirst_pow, Matrix.SpecialLinearGroup.coe_one, inv_pow, hη.pow_eq_one, inv_one,
      ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro h1
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [diagFirst] at this
    exact hη1 this
  · refine Subtype.ext ?_
    rw [diagSecond_pow, Matrix.SpecialLinearGroup.coe_one, inv_pow, hη.pow_eq_one, inv_one,
      ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro h1
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) 1 1) h1
    simp [diagSecond] at this
    exact hη1 this
  · have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) 2 2) hn
    simp only [diagFirst_pow] at this
    simp [diagSecond] at this
    exact hη1 this

end Diag

section Levi

variable {p f : ℕ} {K : Type} [Field K] {s ε : ℕ}

@[expose] noncomputable def diagBlockThree (s : ℕ) (A : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin (3 + s)) (Fin (3 + s)) K :=
  reindexAlgEquiv K K finSumFinEquiv (fromBlocks A 0 0 1)

theorem diagBlockThree_mul (A B : Matrix (Fin 3) (Fin 3) K) :
    diagBlockThree s (A * B) = diagBlockThree s A * diagBlockThree s B := by
  rw [diagBlockThree, diagBlockThree, diagBlockThree, ← map_mul, fromBlocks_multiply]
  simp

theorem diagBlockThree_one : diagBlockThree s (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [diagBlockThree, fromBlocks_one, map_one]

theorem det_diagBlockThree (A : Matrix (Fin 3) (Fin 3) K) : (diagBlockThree s A).det = A.det := by
  rw [diagBlockThree, det_reindexAlgEquiv, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem diagBlockThree_castAdd (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    diagBlockThree s A (Fin.castAdd s i) (Fin.castAdd s j) = A i j := by
  simp [diagBlockThree, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd]

theorem diagBlockThree_apply_of_le (A : Matrix (Fin 3) (Fin 3) K) {j : Fin (3 + s)}
    (hj : 3 ≤ (j : ℕ)) (k : Fin (3 + s)) :
    diagBlockThree s A j k = if j = k then 1 else 0 := by
  obtain ⟨j', rfl⟩ : ∃ j' : Fin s, j = Fin.natAdd 3 j' :=
    ⟨⟨j - 3, by omega⟩, Fin.ext (by simp; omega)⟩
  rcases hk : finSumFinEquiv.symm k with k' | k'
  · have hk' : k = Fin.castAdd s k' := by
      rw [← finSumFinEquiv_apply_left, ← hk, Equiv.apply_symm_apply]
    subst hk'
    have hne : Fin.natAdd 3 j' ≠ Fin.castAdd s k' := by
      intro he
      have := congrArg Fin.val he
      simp at this
      omega
    simp [diagBlockThree, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
      finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, hne]
  · have hk' : k = Fin.natAdd 3 k' := by
      rw [← finSumFinEquiv_apply_right, ← hk, Equiv.apply_symm_apply]
    subst hk'
    simp [diagBlockThree, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
      finSumFinEquiv_symm_apply_natAdd, one_apply]

@[expose] noncomputable def leviMatTwistedA (h : UnitaryFieldData p f K) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) K) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  blk3 A 0 0 1 0 (barInvT h A)

variable (h : UnitaryFieldData p f K)

theorem leviMatTwistedA_gram {r : ℕ} {A : Matrix (Fin r) (Fin r) K} (hA : IsUnit A.det) :
    ((leviMatTwistedA (ε := ε) h A).map h.bar)ᵀ * hypGram r ε K * leviMatTwistedA h A =
      hypGram r ε K := by
  refine (blk3_gram_iff h _ _ _ _ _ _).mpr ⟨conjTranspose_mul_barInvT hA, ?_, ?_, ?_⟩
  · rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.one_mul]
  · simp [Matrix.map_zero _ (map_zero h.bar)]
  · simp [Matrix.map_zero _ (map_zero h.bar)]

theorem det_leviMatTwistedA {r : ℕ} {A : Matrix (Fin r) (Fin r) K} (hA : A.det = 1) :
    (leviMatTwistedA (ε := ε) h A).det = 1 := by
  have hu : IsUnit A.det := by rw [hA]; exact isUnit_one
  rw [leviMatTwistedA, det_blk3, det_one, mul_one, det_barInvT hu, hA, map_one, inv_one, mul_one]

theorem leviMatTwistedA_mul {r : ℕ} (A B : Matrix (Fin r) (Fin r) K) :
    leviMatTwistedA (ε := ε) h (A * B) = leviMatTwistedA h A * leviMatTwistedA h B := by
  rw [leviMatTwistedA, leviMatTwistedA, leviMatTwistedA, blk3_mul, barInvT_mul]
  simp

@[expose] noncomputable def leviHomTwistedA (s ε : ℕ) :
    Matrix.SpecialLinearGroup (Fin 3) K →* hypSU h (3 + s) ε where
  toFun A := mkHypSU h (leviMatTwistedA h (diagBlockThree s (A : Matrix (Fin 3) (Fin 3) K)))
    (leviMatTwistedA_gram h (by rw [det_diagBlockThree, A.2]; exact isUnit_one))
    (det_leviMatTwistedA h (by rw [det_diagBlockThree, A.2]))
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_mkHypSU, Matrix.SpecialLinearGroup.coe_one, diagBlockThree_one]
    simp [leviMatTwistedA, barInvT, blk3]
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_mkHypSU, Subgroup.coe_mul, Units.val_mul, coe_mkHypSU, coe_mkHypSU,
      Matrix.SpecialLinearGroup.coe_mul, diagBlockThree_mul, leviMatTwistedA_mul]

theorem coe_leviHomTwistedA (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    (((leviHomTwistedA h s ε A : hypSU h (3 + s) ε) : GL (HypIndex (3 + s) ε) K) :
      Matrix (HypIndex (3 + s) ε) (HypIndex (3 + s) ε) K) =
      leviMatTwistedA h (diagBlockThree s (A : Matrix (Fin 3) (Fin 3) K)) :=
  rfl

theorem leviHomTwistedA_injective : Function.Injective (leviHomTwistedA (K := K) h s ε) := by
  intro A B hAB
  have h1 := congrArg (fun g : hypSU h (3 + s) ε =>
    ((g : GL (HypIndex (3 + s) ε) K) : Matrix (HypIndex (3 + s) ε) (HypIndex (3 + s) ε) K)) hAB
  simp only [coe_leviHomTwistedA] at h1
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have := congrFun (congrFun h1 (.inl (Fin.castAdd s i))) (.inl (Fin.castAdd s j))
  simpa [leviMatTwistedA, diagBlockThree_castAdd] using this

theorem leviMatTwistedA_mulVec_mem_posFlag (A : Matrix (Fin 3) (Fin 3) K) {i : ℕ} (hi3 : 3 ≤ i)
    (hir : i ≤ 3 + s) {v : HypIndex (3 + s) ε → K} (hv : v ∈ posFlag (3 + s) ε K i) :
    leviMatTwistedA h (diagBlockThree s A) *ᵥ v ∈ posFlag (3 + s) ε K i := by
  intro a ha
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : i ≤ fullPos b
  · rw [hv b hb, mul_zero]
  · rcases b with k | l | k
    · simp only [fullPos_inl, not_le] at hb
      rcases a with j | l | j
      · simp only [fullPos_inl] at ha
        have hjk : j ≠ k := fun he => by rw [he] at ha; omega
        rw [leviMatTwistedA, blk3_inl_inl, diagBlockThree_apply_of_le A (by omega)]
        simp [hjk]
      · rw [leviMatTwistedA, blk3_inr_inl_inl, zero_mul]
      · rw [leviMatTwistedA, blk3_inr_inr_inl, zero_mul]
    · simp at hb
      omega
    · simp at hb
      omega

theorem leviHomTwistedA_smul_hypFlag (hε : ε ≤ 1) (A : Matrix.SpecialLinearGroup (Fin 3) K) {i : ℕ}
    (hi3 : 3 ≤ i) (hir : i ≤ 3 + s) : leviHomTwistedA h s ε A • hypFlag h (3 + s) ε i =
      hypFlag h (3 + s) ε i := by
  rw [hypFlag_eq_posFlag h hε (by omega), Subgroup.smul_def]
  refine smul_eq_of_mulVec_mem (fun v hv => ?_) (fun v hv => ?_)
  · rw [coe_leviHomTwistedA]
    exact leviMatTwistedA_mulVec_mem_posFlag h _ hi3 hir hv
  · have : ((leviHomTwistedA h s ε A : hypSU h (3 + s) ε) : GL (HypIndex (3 + s) ε) K)⁻¹ =
        ((leviHomTwistedA h s ε A⁻¹ : hypSU h (3 + s) ε) : GL (HypIndex (3 + s) ε) K) := by
      rw [map_inv, Subgroup.coe_inv]
    rw [this, coe_leviHomTwistedA]
    exact leviMatTwistedA_mulVec_mem_posFlag h _ hi3 hir hv

end Levi

variable {p f : ℕ} {K : Type} [Field K] {s ε : ℕ}

theorem false_of_levi_three [Finite K] (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 3) K) = ⊤)
    {J : Subgroup (hypSU h (3 + s) ε)} (c : hypSU h (3 + s) ε) {I : Set ℕ}
    (hJI : ∀ y : hypSU h (3 + s) ε, y ∈ J ↔
      ∀ i ∈ I, y • (c • hypFlag h (3 + s) ε i) = c • hypFlag h (3 + s) ε i)
    (hI : I ⊆ Set.Icc 3 (3 + s)) {m : ℕ} (hm : m.Prime) {η : K} (hη : IsPrimitiveRoot η m)
    (hcyc : ∀ V : Subgroup (hypSU h (3 + s) ε), V ≤ J → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (hypSU h (3 + s) ε), Q ≤ V → IsPGroup m Q → IsCyclic Q) : False := by
  have hη0 : η ≠ 0 := hη.ne_zero hm.ne_zero
  set φ : Matrix.SpecialLinearGroup (Fin 3) K →* hypSU h (3 + s) ε :=
    (MulAut.conj c).toMonoidHom.comp (leviHomTwistedA h s ε) with hφ
  have hφinj : Function.Injective φ :=
    (MulAut.conj c).injective.comp (leviHomTwistedA_injective h)
  set V : Subgroup (hypSU h (3 + s) ε) := (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map φ
  have hVperf : ⁅V, V⁆ = V := by
    rw [← Subgroup.map_commutator, ← commutator_def, hSL]
  have hVJ : V ≤ J := by
    rintro _ ⟨A, -, rfl⟩
    refine (hJI _).mpr fun i hi => ?_
    obtain ⟨hi3, hir⟩ := hI hi
    change (c * leviHomTwistedA h s ε A * c⁻¹) • (c • hypFlag h (3 + s) ε i) = _
    rw [mul_smul, mul_smul, inv_smul_smul, leviHomTwistedA_smul_hypFlag h hε A hi3 hir]
  obtain ⟨ho1, ho2, hpow⟩ := diagFirst_diagSecond_facts hm hη hη0
  set x := φ (diagFirst hη0)
  set y := φ (diagSecond hη0)
  have hxy : Commute x y := (commute_diagFirst_diagSecond hη0).map φ
  have hxm : x ^ m = 1 := by rw [← map_pow, ← ho1, pow_orderOf_eq_one, map_one]
  have hym : y ^ m = 1 := by rw [← map_pow, ← ho2, pow_orderOf_eq_one, map_one]
  set Q := Subgroup.closure ({x, y} : Set (hypSU h (3 + s) ε))
  have hQV : Q ≤ V := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, Subgroup.mem_top _, rfl⟩
    · exact ⟨_, Subgroup.mem_top _, rfl⟩
  have hQ := hcyc V hVJ hVperf Q hQV (isPGroup_closure_pair_twistedA hxy hxm hym)
  have hord : orderOf x = orderOf y := by
    rw [orderOf_injective φ hφinj, orderOf_injective φ hφinj, ho1, ho2]
  refine not_isCyclic_of_not_mem_zpowers (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton y))) hord ?_ hQ
  intro hmem
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hmem
  obtain ⟨n, -, hn⟩ := hmem
  rw [← map_pow] at hn
  exact hpow n (hφinj hn)

end CFSG.AGLEmbedding.ToralCensus
