module

public import CFSG.ClassicalInvolution.RouteD.GapsD4ABasic
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

open Matrix CFSG.ComponentClassification
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL slConjugation_diagGL_apply mul_eq_of_conj_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {n : ℕ} {k : Type} [Field k]

variable (k) in
@[expose] def compIndicator (J : Finset (Fin n)) : Matrix (Fin n) (Fin n) k :=
  diagonal fun i => if i ∈ J then 0 else 1

theorem compIndicator_mul_apply (J : Finset (Fin n)) (g : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (compIndicator k J * g) i j = if i ∈ J then 0 else g i j := by
  rw [compIndicator, diagonal_mul]
  split_ifs <;> simp

theorem mul_compIndicator_apply (J : Finset (Fin n)) (g : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (g * compIndicator k J) i j = if j ∈ J then 0 else g i j := by
  rw [compIndicator, mul_diagonal]
  split_ifs <;> simp

theorem compIndicator_apply (J : Finset (Fin n)) (i j : Fin n) :
    compIndicator k J i j = if i ∉ J ∧ i = j then 1 else 0 := by
  rw [compIndicator, diagonal_apply]
  by_cases hij : i = j <;> by_cases hi : i ∈ J <;> simp [hij, hi]

variable (k) in
@[expose] def coordBlockSL (J : Finset (Fin n)) : Subgroup (SpecialLinearGroup (Fin n) k) where
  carrier := {g | compIndicator k J * (g : Matrix (Fin n) (Fin n) k) = compIndicator k J ∧
    (g : Matrix (Fin n) (Fin n) k) * compIndicator k J = compIndicator k J}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    change compIndicator k J * ((g : Matrix (Fin n) (Fin n) k) * h) = compIndicator k J ∧
      ((g : Matrix (Fin n) (Fin n) k) * h) * compIndicator k J = compIndicator k J
    exact ⟨by rw [← Matrix.mul_assoc, hg1, hh1], by rw [Matrix.mul_assoc, hh2, hg2]⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    set gi : Matrix (Fin n) (Fin n) k :=
      ((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) with hgi
    have h1 : (g : Matrix (Fin n) (Fin n) k) * gi = 1 := by
      rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 : gi * (g : Matrix (Fin n) (Fin n) k) = 1 := by
      rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    change compIndicator k J * gi = compIndicator k J ∧ gi * compIndicator k J = compIndicator k J
    refine ⟨?_, ?_⟩
    · calc compIndicator k J * gi = (compIndicator k J * g) * gi := by rw [hg1]
        _ = compIndicator k J := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    · calc gi * compIndicator k J = gi * (g * compIndicator k J) := by rw [hg2]
        _ = compIndicator k J := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem mem_coordBlockSL_iff {J : Finset (Fin n)} {g : SpecialLinearGroup (Fin n) k} :
    g ∈ coordBlockSL k J ↔ ∀ i j, (i ∉ J ∨ j ∉ J) →
      (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := congrFun (congrFun h1 i) j
      simp only [compIndicator_mul_apply, compIndicator_apply, hi, not_false_eq_true, true_and,
        ite_false] at this
      rw [this]
    · have := congrFun (congrFun h2 i) j
      simp only [mul_compIndicator_apply, compIndicator_apply, hj, ite_false] at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      rw [compIndicator_mul_apply, compIndicator_apply]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ite_false, not_false_eq_true, true_and]
        exact h i j (Or.inl hi)
    · ext i j
      rw [mul_compIndicator_apply, compIndicator_apply]
      by_cases hj : j ∈ J
      · by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hj, hij]
      · simp only [hj, ite_false]
        rw [h i j (Or.inr hj)]
        by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hij]

variable (k) in
@[expose] noncomputable def blockOn (J : Finset (Fin n))
    (X : Matrix (Fin J.card) (Fin J.card) k) : Matrix (Fin n) (Fin n) k :=
  reindexAlgEquiv k k (Equiv.sumCompl (· ∈ J))
    (fromBlocks (reindexAlgEquiv k k J.equivFin.symm X) 0 0 1)

theorem blockOn_one (J : Finset (Fin n)) : blockOn k J 1 = 1 := by
  rw [blockOn, map_one, fromBlocks_one, map_one]

theorem blockOn_mul (J : Finset (Fin n)) (X Y : Matrix (Fin J.card) (Fin J.card) k) :
    blockOn k J (X * Y) = blockOn k J X * blockOn k J Y := by
  rw [blockOn, blockOn, blockOn, ← map_mul, fromBlocks_multiply, map_mul]
  simp

theorem det_blockOn (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) k) :
    (blockOn k J X).det = X.det := by
  rw [blockOn, coe_reindexAlgEquiv, det_reindex_self, det_fromBlocks_zero₂₁, coe_reindexAlgEquiv,
    det_reindex_self, det_one, mul_one]

theorem blockOn_apply_mem (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) k)
    {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J) :
    blockOn k J X i j = X (J.equivFin ⟨i, hi⟩) (J.equivFin ⟨j, hj⟩) := by
  rw [blockOn, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj, fromBlocks_apply₁₁,
    coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  rfl

theorem blockOn_apply_not_mem (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) k)
    {i j : Fin n} (hij : i ∉ J ∨ j ∉ J) : blockOn k J X i j = if i = j then 1 else 0 := by
  rw [blockOn, coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · exact absurd (hij.elim (fun h => absurd hi h) fun h => absurd hj h) id
  · rw [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₁₂, Matrix.zero_apply]
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [hne]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj,
      fromBlocks_apply₂₁, Matrix.zero_apply]
    have hne : i ≠ j := fun h => hi (h ▸ hj)
    simp [hne]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₂₂, one_apply]
    by_cases h : i = j
    · subst h
      simp
    · have h' : (⟨i, hi⟩ : {a // a ∉ J}) ≠ ⟨j, hj⟩ := fun h' => h (congrArg Subtype.val h')
      simp only [h, h', ite_false]

variable (k) in
@[expose] noncomputable def blockSLOn (J : Finset (Fin n)) :
    SpecialLinearGroup (Fin J.card) k →* SpecialLinearGroup (Fin n) k where
  toFun X := ⟨blockOn k J X, (det_blockOn J (X : Matrix (Fin J.card) (Fin J.card) k)).trans X.2⟩
  map_one' := Subtype.ext <| by
    show blockOn k J ((1 : SpecialLinearGroup (Fin J.card) k) : Matrix _ _ k) = 1
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact blockOn_one J
  map_mul' X Y := Subtype.ext <| by
    show blockOn k J ((X * Y : SpecialLinearGroup (Fin J.card) k) : Matrix _ _ k) =
      blockOn k J X * blockOn k J Y
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact blockOn_mul J _ _

theorem coe_blockSLOn (J : Finset (Fin n)) (X : SpecialLinearGroup (Fin J.card) k) :
    (blockSLOn k J X : Matrix (Fin n) (Fin n) k) = blockOn k J X :=
  rfl

theorem blockSLOn_injective (J : Finset (Fin n)) : Function.Injective (blockSLOn k J) := by
  intro X Y h
  ext a b
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k =>
    (g : Matrix (Fin n) (Fin n) k) (J.equivFin.symm a) (J.equivFin.symm b)) h
  simp only [coe_blockSLOn] at h1
  rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
    blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at h1
  simpa using h1

theorem range_blockSLOn (J : Finset (Fin n)) : (blockSLOn k J).range = coordBlockSL k J := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [mem_coordBlockSL_iff]
    intro i j hij
    rw [coe_blockSLOn, blockOn_apply_not_mem J _ hij]
  · intro g hg
    rw [mem_coordBlockSL_iff] at hg
    set X : Matrix (Fin J.card) (Fin J.card) k :=
      Matrix.of fun a b => (g : Matrix (Fin n) (Fin n) k) (J.equivFin.symm a) (J.equivFin.symm b)
      with hX
    have hXg : blockOn k J X = (g : Matrix (Fin n) (Fin n) k) := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J X hi hj, hX, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J X (Or.inr hj), hg i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
    have hdet : X.det = 1 := by
      rw [← det_blockOn J X, hXg]
      exact g.2
    exact ⟨⟨X, hdet⟩, Subtype.ext hXg⟩

theorem isQuasisimple_SL_of_two_le [Finite k] {m : ℕ} (hm : 2 ≤ m) (h4 : 4 ≤ Nat.card k) :
    CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin m) k) :=
  (AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (CatalogueBGeneralLinear.specialLinear_quasisimple m k hm (Or.inr (by omega))
      (Or.inr (by omega)))

theorem isQuasisimple_coordBlockSL [Finite k] {J : Finset (Fin n)} (hJ : 2 ≤ J.card)
    (h4 : 4 ≤ Nat.card k) : CFSG.Open.IsQuasisimple (coordBlockSL k J) :=
  Components.quasisimple_of_equiv
    ((MonoidHom.ofInjective (blockSLOn_injective (k := k) J)).trans
      (MulEquiv.subgroupCongr (range_blockSLOn J))).symm
    (isQuasisimple_SL_of_two_le hJ h4)

theorem conj_mem_coordBlockSL {J : Finset (Fin n)} {y g : SpecialLinearGroup (Fin n) k}
    (hyP : compIndicator k J * (y : Matrix (Fin n) (Fin n) k) =
      (y : Matrix (Fin n) (Fin n) k) * compIndicator k J)
    (hg : g ∈ coordBlockSL k J) : y * g * y⁻¹ ∈ coordBlockSL k J := by
  obtain ⟨hg1, hg2⟩ := hg
  set P := compIndicator k J with hP
  set Y : Matrix (Fin n) (Fin n) k := (y : Matrix (Fin n) (Fin n) k) with hY
  set G : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k) with hG
  set Yi : Matrix (Fin n) (Fin n) k :=
    ((y⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) with hYi
  have h1 : Y * Yi = 1 := by
    rw [hY, hYi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have h2 : Yi * Y = 1 := by
    rw [hY, hYi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hYiP : P * Yi = Yi * P := by
    calc P * Yi = Yi * Y * P * Yi := by rw [h2, Matrix.one_mul]
      _ = Yi * (Y * P) * Yi := by simp only [Matrix.mul_assoc]
      _ = Yi * (P * Y) * Yi := by rw [hyP]
      _ = Yi * P * (Y * Yi) := by simp only [Matrix.mul_assoc]
      _ = Yi * P := by rw [h1, Matrix.mul_one]
  change P * (Y * G * Yi) = P ∧ (Y * G * Yi) * P = P
  refine ⟨?_, ?_⟩
  · calc P * (Y * G * Yi) = Y * (P * G) * Yi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hyP]; simp only [Matrix.mul_assoc]
      _ = Y * (P * Yi) := by rw [hg1, Matrix.mul_assoc]
      _ = Y * (Yi * P) := by rw [hYiP]
      _ = P := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · calc (Y * G * Yi) * P = Y * (G * P) * Yi := by
          rw [Matrix.mul_assoc, ← hYiP]; simp only [Matrix.mul_assoc]
      _ = (Y * P) * Yi := by rw [hg2]
      _ = (P * Y) * Yi := by rw [hyP]
      _ = P := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

section Sign

@[expose] def signUnit (k : Type) [Field k] (b : Bool) : kˣ := if b then 1 else -1

variable (k) in
@[expose] noncomputable def signGL (σ : Fin n → Bool) : GL (Fin n) k :=
  diagGL fun i => signUnit k (σ i)

variable (k) in
@[expose] def coordSet (σ : Fin n → Bool) (b : Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => σ i = b

theorem mem_coordSet {σ : Fin n → Bool} {b : Bool} {i : Fin n} : i ∈ coordSet σ b ↔ σ i = b := by
  simp [coordSet]

theorem transvection_mem_coordBlockSL {J : Finset (Fin n)} {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J)
    (hij : i ≠ j) (c : k) : Matrix.SpecialLinearGroup.transvection hij c ∈ coordBlockSL k J := by
  rw [mem_coordBlockSL_iff]
  intro a b hab
  rw [CFSG.ClassicalInvolution.RouteD.Gaps.coe_transvection_eq]
  have hne : ¬ (i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    rcases hab with h | h
    · exact h hi
    · exact h hj
  simp [Matrix.add_apply, Matrix.one_apply, hne]

theorem slConjugation_diagGL_fixes_coordBlockSL (u : Fin n → kˣ) {J : Finset (Fin n)}
    (hu : ∀ i ∈ J, ∀ j ∈ J, u i = u j) {s : SpecialLinearGroup (Fin n) k}
    (hs : s ∈ coordBlockSL k J) : slConjugation n k (diagGL u) s = s := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply]
  by_cases hij : i ∈ J ∧ j ∈ J
  · rw [hu i hij.1 j hij.2, mul_right_comm, Units.mul_inv, one_mul]
  · have hor : i ∉ J ∨ j ∉ J := by
      by_contra h
      push Not at h
      exact hij h
    rw [(mem_coordBlockSL_iff.mp hs) i j hor]
    by_cases hij' : i = j
    · subst hij'
      simp
    · simp [hij']


theorem entry_eq_zero_of_fixed_signGL (h2 : (2 : k) ≠ 0) {σ : Fin n → Bool} {y : SL(n, k)}
    (hy : slConjugation n k (signGL k σ) y = y) {i j : Fin n} (hij : σ i ≠ σ j) :
    (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
  have h := congrArg (fun z : SL(n, k) => (z : Matrix (Fin n) (Fin n) k) i j) hy
  simp only [signGL, slConjugation_diagGL_apply] at h
  have key : -((y : Matrix (Fin n) (Fin n) k) i j) = (y : Matrix (Fin n) (Fin n) k) i j := by
    cases hi : σ i <;> cases hj : σ j
    · exact absurd (hi.trans hj.symm) hij
    · simpa [signUnit, hi, hj] using h
    · simpa [signUnit, hi, hj] using h
    · exact absurd (hi.trans hj.symm) hij
  have h2' : (2 : k) * (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
    linear_combination (-1 : k) * key
  exact (mul_eq_zero.mp h2').resolve_left h2

theorem compIndicator_comm_of_fixed_signGL (h2 : (2 : k) ≠ 0) {σ : Fin n → Bool}
    {y : SL(n, k)} (hy : slConjugation n k (signGL k σ) y = y) (b : Bool) :
    compIndicator k (coordSet σ b) * (y : Matrix (Fin n) (Fin n) k) =
      (y : Matrix (Fin n) (Fin n) k) * compIndicator k (coordSet σ b) := by
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hij : σ i = σ j
  · have : (i ∈ coordSet σ b) ↔ (j ∈ coordSet σ b) := by
      rw [mem_coordSet, mem_coordSet, hij]
    by_cases hi : i ∈ coordSet σ b
    · simp [hi, this.mp hi]
    · simp [hi, mt this.mpr hi]
  · rw [entry_eq_zero_of_fixed_signGL h2 hy hij]
    simp

theorem isComponentOf_block_centralizer [Finite k] (h2 : (2 : k) ≠ 0) (h4 : 4 ≤ Nat.card k)
    {X : Type} [Group X] (Ψ : SL(n, k) →* X) (hker : Ψ.ker ≤ Subgroup.center SL(n, k)) (f : X)
    (σ : Fin n → Bool)
    (hf : ∀ y, f * Ψ y * f⁻¹ = Ψ (slConjugation n k (signGL k σ) y)) (b : Bool)
    (hcard : 2 ≤ (coordSet σ b).card) :
    CFSG.Open.IsComponentOf ((coordBlockSL k (coordSet σ b)).map Ψ)
      (Ψ.range ⊓ Subgroup.centralizer ({f} : Set X)) := by
  have hQ : CFSG.Open.IsComponentOf (coordBlockSL k (coordSet σ b))
      (CFSG.ClassicalInvolution.Balance.fixedGroup (slConjugation n k (signGL k σ))) := by
    have hle : coordBlockSL k (coordSet σ b) ≤
        CFSG.ClassicalInvolution.Balance.fixedGroup (slConjugation n k (signGL k σ)) := by
      intro s hs
      rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup]
      refine slConjugation_diagGL_fixes_coordBlockSL _ ?_ hs
      intro i hi j hj
      rw [mem_coordSet] at hi hj
      rw [hi, hj]
    refine ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle ?_,
      isQuasisimple_coordBlockSL hcard h4⟩
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro s y hs hy
    exact conj_mem_coordBlockSL (compIndicator_comm_of_fixed_signGL h2
      (CFSG.ClassicalInvolution.Balance.mem_fixedGroup.mp hy) b) hs
  have hmain := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 f
    (slConjugation n k (signGL k σ)) (fun y => by simpa using hf y) hQ
  have e : (MulAut.conj (1 : SL(n, k))).toMonoidHom = MonoidHom.id _ := by
    ext; simp
  rwa [e, MonoidHom.comp_id] at hmain

end Sign

end CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
