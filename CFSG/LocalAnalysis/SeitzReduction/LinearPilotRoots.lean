module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def blockComplProj (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) K :=
  diagonal fun i => if i ∈ I then 0 else 1

theorem agrees_one_iff (I : Finset (Fin n)) (A : Matrix (Fin n) (Fin n) K) :
    (∀ i j, (i ∉ I ∨ j ∉ I) → A i j = (1 : Matrix (Fin n) (Fin n) K) i j) ↔
      A * blockComplProj I = blockComplProj I ∧ blockComplProj I * A = blockComplProj I := by
  simp only [blockComplProj, ← Matrix.ext_iff, mul_diagonal, diagonal_mul, diagonal_apply]
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · by_cases hj : j ∈ I
      · by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [hj, hij]
      · rw [h i j (Or.inr hj)]
        by_cases hij : i = j <;> simp [hj, hij, one_apply]
    · by_cases hi : i ∈ I
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hi, hij]
      · rw [h i j (Or.inl hi)]
        by_cases hij : i = j <;> simp [hi, hij, one_apply]
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have h := h2 i j
      clear h1 h2
      by_cases hij : i = j
      · subst hij; simpa [hi, one_apply] using h
      · simpa [hi, hij, one_apply] using h
    · have h := h1 i j
      clear h1 h2
      by_cases hij : i = j
      · subst hij; simpa [hj, one_apply] using h
      · simpa [hj, hij, one_apply] using h

@[expose] def blockSpecialLinear (I : Finset (Fin n)) :
    Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | ∀ i j, (i ∉ I ∨ j ∉ I) →
    (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_ofPred_eq, agrees_one_iff] at hA hB ⊢
    rw [SpecialLinearGroup.coe_mul]
    exact ⟨by rw [Matrix.mul_assoc, hB.1, hA.1], by rw [← Matrix.mul_assoc, hA.2, hB.2]⟩
  inv_mem' := by
    intro A hA
    simp only [Set.mem_ofPred_eq, agrees_one_iff] at hA ⊢
    have h1 : ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (A : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
    have h2 : (A : Matrix (Fin n) (Fin n) K) *
        ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hA.1, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    · conv_lhs => rw [← hA.2, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem mem_blockSpecialLinear {I : Finset (Fin n)} {A : SpecialLinearGroup (Fin n) K} :
    A ∈ blockSpecialLinear I ↔ ∀ i j, (i ∉ I ∨ j ∉ I) →
      (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j :=
  Iff.rfl

theorem mem_blockSpecialLinear_iff_mul {I : Finset (Fin n)} {A : SpecialLinearGroup (Fin n) K} :
    A ∈ blockSpecialLinear I ↔
      (A : Matrix (Fin n) (Fin n) K) * blockComplProj I = blockComplProj I ∧
        blockComplProj I * (A : Matrix (Fin n) (Fin n) K) = blockComplProj I :=
  agrees_one_iff I (A : Matrix (Fin n) (Fin n) K)

theorem blockSpecialLinear_mono {I J : Finset (Fin n)} (h : I ⊆ J) :
    blockSpecialLinear (K := K) I ≤ blockSpecialLinear J :=
  fun _ hA i j hij => hA i j (hij.imp (fun hi hiI => hi (h hiI)) (fun hj hjI => hj (h hjI)))

@[simp]
theorem blockSpecialLinear_empty : blockSpecialLinear (K := K) (∅ : Finset (Fin n)) = ⊥ :=
  eq_bot_iff.2 fun A hA => Subtype.ext (Matrix.ext fun i j => hA i j (Or.inl (by simp)))

@[simp]
theorem blockSpecialLinear_univ : blockSpecialLinear (K := K) (Finset.univ : Finset (Fin n)) = ⊤ :=
  eq_top_iff.2 fun _ _ i j hij => by simp at hij

theorem transvection_mem_blockSpecialLinear {I : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ I) (hj : j ∈ I) (c : K) :
    SpecialLinearGroup.transvection hij c ∈ blockSpecialLinear I := by
  intro k l hkl
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply]
  have : ¬ (i = k ∧ j = l) := by
    rintro ⟨rfl, rfl⟩
    rcases hkl with h | h
    · exact h hi
    · exact h hj
  rw [ite_eq_right this, add_zero]

@[expose] def blockMatrix (I : Finset (Fin n)) (A : Matrix I I K) : Matrix (Fin n) (Fin n) K :=
  reindex (Equiv.sumCompl (· ∈ I)) (Equiv.sumCompl (· ∈ I)) (fromBlocks A 0 0 1)

theorem blockMatrix_apply (I : Finset (Fin n)) (A : Matrix I I K) (i j : Fin n) :
    blockMatrix I A i j = if h : i ∈ I ∧ j ∈ I then A ⟨i, h.1⟩ ⟨j, h.2⟩
      else (1 : Matrix (Fin n) (Fin n) K) i j := by
  by_cases hi : i ∈ I <;> by_cases hj : j ∈ I
  · simp [blockMatrix, Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj,
      hi, hj]
  · have hne : i ≠ j := by rintro rfl; exact hj hi
    rw [dite_eq_right (fun h => hj h.2), one_apply_ne hne]
    simp [blockMatrix, Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj]
  · have hne : i ≠ j := by rintro rfl; exact hi hj
    rw [dite_eq_right (fun h => hi h.1), one_apply_ne hne]
    simp [blockMatrix, Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj]
  · rw [dite_eq_right (fun h => hi h.1)]
    simp only [blockMatrix, reindex_apply, submatrix_apply, Equiv.sumCompl_symm_apply_of_neg hi,
      Equiv.sumCompl_symm_apply_of_neg hj, fromBlocks_apply₂₂, one_apply, Subtype.mk.injEq]

theorem det_blockMatrix (I : Finset (Fin n)) (A : Matrix I I K) :
    (blockMatrix I A).det = A.det := by
  rw [blockMatrix, det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem blockMatrix_one (I : Finset (Fin n)) : blockMatrix I (1 : Matrix I I K) = 1 := by
  rw [blockMatrix, fromBlocks_one, reindex_apply, submatrix_one_equiv]

theorem blockMatrix_mul (I : Finset (Fin n)) (A B : Matrix I I K) :
    blockMatrix I (A * B) = blockMatrix I A * blockMatrix I B := by
  have h := (reindexAlgEquiv K K (Equiv.sumCompl (· ∈ I))).map_mul (fromBlocks A 0 0 1)
    (fromBlocks B 0 0 1)
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero,
    zero_add] at h
  exact h

@[expose] def blockEmbed (I : Finset (Fin n)) :
    SpecialLinearGroup I K →* SpecialLinearGroup (Fin n) K where
  toFun A := ⟨blockMatrix I A, by rw [det_blockMatrix]; exact A.prop⟩
  map_one' := Subtype.ext (blockMatrix_one I)
  map_mul' A B := Subtype.ext <| by
    change blockMatrix I ((A * B : SpecialLinearGroup I K) : Matrix I I K) =
      blockMatrix I A * blockMatrix I B
    rw [SpecialLinearGroup.coe_mul]
    exact blockMatrix_mul I A.1 B.1

@[simp]
theorem coe_blockEmbed (I : Finset (Fin n)) (A : SpecialLinearGroup I K) :
    ((blockEmbed I A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockMatrix I A :=
  rfl

theorem blockEmbed_injective (I : Finset (Fin n)) :
    Function.Injective (blockEmbed (K := K) I) := by
  intro A B h
  ext a b
  have := congrArg (fun M : SpecialLinearGroup (Fin n) K => (M : Matrix (Fin n) (Fin n) K) a b) h
  simpa [blockMatrix_apply] using this

theorem range_blockEmbed (I : Finset (Fin n)) :
    (blockEmbed (K := K) I).range = blockSpecialLinear I := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩ i j hij
    rw [coe_blockEmbed, blockMatrix_apply, dite_eq_right]
    rintro ⟨hi, hj⟩
    rcases hij with h | h
    · exact h hi
    · exact h hj
  · intro A hA
    set B : Matrix I I K := fun a b => (A : Matrix (Fin n) (Fin n) K) a b with hB
    have hAB : blockMatrix I B = A := by
      ext i j
      rw [blockMatrix_apply]
      split_ifs with h
      · rfl
      · exact (hA i j (not_and_or.1 h)).symm
    have hdet : B.det = 1 := by rw [← det_blockMatrix, hAB]; exact A.prop
    exact ⟨⟨B, hdet⟩, Subtype.ext hAB⟩

@[expose] def blockSL (I : Finset (Fin n)) : Subgroup (LinearFlag.projectiveSL n K) :=
  (blockSpecialLinear I).map (LinearFlag.proj n K)

@[expose] def rootSL2 (a b : Fin n) : Subgroup (LinearFlag.projectiveSL n K) :=
  blockSL {a, b}

theorem mem_blockSL {I : Finset (Fin n)} {x : LinearFlag.projectiveSL n K} :
    x ∈ blockSL I ↔ ∃ A ∈ blockSpecialLinear I, LinearFlag.proj n K A = x :=
  Subgroup.mem_map

theorem proj_mem_blockSL {I : Finset (Fin n)} {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ blockSpecialLinear I) : LinearFlag.proj n K A ∈ blockSL I :=
  Subgroup.mem_map_of_mem _ hA

theorem rootSL2_eq (a b : Fin n) : rootSL2 (K := K) a b = blockSL {a, b} :=
  rfl

theorem blockSL_eq_range (I : Finset (Fin n)) :
    blockSL (K := K) I = ((LinearFlag.proj n K).comp (blockEmbed I)).range := by
  rw [MonoidHom.range_comp, range_blockEmbed, blockSL]

theorem blockSL_mono {I J : Finset (Fin n)} (h : I ⊆ J) : blockSL (K := K) I ≤ blockSL J :=
  Subgroup.map_mono (blockSpecialLinear_mono h)

@[simp]
theorem blockSL_empty : blockSL (K := K) (∅ : Finset (Fin n)) = ⊥ := by
  rw [blockSL, blockSpecialLinear_empty, Subgroup.map_bot]

@[simp]
theorem blockSL_univ : blockSL (K := K) (Finset.univ : Finset (Fin n)) = ⊤ := by
  rw [blockSL, blockSpecialLinear_univ, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 (LinearFlag.proj_surjective n K)]

theorem proj_transvection_mem_blockSL {I : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ I) (hj : j ∈ I) (c : K) :
    LinearFlag.proj n K (SpecialLinearGroup.transvection hij c) ∈ blockSL I :=
  proj_mem_blockSL (transvection_mem_blockSpecialLinear hij hi hj c)

theorem proj_transvection_mem_rootSL2 {a b : Fin n} (hab : a ≠ b) (c : K) :
    LinearFlag.proj n K (SpecialLinearGroup.transvection hab c) ∈ rootSL2 a b :=
  proj_transvection_mem_blockSL hab (by simp) (by simp) c

theorem proj_transvection_mem_rootSL2' {a b : Fin n} (hab : a ≠ b) (c : K) :
    LinearFlag.proj n K (SpecialLinearGroup.transvection hab.symm c) ∈ rootSL2 a b :=
  proj_transvection_mem_blockSL hab.symm (by simp) (by simp) c

@[expose] def reindexSpecialLinear {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : SpecialLinearGroup ι K ≃* SpecialLinearGroup κ K where
  toFun A := ⟨reindex e e A.1, by rw [det_reindex_self]; exact A.2⟩
  invFun A := ⟨reindex e.symm e.symm A.1, by rw [det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv A := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext ((reindexAlgEquiv K K e).map_mul A.1 B.1)

theorem proj_comp_blockEmbed_injective {I : Finset (Fin n)} (hI : I.card < n) :
    Function.Injective ((LinearFlag.proj n K).comp (blockEmbed I)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.comp_apply, LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at hA
  obtain ⟨c, -, hc⟩ := hA
  obtain ⟨j, -, hj⟩ : ∃ j, j ∈ (Finset.univ : Finset (Fin n)) ∧ j ∉ I :=
    Finset.exists_mem_notMem_of_card_lt_card (by simpa using hI)
  have hjj := congrFun (congrFun hc j) j
  rw [coe_blockEmbed, blockMatrix_apply, dite_eq_right (fun h => hj h.1), one_apply_eq] at hjj
  have hc1 : (c : K) = 1 := by simpa using hjj.symm
  apply blockEmbed_injective I
  rw [map_one]
  refine Subtype.ext ?_
  rw [hc, hc1, map_one, SpecialLinearGroup.coe_one]

theorem blockSL_mulEquiv {I : Finset (Fin n)} (hI : I.card < n) :
    Nonempty (blockSL (K := K) I ≃* SpecialLinearGroup (Fin I.card) K) :=
  ⟨(MulEquiv.subgroupCongr (blockSL_eq_range I)).trans
    ((MonoidHom.ofInjective (proj_comp_blockEmbed_injective hI)).symm.trans
      (reindexSpecialLinear I.equivFin))⟩

theorem rootSL2_mulEquiv {a b : Fin n} (hab : a ≠ b) (hn : 3 ≤ n) :
    Nonempty (rootSL2 (K := K) a b ≃* SpecialLinearGroup (Fin 2) K) := by
  have hcard : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair hab
  obtain ⟨e⟩ := blockSL_mulEquiv (K := K) (I := {a, b}) (by omega)
  exact ⟨e.trans (reindexSpecialLinear (finCongr hcard))⟩

theorem rootSL2_le_blockSL {I : Finset (Fin n)} {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I) :
    rootSL2 (K := K) a b ≤ blockSL I :=
  blockSL_mono (Finset.insert_subset ha (Finset.singleton_subset_iff.2 hb))

theorem rootSL2_comm (a b : Fin n) : rootSL2 (K := K) a b = rootSL2 b a := by
  rw [rootSL2, rootSL2, Finset.pair_comm]

theorem sub_one_mul_sub_one_eq_zero {I J : Finset (Fin n)} (h : Disjoint I J)
    {A B : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I)
    (hB : B ∈ blockSpecialLinear J) :
    ((A : Matrix (Fin n) (Fin n) K) - 1) * ((B : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [Matrix.sub_apply]
  by_cases hk : k ∈ I
  · rw [hB k j (Or.inl (Finset.disjoint_left.1 h hk)), sub_self, mul_zero]
  · rw [hA i k (Or.inr hk), sub_self, zero_mul]

theorem commute_blockSpecialLinear_of_disjoint {I J : Finset (Fin n)} (h : Disjoint I J)
    {A B : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I)
    (hB : B ∈ blockSpecialLinear J) : Commute A B := by
  have h1 := sub_one_mul_sub_one_eq_zero h hA hB
  have h2 := sub_one_mul_sub_one_eq_zero h.symm hB hA
  show A * B = B * A
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
  set a := (A : Matrix (Fin n) (Fin n) K)
  set b := (B : Matrix (Fin n) (Fin n) K)
  calc a * b = (a - 1) * (b - 1) + a + b - 1 := by noncomm_ring
    _ = (b - 1) * (a - 1) + b + a - 1 := by rw [h1, h2]; abel
    _ = b * a := by noncomm_ring

theorem commute_blockSL_of_disjoint {I J : Finset (Fin n)} (h : Disjoint I J) :
    ∀ x ∈ blockSL (K := K) I, ∀ y ∈ blockSL (K := K) J, Commute x y := by
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  exact (commute_blockSpecialLinear_of_disjoint h hA hB).map _

theorem map_conj_blockSpecialLinear_of_mul_eq {I J : Finset (Fin n)}
    (g : SpecialLinearGroup (Fin n) K)
    (hg : blockComplProj J * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj I) :
    (blockSpecialLinear I).map (MulAut.conj g).toMonoidHom = blockSpecialLinear J := by
  set P := blockComplProj (K := K) I
  set Q := blockComplProj (K := K) J
  set G := (g : Matrix (Fin n) (Fin n) K)
  set G' := ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have h1 : G' * G = 1 := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  have h2 : G * G' = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  have hg' : G' * Q = P * G' := by
    calc G' * Q = G' * Q * (G * G') := by rw [h2, Matrix.mul_one]
      _ = G' * (Q * G) * G' := by simp only [Matrix.mul_assoc]
      _ = G' * (G * P) * G' := by rw [hg]
      _ = P * G' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hQ : G * P * G' = Q := by rw [← hg, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hP : G' * Q * G = P := by rw [hg', Matrix.mul_assoc, h1, Matrix.mul_one]
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    rw [SetLike.mem_coe, mem_blockSpecialLinear_iff_mul] at hA
    rw [mem_blockSpecialLinear_iff_mul]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SpecialLinearGroup.coe_mul]
    refine ⟨?_, ?_⟩
    · calc G * ↑A * G' * Q = G * (↑A * (G' * Q)) := by simp only [Matrix.mul_assoc]
        _ = G * (↑A * P) * G' := by rw [hg']; simp only [Matrix.mul_assoc]
        _ = Q := by rw [hA.1, hQ]
    · calc Q * (G * ↑A * G') = Q * G * ↑A * G' := by simp only [Matrix.mul_assoc]
        _ = G * (P * ↑A) * G' := by rw [hg]; simp only [Matrix.mul_assoc]
        _ = Q := by rw [hA.2, hQ]
  · intro B hB
    rw [mem_blockSpecialLinear_iff_mul] at hB
    refine ⟨g⁻¹ * B * g, ?_, by simp [mul_assoc]⟩
    rw [SetLike.mem_coe, mem_blockSpecialLinear_iff_mul, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_mul]
    refine ⟨?_, ?_⟩
    · calc G' * ↑B * G * P = G' * (↑B * (G * P)) := by simp only [Matrix.mul_assoc]
        _ = G' * (↑B * Q) * G := by rw [← hg]; simp only [Matrix.mul_assoc]
        _ = P := by rw [hB.1, hP]
    · calc P * (G' * ↑B * G) = P * G' * ↑B * G := by simp only [Matrix.mul_assoc]
        _ = G' * (Q * ↑B) * G := by rw [← hg']; simp only [Matrix.mul_assoc]
        _ = P := by rw [hB.2, hP]

theorem map_conj_blockSL_of_mul_eq {I J : Finset (Fin n)} (g : SpecialLinearGroup (Fin n) K)
    (hg : blockComplProj J * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj I) :
    (blockSL I).map (MulAut.conj (LinearFlag.proj n K g)).toMonoidHom = blockSL J := by
  have hcomp : (MulAut.conj (LinearFlag.proj n K g)).toMonoidHom.comp (LinearFlag.proj n K) =
      (LinearFlag.proj n K).comp (MulAut.conj g).toMonoidHom :=
    MonoidHom.ext fun A => by simp [MulAut.conj_apply, map_mul, map_inv]
  rw [blockSL, blockSL, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    map_conj_blockSpecialLinear_of_mul_eq g hg]

theorem blockComplProj_mul_permMatrix (σ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    blockComplProj (K := K) (I.map σ.symm.toEmbedding) * σ.permMatrix K =
      σ.permMatrix K * blockComplProj I := by
  ext i j
  simp only [blockComplProj, diagonal_mul, mul_diagonal, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Finset.mem_map_equiv, Equiv.symm_symm]
  by_cases h : σ i = j
  · subst h; simp
  · simp [h]

private def signDiag (σ : Equiv.Perm (Fin n)) (i₀ : Fin n) : Matrix (Fin n) (Fin n) K :=
  diagonal (Function.update 1 i₀ ((Equiv.Perm.sign σ : ℤ) : K))

private theorem det_permMatrix_mul_signDiag (σ : Equiv.Perm (Fin n)) (i₀ : Fin n) :
    (σ.permMatrix K * signDiag σ i₀).det = 1 := by
  rw [det_mul, det_permutation, signDiag, det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ _)]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

private theorem blockComplProj_mul_signDiag (σ : Equiv.Perm (Fin n)) (i₀ : Fin n)
    (I : Finset (Fin n)) :
    blockComplProj (K := K) I * signDiag σ i₀ = signDiag σ i₀ * blockComplProj I := by
  rw [blockComplProj, signDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem exists_conj_blockSpecialLinear (σ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    ∃ g : SpecialLinearGroup (Fin n) K,
      (blockSpecialLinear I).map (MulAut.conj g).toMonoidHom =
        blockSpecialLinear (I.map σ.toEmbedding) ∧
      blockComplProj (I.map σ.toEmbedding) * (g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * blockComplProj I := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hI : I.map σ.toEmbedding = I := Subsingleton.elim _ _
    refine ⟨1, ?_, ?_⟩
    · rw [hI, map_one]
      exact Subgroup.map_id _
    · rw [hI, SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul]
  · set τ : Equiv.Perm (Fin n) := σ.symm
    let i₀ : Fin n := ⟨0, hn⟩
    let g : SpecialLinearGroup (Fin n) K :=
      ⟨τ.permMatrix K * signDiag τ i₀, det_permMatrix_mul_signDiag τ i₀⟩
    have hg : blockComplProj (I.map σ.toEmbedding) * (g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * blockComplProj I := by
      have h := blockComplProj_mul_permMatrix (K := K) τ I
      rw [show τ.symm = σ from Equiv.symm_symm σ] at h
      change blockComplProj (I.map σ.toEmbedding) * (τ.permMatrix K * signDiag τ i₀) =
        τ.permMatrix K * signDiag τ i₀ * blockComplProj I
      rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, blockComplProj_mul_signDiag,
        ← Matrix.mul_assoc]
    exact ⟨g, map_conj_blockSpecialLinear_of_mul_eq g hg, hg⟩

theorem exists_conj_blockSL (σ : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    ∃ g : LinearFlag.projectiveSL n K,
      (blockSL I).map (MulAut.conj g).toMonoidHom = blockSL (I.map σ.toEmbedding) := by
  obtain ⟨g, -, hg⟩ := exists_conj_blockSpecialLinear (K := K) σ I
  exact ⟨LinearFlag.proj n K g, map_conj_blockSL_of_mul_eq g hg⟩

theorem exists_perm_apply_eq_apply_eq {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin n), σ a = c ∧ σ b = d := by
  set σ₁ := Equiv.swap a c
  have h1 : σ₁ b ≠ c := by
    intro h
    apply hab
    have : σ₁ b = σ₁ a := by rw [h, Equiv.swap_apply_left]
    exact (σ₁.injective this).symm
  refine ⟨σ₁.trans (Equiv.swap (σ₁ b) d), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h1.symm hcd]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem exists_conj_rootSL2 (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : LinearFlag.projectiveSL n K,
      (rootSL2 a b).map (MulAut.conj g).toMonoidHom = rootSL2 c d := by
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_apply_eq_apply_eq hab hcd
  obtain ⟨g, hg⟩ := exists_conj_blockSL (K := K) σ {a, b}
  refine ⟨g, ?_⟩
  rw [rootSL2, hg, rootSL2, Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, hσa,
    hσb]

theorem blockEmbed_transvection (I : Finset (Fin n)) {i j : I} (hij : i ≠ j) (c : K) :
    blockEmbed I (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (fun h => hij (Subtype.ext h)) c := by
  ext k l
  rw [coe_blockEmbed, blockMatrix_apply]
  by_cases h : k ∈ I ∧ l ∈ I
  · rw [dite_eq_left h]
    simp [SpecialLinearGroup.transvection_coe, single_apply, one_apply, Subtype.ext_iff]
  · rw [dite_eq_right h]
    simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply]
    rw [ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact h ⟨i.2, j.2⟩

theorem blockSpecialLinear_eq_closure (I : Finset (Fin n)) :
    blockSpecialLinear (K := K) I = Subgroup.closure {A | ∃ (i j : Fin n) (hij : i ≠ j) (c : K),
      i ∈ I ∧ j ∈ I ∧ SpecialLinearGroup.transvection hij c = A} := by
  apply le_antisymm
  · rw [← range_blockEmbed, MonoidHom.range_eq_map,
      ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t.i, t.j, fun h => t.hij (Subtype.ext h), t.c, t.i.2, t.j.2,
      (blockEmbed_transvection I t.hij t.c).symm⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
    exact transvection_mem_blockSpecialLinear hij hi hj c

theorem blockSL_eq_closure (I : Finset (Fin n)) :
    blockSL (K := K) I = Subgroup.closure {x | ∃ (i j : Fin n) (hij : i ≠ j) (c : K),
      i ∈ I ∧ j ∈ I ∧ LinearFlag.proj n K (SpecialLinearGroup.transvection hij c) = x} := by
  rw [blockSL, blockSpecialLinear_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, j, hij, c, hi, hj, rfl⟩, rfl⟩
    exact ⟨i, j, hij, c, hi, hj, rfl⟩
  · rintro ⟨i, j, hij, c, hi, hj, rfl⟩
    exact ⟨_, ⟨i, j, hij, c, hi, hj, rfl⟩, rfl⟩

@[expose] def pairEquiv {a b : Fin n} (hab : a ≠ b) : Fin 2 ≃ ({a, b} : Finset (Fin n)) where
  toFun i := if i = 0 then ⟨a, by simp⟩ else ⟨b, by simp⟩
  invFun x := if (x : Fin n) = a then 0 else 1
  left_inv i := by fin_cases i <;> simp [hab.symm]
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hab.symm]

theorem pairEquiv_symm_apply {a b : Fin n} (hab : a ≠ b) (x : ({a, b} : Finset (Fin n))) :
    (pairEquiv hab).symm x = if (x : Fin n) = a then 0 else 1 :=
  rfl

@[expose] def pairEmbed {a b : Fin n} (hab : a ≠ b) :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin n) K :=
  (blockEmbed {a, b}).comp (reindexSpecialLinear (pairEquiv hab)).toMonoidHom

theorem pairEmbed_apply {a b : Fin n} (hab : a ≠ b) (A : SpecialLinearGroup (Fin 2) K)
    (i j : Fin n) :
    (pairEmbed hab A : Matrix (Fin n) (Fin n) K) i j =
      if (i ∈ ({a, b} : Finset (Fin n)) ∧ j ∈ ({a, b} : Finset (Fin n))) then
        (A : Matrix (Fin 2) (Fin 2) K) (if i = a then 0 else 1) (if j = a then 0 else 1)
      else (1 : Matrix (Fin n) (Fin n) K) i j := by
  rw [pairEmbed, MonoidHom.comp_apply, coe_blockEmbed, blockMatrix_apply]
  by_cases h : i ∈ ({a, b} : Finset (Fin n)) ∧ j ∈ ({a, b} : Finset (Fin n))
  · rw [dite_eq_left h, ite_eq_left h]
    rfl
  · rw [dite_eq_right h, ite_eq_right h]

@[simp]
theorem pairEmbed_apply_left_left {a b : Fin n} (hab : a ≠ b) (A : SpecialLinearGroup (Fin 2) K) :
    (pairEmbed hab A : Matrix (Fin n) (Fin n) K) a a = (A : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  simp [pairEmbed_apply]

@[simp]
theorem pairEmbed_apply_left_right {a b : Fin n} (hab : a ≠ b)
    (A : SpecialLinearGroup (Fin 2) K) :
    (pairEmbed hab A : Matrix (Fin n) (Fin n) K) a b = (A : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  simp [pairEmbed_apply, hab.symm]

@[simp]
theorem pairEmbed_apply_right_left {a b : Fin n} (hab : a ≠ b)
    (A : SpecialLinearGroup (Fin 2) K) :
    (pairEmbed hab A : Matrix (Fin n) (Fin n) K) b a = (A : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  simp [pairEmbed_apply, hab.symm]

@[simp]
theorem pairEmbed_apply_right_right {a b : Fin n} (hab : a ≠ b)
    (A : SpecialLinearGroup (Fin 2) K) :
    (pairEmbed hab A : Matrix (Fin n) (Fin n) K) b b = (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  simp [pairEmbed_apply, hab.symm]

theorem pairEmbed_apply_of_notMem {a b : Fin n} (hab : a ≠ b) (A : SpecialLinearGroup (Fin 2) K)
    {i j : Fin n} (h : i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) :
    (pairEmbed hab A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  rw [pairEmbed_apply, ite_eq_right (fun h' => h.elim (· h'.1) (· h'.2))]

theorem pairEmbed_injective {a b : Fin n} (hab : a ≠ b) :
    Function.Injective (pairEmbed (K := K) hab) :=
  (blockEmbed_injective _).comp (MulEquiv.injective _)

theorem range_pairEmbed {a b : Fin n} (hab : a ≠ b) :
    (pairEmbed (K := K) hab).range = blockSpecialLinear {a, b} := by
  rw [pairEmbed, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (MulEquiv.surjective (reindexSpecialLinear (pairEquiv hab))),
    ← MonoidHom.range_eq_map, range_blockEmbed]

theorem rootSL2_eq_range_pairEmbed {a b : Fin n} (hab : a ≠ b) :
    rootSL2 (K := K) a b = ((LinearFlag.proj n K).comp (pairEmbed hab)).range := by
  rw [MonoidHom.range_comp, range_pairEmbed]
  rfl

theorem proj_pairEmbed_mem_rootSL2 {a b : Fin n} (hab : a ≠ b) (A : SpecialLinearGroup (Fin 2) K) :
    LinearFlag.proj n K (pairEmbed hab A) ∈ rootSL2 a b := by
  rw [rootSL2_eq_range_pairEmbed hab]
  exact ⟨A, rfl⟩

theorem proj_comp_pairEmbed_injective {a b : Fin n} (hab : a ≠ b) (hn : 3 ≤ n) :
    Function.Injective ((LinearFlag.proj n K).comp (pairEmbed hab)) :=
  (proj_comp_blockEmbed_injective (I := {a, b}) (by rw [Finset.card_pair hab]; omega)).comp
    (MulEquiv.injective _)

theorem pairEmbed_transvection_zero_one {a b : Fin n} (hab : a ≠ b) (c : K) :
    pairEmbed hab (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      SpecialLinearGroup.transvection hab c := by
  ext i j
  by_cases h : i ∈ ({a, b} : Finset (Fin n)) ∧ j ∈ ({a, b} : Finset (Fin n))
  · obtain ⟨hi, hj⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [SpecialLinearGroup.transvection_coe, one_apply, hab, hab.symm]
  · rw [pairEmbed_apply_of_notMem hab _ (not_and_or.1 h)]
    exact (transvection_mem_blockSpecialLinear hab (by simp) (by simp) c i j
      (not_and_or.1 h)).symm

theorem pairEmbed_transvection_one_zero {a b : Fin n} (hab : a ≠ b) (c : K) :
    pairEmbed hab (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      SpecialLinearGroup.transvection hab.symm c := by
  ext i j
  by_cases h : i ∈ ({a, b} : Finset (Fin n)) ∧ j ∈ ({a, b} : Finset (Fin n))
  · obtain ⟨hi, hj⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [SpecialLinearGroup.transvection_coe, one_apply, hab, hab.symm]
  · rw [pairEmbed_apply_of_notMem hab _ (not_and_or.1 h)]
    exact (transvection_mem_blockSpecialLinear hab.symm (by simp) (by simp) c i j
      (not_and_or.1 h)).symm

end CFSG.SeitzReduction.LinearPilot
