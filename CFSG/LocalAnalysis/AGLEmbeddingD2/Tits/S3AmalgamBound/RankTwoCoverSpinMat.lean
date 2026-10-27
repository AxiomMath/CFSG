module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrthRank
public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.SpinRank

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin Matrix QuadraticMap

variable {n : ℕ} {F : Type} [Field F]

@[expose] def ix (i : Fin n) : Bool → Fin n ⊕ Fin n
  | true => .inl i
  | false => .inr i

theorem plusVec_eq_single (i : Fin n) (s : Bool) :
    plusVec n F i s = Pi.single (ix i s) 1 := by
  cases s <;> rfl

theorem polar_plusVec (v : Fin n ⊕ Fin n → F) (j : Fin n) (t : Bool) :
    polar (quadPlus n F) v (plusVec n F j t) = v (ix j (!t)) := by
  cases t
  · exact polar_quadPlus_single_inr n F v j
  · exact polar_quadPlus_single_inl n F v j

theorem spinMatrix_longRoot (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : F) :
    (spinMatrix (quadPlus n F) ((plusFrame n F hn).longRoot hij s t (.ofAdd c)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.single (ix i s) (ix j (!t)) (1 : F) -
        Matrix.single (ix j t) (ix i (!s)) (1 : F)) := by
  refine Matrix.ext_of_mulVec_single fun r => ?_
  rw [spinMatrix_mulVec, HypFrame.spinAction_longRoot, plusFrame_vec, polar_plusVec,
    polar_plusVec, plusVec_eq_single, plusVec_eq_single]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq, Matrix.single_mulVec_eq, smul_sub, smul_smul, smul_smul, sub_eq_add_neg,
    sub_eq_add_neg, add_assoc, one_mul, one_mul]


section Node

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [CharP F 2]

@[expose] noncomputable def nodeN (F : Type*) [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P1 P2 A B : ι) : Matrix ι ι F :=
  Matrix.single P1 A 1 + Matrix.single B P2 1 + Matrix.single A P1 1 + Matrix.single P2 B 1 +
    Matrix.single P1 P1 1 + Matrix.single B B 1

@[expose] def nodeS (P1 P2 A B : ι) : Finset ι := {P1, P2, A, B}

structure Distinct4 (P1 P2 A B : ι) : Prop where
  h12 : P1 ≠ P2
  h1A : P1 ≠ A
  h1B : P1 ≠ B
  h2A : P2 ≠ A
  h2B : P2 ≠ B
  hAB : A ≠ B

theorem nodeN_mulVec {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) (v : ι → F) (r : ι) :
    (nodeN F P1 P2 A B *ᵥ v) r =
      if r = P1 then v A + v P1 else if r = A then v P1 else if r = B then v P2 + v B
      else if r = P2 then v B else 0 := by
  obtain ⟨h12, h1A, h1B, h2A, h2B, hAB⟩ := hd
  simp only [nodeN, Matrix.add_mulVec, Matrix.single_mulVec_eq, Pi.add_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, one_mul, mul_one, mul_ite, mul_zero]
  by_cases a1 : r = P1
  · subst a1; simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm]
  by_cases a2 : r = A
  · subst a2; simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, hAB.symm]
  by_cases a3 : r = B
  · subst a3; simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2B.symm, hAB.symm]
  by_cases a4 : r = P2
  · subst a4; simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h2A.symm, h2B.symm]
  simp [a1, a2, a3, a4]

theorem card_nodeS {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) : (nodeS P1 P2 A B).card = 4 := by
  obtain ⟨h12, h1A, h1B, h2A, h2B, hAB⟩ := hd
  unfold nodeS
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simpa using hAB
  · simp [h2A, h2B]
  · simp [h1A, h1B, h12]

theorem nodeN_supp (P1 P2 A B : ι) (a b : ι) (h : nodeN F P1 P2 A B a b ≠ 0) :
    a ∈ nodeS P1 P2 A B ∧ b ∈ nodeS P1 P2 A B := by
  by_contra hc
  apply h
  simp only [nodeS, Finset.mem_insert, Finset.mem_singleton, not_and_or] at hc
  simp only [nodeN, Matrix.add_apply, Matrix.single_apply]
  rcases hc with hc | hc <;> push_neg at hc <;> obtain ⟨c1, c2, c3, c4⟩ := hc
  · simp [Ne.symm c1, Ne.symm c2, Ne.symm c3, Ne.symm c4]
  · simp [Ne.symm c1, Ne.symm c2, Ne.symm c3, Ne.symm c4]

theorem nodeN_inj {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) (v : ι → F)
    (hv : ∀ a ∉ nodeS P1 P2 A B, v a = 0)
    (h : ∀ a ∈ nodeS P1 P2 A B, (nodeN F P1 P2 A B *ᵥ v) a = 0) : ∀ a, v a = 0 := by
  have hd' := hd
  obtain ⟨h12, h1A, h1B, h2A, h2B, hAB⟩ := hd
  have e1 := h P1 (by simp [nodeS])
  have e2 := h A (by simp [nodeS])
  have e3 := h B (by simp [nodeS])
  have e4 := h P2 (by simp [nodeS])
  rw [nodeN_mulVec hd'] at e1 e2 e3 e4
  simp only [if_true, if_neg h1A.symm, if_neg h1B.symm, if_neg h12.symm, if_neg h2A.symm.symm,
    if_neg hAB, if_neg hAB.symm, if_neg h2B.symm, if_neg h2B, if_neg h2A, if_neg h1A, if_neg h1B,
    if_neg h12] at e1 e2 e3 e4
  have a1 : v P1 = 0 := e2
  have a2 : v B = 0 := e4
  have a3 : v A = 0 := by rw [a1, add_zero] at e1; exact e1
  have a4 : v P2 = 0 := by rw [a2, add_zero] at e3; exact e3
  intro a
  by_cases ha : a ∈ nodeS P1 P2 A B
  · simp only [nodeS, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  · exact hv a ha

theorem rank_nodeN {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) :
    (nodeN F P1 P2 A B).rank = 4 := by
  apply le_antisymm
  · refine (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth.rank_le_card_of_rowSupport
      _ (nodeS P1 P2 A B) ?_).trans (card_nodeS hd).le
    intro a ha b
    by_contra hne
    exact ha (nodeN_supp P1 P2 A B a b hne).1
  · rw [← card_nodeS hd]
    exact CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth.card_le_rank _ _
      (nodeN_inj hd)

theorem nodeN_mul_nodeN_disjoint {P1 P2 A B P1' P2' A' B' : ι}
    (hd : Disjoint (nodeS P1 P2 A B) (nodeS P1' P2' A' B')) :
    nodeN F P1 P2 A B * nodeN F P1' P2' A' B' = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : nodeN F P1 P2 A B a c = 0
  · simp [h1]
  by_cases h2 : nodeN F P1' P2' A' B' c b = 0
  · simp [h2]
  exact absurd (nodeN_supp P1' P2' A' B' c b h2).1
    (Finset.disjoint_left.1 hd (nodeN_supp P1 P2 A B a c h1).2)

theorem rank_add_nodeN_disjoint {P1 P2 A B P1' P2' A' B' : ι} (hd1 : Distinct4 P1 P2 A B)
    (hd2 : Distinct4 P1' P2' A' B')
    (hd : Disjoint (nodeS P1 P2 A B) (nodeS P1' P2' A' B')) :
    8 ≤ (nodeN F P1 P2 A B + nodeN F P1' P2' A' B').rank := by
  have h := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth.card_add_le_rank_add
    (nodeN F P1 P2 A B) (nodeN F P1' P2' A' B') _ _ hd (nodeN_supp P1 P2 A B)
    (nodeN_supp P1' P2' A' B') (nodeN_inj hd1) (nodeN_inj hd2)
  rw [card_nodeS hd1, card_nodeS hd2] at h
  exact h

theorem swap_mulVec {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) (v : ι → F) (r : ι) :
    ((nodeN F P1 P2 A B + nodeN F P1 P2 B A + nodeN F P1 P2 A B * nodeN F P1 P2 B A) *ᵥ v) r =
      if r = P1 then v P1 + v P2 else if r = A then v P2 + v A + v B
      else if r = B then v P2 + v A + v B else if r = P2 then v P1 + v A + v B else 0 := by
  have hd' : Distinct4 P1 P2 B A :=
    ⟨hd.h12, hd.h1B, hd.h1A, hd.h2B, hd.h2A, hd.hAB.symm⟩
  rw [Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply, Pi.add_apply]
  simp only [nodeN_mulVec hd, nodeN_mulVec hd']
  obtain ⟨h12, h1A, h1B, h2A, h2B, hAB⟩ := hd
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases a1 : r = P1
  · subst a1
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
    grind
  by_cases a2 : r = A
  · subst a2
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
    grind
  by_cases a3 : r = B
  · subst a3
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
    grind
  by_cases a4 : r = P2
  · subst a4
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
    grind
  simp [a1, a2, a3, a4]

theorem swap_mulVec_eq {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) (v : ι → F) :
    ((nodeN F P1 P2 A B + nodeN F P1 P2 B A + nodeN F P1 P2 A B * nodeN F P1 P2 B A) *ᵥ v) =
      (v P1 + v P2) • (Pi.single P1 (1 : F) + Pi.single A 1 + Pi.single B 1 : ι → F) +
        (v P1 + v A + v B) • (Pi.single P2 (1 : F) + Pi.single A 1 + Pi.single B 1 : ι → F) := by
  funext r
  rw [swap_mulVec hd]
  obtain ⟨h12, h1A, h1B, h2A, h2B, hAB⟩ := hd
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases a1 : r = P1
  · subst a1
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
  by_cases a2 : r = A
  · subst a2
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
    grind
  by_cases a3 : r = B
  · subst a3
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
    grind
  by_cases a4 : r = P2
  · subst a4
    simp [h12, h1A, h1B, h2A, h2B, hAB, h12.symm, h1A.symm, h1B.symm, h2A.symm, h2B.symm, hAB.symm]
  simp [a1, a2, a3, a4]

theorem rank_swap_le {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) :
    (nodeN F P1 P2 A B + nodeN F P1 P2 B A + nodeN F P1 P2 A B * nodeN F P1 P2 B A).rank ≤ 2 := by
  classical
  set M := nodeN F P1 P2 A B + nodeN F P1 P2 B A + nodeN F P1 P2 A B * nodeN F P1 P2 B A
  set u1 : ι → F := Pi.single P1 (1 : F) + Pi.single A 1 + Pi.single B 1
  set u2 : ι → F := Pi.single P2 (1 : F) + Pi.single A 1 + Pi.single B 1
  have hle : LinearMap.range M.mulVecLin ≤ Submodule.span F (↑({u1, u2} : Finset (ι → F))) := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, swap_mulVec_eq hd]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_insert_self _ _))))
      (Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
  calc M.rank = Module.finrank F (LinearMap.range M.mulVecLin) := rfl
    _ ≤ Module.finrank F (Submodule.span F (↑({u1, u2} : Finset (ι → F)))) :=
        Submodule.finrank_mono hle
    _ ≤ ({u1, u2} : Finset (ι → F)).card := finrank_span_finset_le_card _
    _ ≤ 2 := Finset.card_le_two

theorem rank_swap_pos {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) :
    1 ≤ (nodeN F P1 P2 A B + nodeN F P1 P2 B A + nodeN F P1 P2 A B * nodeN F P1 P2 B A).rank := by
  set M := nodeN F P1 P2 A B + nodeN F P1 P2 B A + nodeN F P1 P2 A B * nodeN F P1 P2 B A
  have hne : M *ᵥ Pi.single P1 1 ≠ 0 := by
    intro h
    have := congrFun h P1
    rw [swap_mulVec hd] at this
    simp [Pi.single_apply, Ne.symm hd.h12] at this
  have : (LinearMap.range M.mulVecLin) ≠ ⊥ := by
    intro hbot
    apply hne
    have : M.mulVecLin (Pi.single P1 1) ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact this
  exact Submodule.one_le_finrank_iff.2 this

theorem ubar_matrix_aux {P1 P2 A B : ι} (hd : Distinct4 P1 P2 A B) :
    (1 + (1 : F) • (Matrix.single P1 A (1 : F) - Matrix.single B P2 (1 : F))) *
      (1 + (1 : F) • (Matrix.single A P1 (1 : F) - Matrix.single P2 B (1 : F))) =
      1 + nodeN F P1 P2 A B := by
  have hneg : ∀ i j : ι, -(Matrix.single i j (1 : F)) = Matrix.single i j 1 := fun i j => by
    rw [Matrix.single_neg, CharTwo.neg_eq]
  have e1 : Matrix.single P1 A (1 : F) * Matrix.single P2 B 1 = 0 :=
    Matrix.single_mul_single_of_ne (1 : F) P1 A P2 hd.h2A.symm 1
  have e2 : Matrix.single B P2 (1 : F) * Matrix.single A P1 1 = 0 :=
    Matrix.single_mul_single_of_ne (1 : F) B P2 A hd.h2A 1
  simp only [one_smul, sub_eq_add_neg, hneg, mul_add, add_mul, one_mul, mul_one,
    Matrix.single_mul_single_same, e1, e2, mul_one, nodeN]
  abel

end Node


section Spin

variable [CharP F 2]

theorem distinct4_node (hn : 3 ≤ n) (k : Fin n) :
    Distinct4 (Sum.inl (rootIdxD n k) : Fin n ⊕ Fin n) (Sum.inr (rootIdxD n k))
      (ix (rootIdxD' n k) (!rootSignD n k)) (ix (rootIdxD' n k) (rootSignD n k)) := by
  have hpq : rootIdxD n k ≠ rootIdxD' n k := rootIdxD_ne n (by omega) k
  cases h : rootSignD n k <;> simp only [ix, Bool.not_true, Bool.not_false] <;>
  refine ⟨by simp, ?_, ?_, ?_, ?_, by simp⟩ <;> simp [hpq]

theorem spinMatrix_rootD (hn : 3 ≤ n) (k : Fin n) (c : F) :
    (spinMatrix (quadPlus n F) (rootD F hn k (.ofAdd c)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.single (Sum.inl (rootIdxD n k) : Fin n ⊕ Fin n)
          (ix (rootIdxD' n k) (!rootSignD n k)) (1 : F) -
        Matrix.single (ix (rootIdxD' n k) (rootSignD n k)) (Sum.inr (rootIdxD n k)) (1 : F)) :=
  spinMatrix_longRoot hn (rootIdxD_ne n (by omega) k) true (rootSignD n k) c

theorem spinMatrix_negRootD (hn : 3 ≤ n) (k : Fin n) (c : F) :
    (spinMatrix (quadPlus n F) (negRootD F hn k (.ofAdd c)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.single (ix (rootIdxD' n k) (!rootSignD n k))
          (Sum.inl (rootIdxD n k) : Fin n ⊕ Fin n) (1 : F) -
        Matrix.single (Sum.inr (rootIdxD n k) : Fin n ⊕ Fin n)
          (ix (rootIdxD' n k) (rootSignD n k)) (1 : F)) := by
  have := spinMatrix_longRoot (F := F) hn (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false c
  unfold negRootD
  simpa [ix] using this

end Spin

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.SpinRank
