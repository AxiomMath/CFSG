module

public import CFSG.LieType.Ree.SmallReeThreeData

public noncomputable section

namespace CFSG.LieType.Ree

open Equiv

theorem pdigit_penc {l : List ℕ} (hl : ∀ x ∈ l, x < 64) (j : ℕ) :
    pdigit (penc l) j = l.getD j 0 := by
  induction l generalizing j with
  | nil => simp [penc, pdigit]
  | cons x l ih =>
    have hx : x < 64 := hl x List.mem_cons_self
    have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    cases j with
    | zero => simp [penc, pdigit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ j =>
      rw [List.getD_cons_succ, ← ih' j, pdigit, pdigit, pow_succ', ← Nat.div_div_eq_div_mul, penc,
        Nat.add_mul_div_left _ _ (by norm_num : 0 < 64), Nat.div_eq_of_lt hx, zero_add]

@[expose] def permCode (σ : Perm (Fin 56)) : ℕ :=
  penc (List.ofFn fun i => (σ i : ℕ))

theorem pdigit_permCode (σ : Perm (Fin 56)) (i : Fin 56) : pdigit (permCode σ) i = σ i := by
  rw [permCode, pdigit_penc]
  · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact (σ j).2.trans (by norm_num)

theorem permCode_injective : Function.Injective permCode := fun σ τ h =>
  Equiv.ext fun i => Fin.ext (by rw [← pdigit_permCode, h, pdigit_permCode])

theorem permCode_mul (σ τ : Perm (Fin 56)) :
    permCode (σ * τ) = cmul (permCode σ) (permCode τ) := by
  rw [cmul, permCode]
  congr 1
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  have hi : i < 56 := by simpa using h₁
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  have e := pdigit_permCode τ ⟨i, hi⟩
  simp only at e
  rw [e, pdigit_permCode σ (τ ⟨i, hi⟩), Perm.mul_apply]

theorem permCode_one : permCode 1 = penc (List.range 56) :=
  congrArg penc (by decide +kernel)

@[expose] def listPerm (l l' : List ℕ) (h : srPermPairCheck l l' = true) : Perm (Fin 56) where
  toFun i := ⟨l.getD i 0 % 56, Nat.mod_lt _ (by norm_num)⟩
  invFun i := ⟨l'.getD i 0 % 56, Nat.mod_lt _ (by norm_num)⟩
  left_inv i := by
    simp only [srPermPairCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      Nat.blt_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.2 i i.2
    ext
    simp only [Nat.mod_eq_of_lt h1, h3, Nat.mod_eq_of_lt i.2]
  right_inv i := by
    simp only [srPermPairCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      Nat.blt_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.2 i i.2
    ext
    simp only [Nat.mod_eq_of_lt h2, h4, Nat.mod_eq_of_lt i.2]

@[expose] def srSigma0 : Perm (Fin 56) :=
  listPerm srPermU0 srPermU0Inv srPermPairCheck_u0

@[expose] def srSigmaN : Perm (Fin 56) :=
  listPerm srPermN srPermNInv srPermPairCheck_n

@[expose] def srSigma1 : Perm (Fin 56) :=
  listPerm srPermU1 srPermU1Inv srPermPairCheck_u1

theorem permCode_srSigma0 : permCode srSigma0 = penc srPermU0 :=
  congrArg penc (by decide +kernel)

theorem permCode_srSigma0_inv : permCode srSigma0⁻¹ = penc srPermU0Inv :=
  congrArg penc (by decide +kernel)

theorem permCode_srSigmaN : permCode srSigmaN = penc srPermN :=
  congrArg penc (by decide +kernel)

theorem permCode_srSigmaN_inv : permCode srSigmaN⁻¹ = penc srPermNInv :=
  congrArg penc (by decide +kernel)

theorem permCode_srSigma1 : permCode srSigma1 = penc srPermU1 :=
  congrArg penc (by decide +kernel)

@[expose] def srP : Subgroup (Perm (Fin 56)) :=
  Subgroup.closure {srSigma0, srSigmaN}

theorem forall_lt_of_chunks {p : ℕ → Bool} (h0 : (List.range' 0 (63 - 0)).all p = true)
    (h1 : (List.range' 63 (126 - 63)).all p = true)
    (h2 : (List.range' 126 (189 - 126)).all p = true)
    (h3 : (List.range' 189 (252 - 189)).all p = true)
    (h4 : (List.range' 252 (315 - 252)).all p = true)
    (h5 : (List.range' 315 (378 - 315)).all p = true)
    (h6 : (List.range' 378 (441 - 378)).all p = true)
    (h7 : (List.range' 441 (504 - 441)).all p = true) {k : ℕ} (hk : k < 504) : p k = true := by
  have key : ∀ a b, (List.range' a (b - a)).all p = true → a ≤ k → k < b → p k = true :=
    fun a b h ha hb => List.all_eq_true.1 h k (List.mem_range'_1.2 ⟨ha, by omega⟩)
  by_cases k < 63
  · exact key 0 63 h0 (by omega) (by omega)
  by_cases k < 126
  · exact key 63 126 h1 (by omega) (by omega)
  by_cases k < 189
  · exact key 126 189 h2 (by omega) (by omega)
  by_cases k < 252
  · exact key 189 252 h3 (by omega) (by omega)
  by_cases k < 315
  · exact key 252 315 h4 (by omega) (by omega)
  by_cases k < 378
  · exact key 315 378 h5 (by omega) (by omega)
  by_cases k < 441
  · exact key 378 441 h6 (by omega) (by omega)
  exact key 441 504 h7 (by omega) hk

theorem srHead : srEltCodes.length = 504 ∧ srCode 0 = penc (List.range 56) ∧ srReps.length = 9 ∧
    srReps.getD 0 0 = 0 ∧ ∀ r ∈ srReps, r < 504 := by
  have h := srHeadCheck_eq
  simp only [srHeadCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem srCode_mem {k : ℕ} (hk : k < 504) : srCode k ∈ srEltCodes := by
  rw [srCode, List.getD_eq_getElem _ _ (srHead.1 ▸ hk)]
  exact List.getElem_mem _

theorem exists_srCode_eq {c : ℕ} (hc : c ∈ srEltCodes) : ∃ k < 504, srCode k = c := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
  exact ⟨k, srHead.1 ▸ hk, List.getD_eq_getElem _ _ hk⟩

theorem srClosure {k : ℕ} (hk : k < 504) {g : ℕ} (hg : g ∈ srGenCodes) :
    cmul (srCode k) g ∈ srEltCodes := by
  have h := forall_lt_of_chunks (p := fun k => srGenCodes.all fun g =>
    srEltCodes.contains (cmul (srCode k) g)) srClosureChunk_0 srClosureChunk_1 srClosureChunk_2
    srClosureChunk_3 srClosureChunk_4 srClosureChunk_5 srClosureChunk_6 srClosureChunk_7 hk
  simpa using List.all_eq_true.1 h g hg

theorem srBFS {k : ℕ} (hk : k < 504) (hk0 : k ≠ 0) :
    srPar.getD k 0 < k ∧ srGen.getD k 0 < 2 ∧
      srCode k = cmul (srCode (srPar.getD k 0)) (srGenCodes.getD (srGen.getD k 0) 0) := by
  have h := forall_lt_of_chunks (p := fun k => k == 0 || (Nat.blt (srPar.getD k 0) k &&
    Nat.blt (srGen.getD k 0) 2 &&
      srCode k == cmul (srCode (srPar.getD k 0)) (srGenCodes.getD (srGen.getD k 0) 0)))
    srBFSChunk_0 srBFSChunk_1 srBFSChunk_2 srBFSChunk_3 srBFSChunk_4 srBFSChunk_5 srBFSChunk_6
    srBFSChunk_7 hk
  simp only [Bool.or_eq_true, beq_iff_eq, hk0, false_or, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_drop_of_lt {l : List ℕ} {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    l.getD j 0 ∈ l.drop (i + 1) := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x l ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [List.getD_cons_succ, List.drop_succ_cons]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [List.drop_zero, List.getD_eq_getElem _ _ (by simpa using hj)]
        exact List.getElem_mem _
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hi
        have := ih (i := i) (j := j) (by omega) (by simpa using hj)
        simpa using this

theorem srCode_injective {i j : ℕ} (hi : i < 504) (hj : j < 504) (h : srCode i = srCode j) :
    i = j := by
  have key : ∀ {i j : ℕ}, i < j → j < 504 → srCode i ≠ srCode j := by
    intro i j hij hj h
    have hd := forall_lt_of_chunks (p := fun k =>
      (srEltCodes.drop (k + 1)).all fun c => c != srCode k) srDistinctChunk_0 srDistinctChunk_1
      srDistinctChunk_2 srDistinctChunk_3 srDistinctChunk_4 srDistinctChunk_5 srDistinctChunk_6
      srDistinctChunk_7 (hij.trans hj)
    have hmem : srCode j ∈ srEltCodes.drop (i + 1) :=
      mem_drop_of_lt hij (srHead.1.symm ▸ hj)
    have := List.all_eq_true.1 hd _ hmem
    simp [h] at this
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h (key hij hj)
  · rfl
  · exact absurd h.symm (key hij hi)

theorem permCode_mem_of_mem_srP {x : Perm (Fin 56)} (hx : x ∈ srP) : permCode x ∈ srEltCodes := by
  induction hx using Subgroup.closure_induction_right with
  | one => rw [permCode_one, ← srHead.2.1]; exact srCode_mem (by norm_num)
  | mul_right x _ y hy ih =>
    obtain ⟨k, hk, hkc⟩ := exists_srCode_eq ih
    rw [permCode_mul, ← hkc]
    refine srClosure hk ?_
    rcases hy with rfl | rfl
    · simp [srGenCodes, permCode_srSigma0]
    · simp [srGenCodes, permCode_srSigmaN]
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨k, hk, hkc⟩ := exists_srCode_eq ih
    rw [permCode_mul, ← hkc]
    refine srClosure hk ?_
    rcases hy with rfl | rfl
    · simp [srGenCodes, permCode_srSigma0_inv]
    · simp [srGenCodes, permCode_srSigmaN_inv]

theorem exists_mem_srP_permCode {k : ℕ} (hk : k < 504) : ∃ x ∈ srP, permCode x = srCode k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, one_mem _, by rw [permCode_one, srHead.2.1]⟩
    · obtain ⟨hpar, hgen, heq⟩ := srBFS hk hpos.ne'
      obtain ⟨x, hx, hxc⟩ := ih _ hpar (hpar.trans hk)
      obtain ⟨y, hy, hyc⟩ : ∃ y ∈ ({srSigma0, srSigmaN} : Set (Perm (Fin 56))),
          permCode y = srGenCodes.getD (srGen.getD k 0) 0 := by
        rcases (by omega : srGen.getD k 0 = 0 ∨ srGen.getD k 0 = 1) with h0 | h1
        · exact ⟨srSigma0, Set.mem_insert _ _, by rw [h0, permCode_srSigma0]; rfl⟩
        · exact ⟨srSigmaN, Set.mem_insert_of_mem _ rfl, by rw [h1, permCode_srSigmaN]; rfl⟩
      exact ⟨x * y, mul_mem hx (Subgroup.subset_closure hy), by rw [permCode_mul, hxc, hyc, heq]⟩

@[expose] def srX (k : ℕ) : Perm (Fin 56) :=
  if h : k < 504 then (exists_mem_srP_permCode h).choose else 1

theorem srX_mem (k : ℕ) : srX k ∈ srP := by
  unfold srX
  split_ifs with h
  · exact (exists_mem_srP_permCode h).choose_spec.1
  · exact one_mem _

theorem permCode_srX {k : ℕ} (hk : k < 504) : permCode (srX k) = srCode k := by
  unfold srX
  rw [dite_eq_left hk]
  exact (exists_mem_srP_permCode hk).choose_spec.2

theorem srX_zero : srX 0 = 1 :=
  permCode_injective (by rw [permCode_srX (by norm_num), permCode_one, srHead.2.1])

theorem exists_srX_eq {x : Perm (Fin 56)} (hx : x ∈ srP) : ∃ k < 504, srX k = x := by
  obtain ⟨k, hk, hkc⟩ := exists_srCode_eq (permCode_mem_of_mem_srP hx)
  exact ⟨k, hk, permCode_injective (by rw [permCode_srX hk, hkc])⟩

@[expose] def srXP (k : ℕ) : srP :=
  ⟨srX k, srX_mem k⟩

theorem srXP_bijective : Function.Bijective fun k : Fin 504 => srXP k := by
  constructor
  · intro i j h
    have h2 : srX i = srX j := congrArg Subtype.val h
    have h1 : srCode i = srCode j := by
      rw [← permCode_srX i.2, ← permCode_srX j.2, h2]
    exact Fin.ext (srCode_injective i.2 j.2 h1)
  · intro x
    obtain ⟨k, hk, hkx⟩ := exists_srX_eq x.2
    exact ⟨⟨k, hk⟩, Subtype.ext hkx⟩

@[expose] def srEquiv : Fin 504 ≃ srP :=
  Equiv.ofBijective _ srXP_bijective

theorem card_srP : Nat.card srP = 504 := by
  rw [← Nat.card_congr srEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem srClass {k : ℕ} (hk : k < 504) :
    srCls.getD k 0 < 9 ∧ srConj.getD k 0 < 504 ∧ srReps.getD (srCls.getD k 0) 0 < 504 ∧
      srX k * srX (srConj.getD k 0) =
        srX (srConj.getD k 0) * srX (srReps.getD (srCls.getD k 0) 0) := by
  have h := forall_lt_of_chunks (p := fun k => Nat.blt (srCls.getD k 0) 9 &&
    Nat.blt (srConj.getD k 0) 504 &&
      cmul (srCode k) (srCode (srConj.getD k 0)) ==
        cmul (srCode (srConj.getD k 0)) (srCode (srReps.getD (srCls.getD k 0) 0)))
    srClassChunk_0 srClassChunk_1 srClassChunk_2 srClassChunk_3 srClassChunk_4 srClassChunk_5
    srClassChunk_6 srClassChunk_7 hk
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  obtain ⟨⟨hc, hj⟩, he⟩ := h
  have hr : srReps.getD (srCls.getD k 0) 0 < 504 := by
    refine srHead.2.2.2.2 _ ?_
    rw [List.getD_eq_getElem _ _ (srHead.2.2.1 ▸ hc)]
    exact List.getElem_mem _
  refine ⟨hc, hj, hr, permCode_injective ?_⟩
  rw [permCode_mul, permCode_mul, permCode_srX hk, permCode_srX hj, permCode_srX hr, he]

theorem isSimpleGroup_srP : IsSimpleGroup srP := by
  have hcard := card_srP
  have : Nontrivial srP := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  classical
  refine ⟨fun N hN => ?_⟩
  set X : ℕ → srP := srXP with hX
  have hmem : ∀ k < 504, X k ∈ N ↔ X (srReps.getD (srCls.getD k 0) 0) ∈ N := by
    intro k hk
    obtain ⟨-, -, -, h⟩ := srClass hk
    have h' : X k = X (srConj.getD k 0) * X (srReps.getD (srCls.getD k 0) 0) *
        (X (srConj.getD k 0))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact Subtype.ext h
    have h'' : (X (srConj.getD k 0))⁻¹ * X k * ((X (srConj.getD k 0))⁻¹)⁻¹ =
        X (srReps.getD (srCls.getD k 0) 0) := by
      rw [h']
      group
    constructor
    · intro hk'
      rw [← h'']
      exact hN.conj_mem _ hk' _
    · intro hr
      rw [h']
      exact hN.conj_mem _ hr _
  set T : Finset (Fin 9) := Finset.univ.filter fun c => X (srReps.getD c 0) ∈ N with hT
  have hT0 : (0 : Fin 9) ∈ T := by
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : X (srReps.getD 0 0) = 1 := by
      rw [srHead.2.2.2.1]
      exact Subtype.ext srX_zero
    simpa using this ▸ N.one_mem
  have hcount : Nat.card N = ∑ c ∈ T, [1, 56, 63, 72, 72, 56, 72, 56, 56].getD c 0 := by
    have e : N ≃ {k : Fin 504 // X k ∈ N} :=
      (srEquiv.subtypeEquiv (p := fun k : Fin 504 => X k ∈ N) (q := fun x => x ∈ N)
        fun k => Iff.rfl).symm
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfib := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun k : Fin 504 =>
      X k ∈ N) (t := T) (f := fun k : Fin 504 => (⟨srCls.getD k 0, (srClass k.2).1⟩ : Fin 9))
      (fun k hk => by
        rw [Finset.mem_coe, Finset.mem_filter] at hk
        rw [Finset.mem_coe, hT, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hmem k k.2).1 hk.2⟩)
    rw [hfib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' : X (srReps.getD c 0) ∈ N := by
      have h := hc
      rw [hT, Finset.mem_filter] at h
      exact h.2
    have hfilt : (Finset.univ.filter fun k : Fin 504 => X k ∈ N).filter
        (fun k : Fin 504 => (⟨srCls.getD k 0, (srClass k.2).1⟩ : Fin 9) = c) =
          Finset.univ.filter fun k : Fin 504 => srCls.getD k 0 = c := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hkc⟩
        exact congrArg Fin.val hkc
      · intro hkc
        refine ⟨(hmem k k.2).2 ?_, Fin.ext hkc⟩
        rw [hkc]
        exact hc'
    rw [hfilt]
    exact srClassSize_eq c
  have hdvd : Nat.card N ∣ 504 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  rcases srClassSum_check T hT0 (hcount ▸ hdvd) with h1 | h504
  · left
    exact Subgroup.eq_bot_of_card_eq N (hcount.trans h1)
  · right
    exact Subgroup.eq_top_of_card_eq N ((hcount.trans h504).trans hcard.symm)

theorem srSigma0_mem : srSigma0 ∈ srP :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem srSigmaN_mem : srSigmaN ∈ srP :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem srSigma0_mul_srSigmaN_ne : srSigma0 * srSigmaN ≠ srSigmaN * srSigma0 := fun h => by
  have := congrArg permCode h
  rw [permCode_mul, permCode_mul, permCode_srSigma0, permCode_srSigmaN] at this
  exact srNoncommCheck_eq this

theorem srSigma1_not_mem : srSigma1 ∉ srP := fun h => by
  have := permCode_mem_of_mem_srP h
  rw [permCode_srSigma1] at this
  exact srOutsideCheck_eq this

theorem srSigma1_conj_mem : srSigma1 * srSigma0 * srSigma1⁻¹ ∈ srP ∧
    srSigma1 * srSigmaN * srSigma1⁻¹ ∈ srP := by
  have h := srNormalCheck_eq
  simp only [srNormalCheck, Bool.and_eq_true, beq_iff_eq] at h
  have e0 : srSigma1 * srSigma0 = srX 1 * srSigma1 := permCode_injective (by
    rw [permCode_mul, permCode_mul, permCode_srSigma1, permCode_srSigma0,
      permCode_srX (by norm_num), h.1])
  have en : srSigma1 * srSigmaN = srX 445 * srSigma1 := permCode_injective (by
    rw [permCode_mul, permCode_mul, permCode_srSigma1, permCode_srSigmaN,
      permCode_srX (by norm_num), h.2])
  refine ⟨?_, ?_⟩
  · rw [e0, mul_inv_cancel_right]
    exact srX_mem 1
  · rw [en, mul_inv_cancel_right]
    exact srX_mem 445

end CFSG.LieType.Ree
