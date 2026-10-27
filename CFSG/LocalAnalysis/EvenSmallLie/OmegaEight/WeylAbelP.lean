module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAct
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAbelCheck

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer

theorem testBit_bitsOf (p : ℕ → Bool) (n i : ℕ) :
    (bitsOf p n).testBit i = (decide (i < n) && p i) := by
  induction n with
  | zero => simp [bitsOf]
  | succ n ih =>
    rw [bitsOf, Nat.testBit_lor, ih]
    rcases lt_trichotomy i n with h | rfl | h
    · cases hp : p n <;> simp [h, h.trans (Nat.lt_succ_self n), Nat.ne_of_gt h]
    · cases hp : p i <;> simp
    · cases hp : p n <;> simp [Nat.ne_of_lt h, not_lt.2 h.le, not_lt.2 (Nat.succ_le_of_lt h)]

theorem rep_perm8Arr (σ : Equiv.Perm (Fin 8)) : Rep 8 (perm8Arr σ) σ := fun x => by
  rw [perm8Arr, getElem!_ofFn_nat _ x.2]

@[expose] def q1Sub : Subgroup (Equiv.Perm (Fin 8)) := closure {σ | σ ∈ q1Gens}

@[expose] def q0Sub : Subgroup (Equiv.Perm (Fin 8)) := closure {σ | σ ∈ q0Gens}

@[expose] def pElt (i : ℕ) : Equiv.Perm (Fin 8) := permOfArr 8 (pListArr i)

theorem rep_pElt {i : ℕ} (hi : i < 128) : Rep 8 (pListArr i) (pElt i) :=
  rep_of_validA (p_list_facts.valid i hi)

theorem pMul_lt (i j : ℕ) : pMul i j < 128 := Nat.mod_lt _ (by norm_num)

theorem pInv_lt (i : ℕ) : pInv i < 128 := Nat.mod_lt _ (by norm_num)

theorem pElt_zero : pElt 0 = 1 := eq_of_eqA (rep_pElt (by norm_num)) rep_idA p_list_facts.id0

theorem pElt_mul {i j : ℕ} (hi : i < 128) (hj : j < 128) : pElt (pMul i j) = pElt i * pElt j :=
  (eq_of_eqA (rep_compA (rep_pElt hi) (rep_pElt hj)) (rep_pElt (pMul_lt i j))
    (p_list_facts.mul i hi j hj)).symm

theorem pElt_inv {i : ℕ} (hi : i < 128) : pElt (pInv i) = (pElt i)⁻¹ := by
  have h := eq_of_eqA (rep_compA (rep_pElt hi) (rep_pElt (pInv_lt i))) rep_idA
    (p_list_facts.inv i hi)
  exact (inv_eq_of_mul_eq_one_right h).symm

theorem pElt_inj {i j : ℕ} (hi : i < 128) (hj : j < 128) (h : pElt i = pElt j) : i = j := by
  by_contra hij
  have h1 := p_list_facts.distinct i hi j hj hij
  rw [(eqA_iff (rep_pElt hi) (rep_pElt hj)).2 h] at h1
  exact absurd h1 (by decide)

theorem pGens_length : (Equiv.swap 0 1 :: pPlusGens).length = 7 := rfl

theorem pElt_gen {k : ℕ} (hk : k < 7) :
    pElt (k + 1) = (Equiv.swap 0 1 :: pPlusGens)[k]'(by rw [pGens_length]; exact hk) := by
  have h := eq_of_eqA (rep_perm8Arr _) (rep_pElt (by omega)) (p_list_facts.gens k hk)
  rw [List.getD_eq_getElem _ _ (by rw [pGens_length]; exact hk)] at h
  exact h.symm

theorem mem_pSub_iff {σ : Equiv.Perm (Fin 8)} : σ ∈ pSub ↔ ∃ i < 128, pElt i = σ := by
  constructor
  · intro hσ
    refine closure_induction (p := fun x _ => ∃ i < 128, pElt i = x) (fun x hx => ?_)
      ⟨0, by norm_num, pElt_zero⟩ (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hσ
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      rw [pGens_length] at hk
      exact ⟨k + 1, by omega, pElt_gen hk⟩
    · obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hy
      exact ⟨pMul i j, pMul_lt i j, pElt_mul hi hj⟩
    · obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨pInv i, pInv_lt i, pElt_inv hi⟩
  · rintro ⟨i, hi, rfl⟩
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [pElt_zero]
        exact one_mem _
      · obtain ⟨hp, hl, he⟩ := p_list_facts.tree i hi hpos
        rw [← he, pElt_mul (by omega) (hp.trans hi), pElt_gen hl]
        exact mul_mem (subset_closure (List.getElem_mem _)) (ih _ hp (hp.trans hi))

theorem pElt_mem {i : ℕ} (hi : i < 128) : pElt i ∈ pSub := mem_pSub_iff.2 ⟨i, hi, rfl⟩

open Classical in
@[expose] def maskOf (Q : Subgroup (Equiv.Perm (Fin 8))) : ℕ :=
  bitsOf (fun i => decide (pElt i ∈ Q)) 128

theorem testBit_maskOf (Q : Subgroup (Equiv.Perm (Fin 8))) (i : ℕ) :
    (maskOf Q).testBit i = true ↔ i < 128 ∧ pElt i ∈ Q := by
  classical
  rw [maskOf, testBit_bitsOf, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

section SubList

variable {gs : List (Equiv.Perm (Fin 8))} {gi : List ℕ} {M : ℕ} {W : List (List ℕ)}

theorem pElt_gi (h : SubListFacts gs gi M W) {k : ℕ} (hk : k < gs.length) :
    pElt (gi.getD k 0) = gs[k] := by
  have e := eq_of_eqA (rep_perm8Arr _) (rep_pElt (h.idx k (h.len ▸ hk)).1) (h.gens k hk)
  rw [List.getD_eq_getElem _ _ hk] at e
  exact e.symm

theorem wordIdx_lt (gi : List ℕ) : ∀ w : List ℕ, wordIdx gi w < 128
  | [] => by norm_num [wordIdx]
  | _ :: _ => pMul_lt _ _

theorem pElt_wordIdx (h : SubListFacts gs gi M W) (w : List ℕ) :
    pElt (wordIdx gi w) ∈ closure {σ | σ ∈ gs} := by
  induction w with
  | nil => exact pElt_zero ▸ one_mem _
  | cons k w ih =>
    change pElt (pMul (gi.getD k 0) (wordIdx gi w)) ∈ _
    by_cases hk : k < gi.length
    · rw [pElt_mul (h.idx k hk).1 (wordIdx_lt gi w), pElt_gi h (h.len ▸ hk)]
      exact mul_mem (subset_closure (List.getElem_mem _)) ih
    · rw [List.getD_eq_default _ _ (not_lt.1 hk), pElt_mul (by norm_num) (wordIdx_lt gi w),
        pElt_zero, one_mul]
      exact ih

theorem maskOf_closure (h : SubListFacts gs gi M W) : maskOf (closure {σ | σ ∈ gs}) = M := by
  refine Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.2 ?_
  rw [testBit_maskOf]
  constructor
  · rintro ⟨hi, hσ⟩
    obtain ⟨j, hj, hmj, he⟩ : ∃ j < 128, M.testBit j = true ∧ pElt j = pElt i := by
      refine closure_induction (p := fun x _ => ∃ j < 128, M.testBit j = true ∧ pElt j = x)
        (fun x hx => ?_) ⟨0, by norm_num, h.one, pElt_zero⟩ (fun x y _ _ hx hy => ?_)
        (fun x _ hx => ?_) hσ
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        exact ⟨_, (h.idx k (h.len ▸ hk)).1, (h.idx k (h.len ▸ hk)).2, pElt_gi h hk⟩
      · obtain ⟨a, ha, hma, rfl⟩ := hx
        obtain ⟨b, hb, hmb, rfl⟩ := hy
        exact ⟨pMul a b, pMul_lt a b, h.mul a ha b hb hma hmb, pElt_mul ha hb⟩
      · obtain ⟨a, ha, hma, rfl⟩ := hx
        exact ⟨pInv a, pInv_lt a, h.inv a ha hma, pElt_inv ha⟩
    rwa [← pElt_inj hj hi he]
  · intro hm
    have hi : i < 128 := by
      by_contra hc
      rw [Nat.testBit_eq_false_of_lt (h.lt.trans_le (Nat.pow_le_pow_right (by norm_num)
        (not_lt.1 hc)))] at hm
      exact Bool.false_ne_true hm
    obtain ⟨w, -, hw⟩ := h.words i hi hm
    exact ⟨hi, hw ▸ pElt_wordIdx h w⟩

end SubList

theorem eq_of_maskOf_eq {Q R : Subgroup (Equiv.Perm (Fin 8))} (hQ : Q ≤ pSub) (hR : R ≤ pSub)
    (h : maskOf Q = maskOf R) : Q = R := by
  have key : ∀ i < 128, pElt i ∈ Q ↔ pElt i ∈ R := fun i hi => by
    have h1 := testBit_maskOf Q i
    have h2 := testBit_maskOf R i
    rw [h] at h1
    exact ⟨fun hq => (h2.1 (h1.2 ⟨hi, hq⟩)).2, fun hr => (h1.1 (h2.2 ⟨hi, hr⟩)).2⟩
  ext σ
  constructor
  · intro hσ
    obtain ⟨i, hi, rfl⟩ := mem_pSub_iff.1 (hQ hσ)
    exact (key i hi).1 hσ
  · intro hσ
    obtain ⟨i, hi, rfl⟩ := mem_pSub_iff.1 (hR hσ)
    exact (key i hi).2 hσ

theorem maskOf_bot : maskOf ⊥ = 1 := by
  refine Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.2 ?_
  rw [testBit_maskOf, mem_bot, show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hi, h⟩
    exact pElt_inj (by norm_num) hi (pElt_zero.trans h.symm)
  · rintro rfl
    exact ⟨by norm_num, pElt_zero⟩

theorem testBit_extMask (m x j : ℕ) : (extMask m x).testBit j =
    (m.testBit j || (decide (j < 128) && m.testBit (pMul (pInv x) j))) := by
  rw [extMask, Nat.testBit_lor, testBit_bitsOf]

theorem layerLists_length : layerLists.length = 5 := rfl

theorem layer_eq_nil {k : ℕ} (hk : 5 ≤ k) : layer k = [] :=
  List.getD_eq_default _ _ (by rw [layerLists_length]; exact hk)

theorem testBit_maskOf_ge (Q : Subgroup (Equiv.Perm (Fin 8))) {j : ℕ} (hj : ¬ j < 128) :
    (maskOf Q).testBit j = false := by
  by_contra h
  exact hj ((testBit_maskOf Q j).1 (Bool.not_eq_false _ ▸ h)).1

theorem maskOf_mem_layer : ∀ (k : ℕ) (Q : Subgroup (Equiv.Perm (Fin 8))), Q ≤ pSub →
    (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) → Nat.card Q = 2 ^ k → maskOf Q ∈ layer k
  | 0, Q, _, _, hc => by
    rw [Subgroup.eq_bot_of_card_eq Q (by simpa using hc), maskOf_bot]
    change 1 ∈ [1]
    exact List.mem_singleton_self 1
  | k + 1, Q, hQ, hab, hc => by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Q) 2 (n := k)
      (by rw [hc, pow_succ]; exact Dvd.intro 2 rfl)
    set H : Subgroup (Equiv.Perm (Fin 8)) := K.map Q.subtype with hHdef
    have hHQ : H ≤ Q := map_subtype_le K
    have hHc : Nat.card H = 2 ^ k := by
      rw [hHdef, Subgroup.card_map_of_injective Q.subtype_injective, hK]
    have hHm := maskOf_mem_layer k H (hHQ.trans hQ)
      (fun a ha b hb => hab a (hHQ ha) b (hHQ hb)) hHc
    have hidx : K.index = 2 := by
      have h1 := Subgroup.card_mul_index K
      rw [hK, hc, pow_succ] at h1
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    have hmemH : ∀ y : Q, (y : Equiv.Perm (Fin 8)) ∈ H ↔ y ∈ K := fun y =>
      Subgroup.mem_map_iff_mem Q.subtype_injective
    obtain ⟨x, hxK⟩ : ∃ x : Q, x ∉ K := by
      by_contra h
      push Not at h
      have htop : K = ⊤ := eq_top_iff.2 fun x _ => h x
      rw [htop, index_top] at hidx
      exact absurd hidx (by norm_num)
    obtain ⟨ix, hix, hx⟩ := mem_pSub_iff.1 (hQ x.2)
    have hxx : x * x ∈ K := mul_self_mem_of_index_two hidx x
    have hsplit : ∀ y : Q, y ∈ K ∨ x⁻¹ * y ∈ K := fun y => by
      by_cases hy : y ∈ K
      · exact Or.inl hy
      · right
        rw [mul_mem_iff_of_index_two hidx]
        exact ⟨fun h => absurd (inv_mem_iff.1 h) hxK, fun h => absurd h hy⟩
    set m := maskOf H
    have hvalid : validExt m ix = true := by
      rw [validExt, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
      refine ⟨⟨?_, ?_⟩, fun i hi => ?_⟩
      · by_contra h
        rw [Bool.not_eq_false] at h
        exact hxK ((hmemH x).1 (hx ▸ ((testBit_maskOf H ix).1 h).2))
      · rw [testBit_maskOf, pElt_mul hix hix, hx]
        exact ⟨pMul_lt _ _, (hmemH (x * x)).2 hxx⟩
      · rw [List.mem_range] at hi
        rw [Bool.or_eq_true, beq_iff_eq]
        by_cases hm : m.testBit i = true
        · right
          have hiH := ((testBit_maskOf H i).1 hm).2
          refine pElt_inj (pMul_lt _ _) (pMul_lt _ _) ?_
          rw [pElt_mul hix hi, pElt_mul hi hix, hx]
          exact hab _ x.2 _ (hHQ hiH)
        · left
          simpa using hm
    have hext : extMask m ix = maskOf Q := by
      refine Nat.eq_of_testBit_eq fun j => ?_
      rw [testBit_extMask]
      by_cases hj : j < 128
      · refine Bool.eq_iff_iff.2 ?_
        rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, testBit_maskOf,
          testBit_maskOf, testBit_maskOf, pElt_mul (pInv_lt ix) hj, pElt_inv hix, hx]
        constructor
        · rintro (⟨-, h⟩ | ⟨-, -, h⟩)
          · exact ⟨hj, hHQ h⟩
          · refine ⟨hj, ?_⟩
            have := mul_mem x.2 (hHQ h)
            rwa [mul_inv_cancel_left] at this
        · rintro ⟨-, hjQ⟩
          rcases hsplit ⟨_, hjQ⟩ with h | h
          · exact Or.inl ⟨hj, (hmemH _).2 h⟩
          · exact Or.inr ⟨hj, pMul_lt _ _, (hmemH _).2 h⟩
      · rw [testBit_maskOf_ge H hj, testBit_maskOf_ge Q hj]
        simp [hj]
    have hk : k < 5 := by
      by_contra h
      rw [layer_eq_nil (by omega)] at hHm
      exact List.not_mem_nil hHm
    rw [← hext]
    exact layer_list_facts.closed k hk m hHm ix hix hvalid

theorem fixA_iff {a : Array ℕ} {σ : Equiv.Perm (Fin 8)} (ha : Rep 8 a σ) (n : ℕ) :
    fixA a n = true ↔ permVec σ (frameDecode n) = frameDecode n := by
  rw [fixA, List.all_eq_true]
  constructor
  · intro h
    funext i
    have h1 := h (σ.symm i) (List.mem_range.2 (σ.symm i).2)
    rw [beq_iff_eq, ha.apply (σ.symm i).2] at h1
    simp only [Fin.eta, Equiv.apply_symm_apply] at h1
    simp only [permVec, frameDecode, h1]
  · intro h j hj
    rw [List.mem_range] at hj
    have h1 := congrFun h (σ ⟨j, hj⟩)
    simp only [permVec, frameDecode, Equiv.symm_apply_apply] at h1
    rw [beq_iff_eq, ha.apply hj]
    cases h2 : n.testBit j <;> cases h3 : n.testBit (σ ⟨j, hj⟩ : ℕ) <;> simp_all

theorem mem_fixSet_iff {Q : Subgroup (Equiv.Perm (Fin 8))} (hQ : Q ≤ pSub) {n : ℕ}
    (hn : n < 256) : frameDecode n ∈ fixSet Q ↔ (framePop n % 2 == 0 &&
      (List.range 128).all fun i => !(maskOf Q).testBit i || fixA (pListArr i) n) = true := by
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, fixSet, Set.mem_ofPred_eq, mem_evenSub,
    evenSub_iff_frameDecode n hn]
  refine and_congr_right fun _ => ⟨fun h i hi => ?_, fun h σ hσ => ?_⟩
  · rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hm : (maskOf Q).testBit i = true
    · right
      have hi' := List.mem_range.1 hi
      exact (fixA_iff (rep_pElt hi') n).2 (h _ ((testBit_maskOf Q i).1 hm).2)
    · left
      simpa using hm
  · obtain ⟨i, hi, rfl⟩ := mem_pSub_iff.1 (hQ hσ)
    have := h i (List.mem_range.2 hi)
    rw [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h1 | h1
    · rw [(testBit_maskOf Q i).2 ⟨hi, hσ⟩] at h1
      exact absurd h1 (by decide)
    · exact (fixA_iff (rep_pElt hi) n).1 h1

theorem card_fixSet_eq {Q : Subgroup (Equiv.Perm (Fin 8))} (hQ : Q ≤ pSub) :
    Nat.card (fixSet Q) = fixEven (maskOf Q) := by
  classical
  have h1 : Nat.card (fixSet Q) = (Finset.univ.filter fun v => v ∈ fixSet Q).card := by
    rw [Nat.card_eq_card_toFinset]
    congr 1
    ext v
    simp
  rw [h1, card_filter_frameVec, fixEven, ← List.countP_eq_length_filter, countP_range_eq_card']
  congr 1
  exact Finset.filter_congr fun n hn => mem_fixSet_iff hQ (Finset.mem_range.1 hn)

theorem card_pSub : Nat.card pSub = 2 ^ 7 := by
  let f : Fin 128 → pSub := fun i => ⟨pElt i, pElt_mem i.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => Fin.ext (pElt_inj i.2 j.2 (congrArg Subtype.val h)), fun x => ?_⟩
    obtain ⟨i, hi, he⟩ := mem_pSub_iff.1 x.2
    exact ⟨⟨i, hi⟩, Subtype.ext he⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem exists_card_eq_two_pow {Q : Subgroup (Equiv.Perm (Fin 8))} (hQ : Q ≤ pSub) :
    ∃ k ≤ 7, Nat.card Q = 2 ^ k := by
  have h1 : Nat.card Q ∣ Nat.card pSub := Subgroup.card_dvd_of_le hQ
  rw [card_pSub] at h1
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h1

theorem q1Sub_le_pSub : q1Sub ≤ pSub := by
  rw [q1Sub, closure_le]
  rintro σ hσ
  simp only [q1Gens, Set.mem_ofPred_eq, List.mem_cons, List.mem_nil_iff, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl
  · exact swap01_mem_pSub
  · exact swap23_mem_pSub
  · exact swap45_mem_pSub
  · exact swap67_mem_pSub

theorem pPlusSub_le_pSub : pPlusSub ≤ pSub := by
  rw [pPlusSub, closure_le]
  exact fun σ hσ => pPlusGen_mem_pSub hσ

theorem q0Sub_le_pPlusSub : q0Sub ≤ pPlusSub := by
  rw [q0Sub, closure_le]
  rintro σ hσ
  simp only [q0Gens, Set.mem_ofPred_eq, List.mem_cons, List.mem_nil_iff, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  · exact pPlusGen_mem_pPlusSub (by decide)
  · exact pPlusGen_mem_pPlusSub (by decide)
  · exact swap0167_mem_pPlusSub

theorem fixSet_bound {Q : Subgroup (Equiv.Perm (Fin 8))} (hQ : Q ≤ pSub)
    (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) :
    Nat.card (fixSet Q) * Nat.card Q ≤ 256 ∧
      (Nat.card (fixSet Q) * Nat.card Q = 256 → Q = q1Sub) ∧
      (Q ≤ pPlusSub → Nat.card (fixSet Q) * Nat.card Q ≤ 128 ∧
        (Nat.card (fixSet Q) * Nat.card Q = 128 → Q = ⊥ ∨ Q = q0Sub)) := by
  obtain ⟨k, -, hk⟩ := exists_card_eq_two_pow hQ
  have hm := maskOf_mem_layer k Q hQ hab hk
  have hk5 : k < 5 := by
    by_contra h
    rw [layer_eq_nil (by omega)] at hm
    exact List.not_mem_nil hm
  have hv := layer_list_facts.val k hk5 _ hm
  rw [card_fixSet_eq hQ, hk]
  rw [layerValOK, ← maskOf_closure q1_facts, ← maskOf_closure q0_facts,
    ← maskOf_closure pPlus_facts, ← q1Sub, ← q0Sub, ← pPlusSub] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, Bool.not_eq_true'] at hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := hv
  refine ⟨h1, fun he => eq_of_maskOf_eq hQ q1Sub_le_pSub (h2.resolve_left (not_not.2 he)),
    fun hP => ?_⟩
  have hsub : subMask (maskOf Q) (maskOf pPlusSub) = true := by
    rw [subMask, List.all_eq_true]
    intro i _
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hb : (maskOf Q).testBit i = true
    · right
      obtain ⟨hi, hq⟩ := (testBit_maskOf Q i).1 hb
      exact (testBit_maskOf _ i).2 ⟨hi, hP hq⟩
    · left
      simpa using hb
  rcases h3 with h3 | ⟨h4, h5⟩
  · rw [hsub] at h3
    exact absurd h3 (by decide)
  · refine ⟨h4, fun he => ?_⟩
    rcases h5 with (h6 | h6) | h6
    · exact absurd he h6
    · left
      exact eq_of_maskOf_eq hQ bot_le (h6.trans maskOf_bot.symm)
    · right
      exact eq_of_maskOf_eq hQ (q0Sub_le_pPlusSub.trans pPlusSub_le_pSub) h6

end CFSG.EvenSmallLie.OmegaEight.Weyl
