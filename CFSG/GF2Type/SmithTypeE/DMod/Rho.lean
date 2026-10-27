module

public import Certificates.Certificate38703
public import CFSG.GF2Type.SmithTypeE.DMod.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 Module

attribute [local irreducible] tvCols tvLin

theorem spanWCheck_holds : chkSpanW = true :=
  Certificates.certificate38703.1

theorem rankCheck_holds : chkRank = true :=
  Certificates.certificate38703.2

theorem spanW_parts :
    spanIdx.size = 32 ∧ (∀ i ∈ spanIdx, i < 75735) ∧ ∀ m < 32,
      applyCols (spanIdx.map fun i => wtArr[i]!) spanCoef[m]! = 2 ^ m := by
  have h := spanWCheck_holds
  simp only [chkSpanW, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true', decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.2, h.2⟩

theorem spanIdx_lt (s : Fin 32) : spanIdx[s.val]! < 75735 := by
  obtain ⟨hs, hlt, -⟩ := spanW_parts
  have hs' : s.val < spanIdx.size := by rw [hs]; exact s.2
  rw [getElem!_pos spanIdx s.val hs']
  exact hlt _ (Array.getElem_mem hs')

theorem span_spanIdx :
    Submodule.span (ZMod 2) (Set.range fun s : Fin 32 => wtV spanIdx[s.val]!) = ⊤ := by
  obtain ⟨hs, -, he⟩ := spanW_parts
  set B := spanIdx.map fun i => wtArr[i]! with hB
  have hBs : B.size = 32 := by rw [hB, Array.size_map, hs]
  have hBget : ∀ s : Fin 32, decode32 B[s.val]! = wtV spanIdx[s.val]! := by
    intro s
    have hs' : s.val < spanIdx.size := by rw [hs]; exact s.2
    rw [hB, getElem!_pos _ s.val (by rw [Array.size_map]; exact hs'), Array.getElem_map,
      ← getElem!_pos spanIdx s.val hs']
    rfl
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ m : Fin 32, v m • Pi.single m (1 : ZMod 2) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  rw [← decode32_two_pow, ← he m m.2, decode32_applyCols hBs, colsLin_apply]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨s, (hBget s).symm⟩)

theorem span_wtV :
    Submodule.span (ZMod 2) (Set.range fun i : Fin 75735 => wtV i.val) = ⊤ := by
  rw [eq_top_iff, ← span_spanIdx]
  refine Submodule.span_mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨_, spanIdx_lt s⟩, rfl⟩

theorem linearIndependent_spanIdx :
    LinearIndependent (ZMod 2) fun s : Fin 32 => wtV spanIdx[s.val]! :=
  linearIndependent_of_top_le_span_of_card_eq_finrank span_spanIdx.ge
    (by rw [Fintype.card_fin, Module.finrank_fin_fun])

theorem planeSub_injective
    {i j : ℕ} (hi : i < 75735)
    (hj : j < 75735) (h : planeSub i = planeSub j) : i = j := by
  classical
  have key : fModel (wtV i + wtV j) = 0 := by
    refine LinearMap.ext_on_range span_wtV fun k => ?_
    have hopp : Opp i k.val ↔ Opp j k.val := by
      unfold Opp
      rw [h]
    have h1 := fModel_wtV hi k.2
    have h2 := fModel_wtV hj k.2
    rw [LinearMap.map_add, LinearMap.add_apply, h1, h2]
    by_cases hk : Opp i k.val
    · simp only [hk, hopp.mp hk, ↓reduceIte, LinearMap.zero_apply]
      decide
    · have hk' : ¬ Opp j k.val := fun h' => hk (hopp.mpr h')
      simp only [hk, hk', ↓reduceIte, add_zero, LinearMap.zero_apply]
  have hz : wtV i + wtV j = 0 := fModel_nondegenerate fun w => by rw [key]; rfl
  have heq : wtV i = wtV j := by
    have : wtV i = - wtV j := eq_neg_of_add_eq_zero_left hz
    rw [this]
    funext m
    simp only [Pi.neg_apply]
    generalize wtV j m = c
    revert c
    decide
  exact wtV_injective hi hj heq

theorem meetCnt_eq_one_iff {i j : ℕ} (hi : i < 75735)
    (hj : j < 75735) : meetCnt i j = 1 ↔ Opp i j := by
  have Fi := planeFacts hi
  have Fj := planeFacts hj
  have hz : memR pbArr[j]! ppArr[j]! 0 = true := by
    have h := Fj.complete 0 (by norm_num)
    rwa [xorComb_zero] at h
  constructor
  · intro h
    have key : ∀ d < 64, memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d) = true → d = 0 := by
      intro d hd hmem
      unfold meetCnt at h
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h
      have h0 : 0 ∈ (List.range 64).filter
          (fun d => memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d)) := by
        refine List.mem_filter.2 ⟨List.mem_range.2 (by norm_num), ?_⟩
        show memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! 0) = true
        rw [xorComb_zero]
        exact hz
      have hd' : d ∈ (List.range 64).filter
          (fun d => memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d)) :=
        List.mem_filter.2 ⟨List.mem_range.2 hd, hmem⟩
      rw [ha, List.mem_singleton] at h0 hd'
      omega
    unfold Opp
    rw [Submodule.disjoint_def]
    intro x hxi hxj
    have hxi' : x ∈ planeSpan pbArr[i]! := hxi
    have hxj' : x ∈ planeSpan pbArr[j]! := hxj
    obtain ⟨d, hd, rfl⟩ := mem_planeSpan_iff.1 hxi'
    obtain ⟨e, he, hxe⟩ := mem_planeSpan_iff.1 hxj'
    have hcode : xorComb pbArr[i]! d = xorComb pbArr[j]! e :=
      eq_of_dec12_eq (xorComb_lt Fi.lt d) (xorComb_lt Fj.lt e) hxe
    have hmem : memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d) = true := by
      rw [hcode]
      exact Fj.complete e he
    obtain rfl := key d hd hmem
    rw [xorComb_zero, dec12_zero]
  · intro hopp
    have hopp' : Disjoint (planeSub i) (planeSub j) := hopp
    rw [Submodule.disjoint_def] at hopp'
    have hiff : ∀ d < 64, memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d) = true ↔ d = 0 := by
      intro d hd
      constructor
      · intro hmem
        by_contra hd0
        have hmj : dec12 (xorComb pbArr[i]! d) ∈ planeSpan pbArr[j]! :=
          dec12_mem_planeSpan_of_memR hmem
        have hmi : dec12 (xorComb pbArr[i]! d) ∈ planeSpan pbArr[i]! :=
          dec12_xorComb_mem_planeSpan _ d
        have h0 : dec12 (xorComb pbArr[i]! d) = 0 :=
          hopp' (dec12 (xorComb pbArr[i]! d)) hmi hmj
        have hc : xorComb pbArr[i]! d = 0 :=
          eq_of_dec12_eq (xorComb_lt Fi.lt d) (by norm_num) (h0.trans dec12_zero.symm)
        rcases Fi.indep d hd with h1 | h1
        · exact hd0 h1
        · exact h1 hc
      · intro hd0
        subst hd0
        rw [xorComb_zero]
        exact hz
    have hfilt : (List.range 64).filter (fun d => memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d))
        = (List.range 64).filter (fun d => d == 0) := by
      apply List.filter_congr
      intro d hd
      rw [List.mem_range] at hd
      show memR pbArr[j]! ppArr[j]! (xorComb pbArr[i]! d) = (d == 0)
      rw [Bool.eq_iff_iff, hiff d hd, beq_iff_eq]
    unfold meetCnt
    rw [hfilt]
    decide

theorem distD_eq_three_iff {i j : ℕ} (hi : i < 75735)
    (hj : j < 75735) : distD i j = 3 ↔ Opp i j := by
  rw [← meetCnt_eq_one_iff hi hj]
  simp only [distD]
  by_cases h1 : meetCnt i j = 1
  · simp [h1]
  · simp only [h1, iff_false]
    split_ifs <;> simp_all

theorem distD_le (i j : ℕ) : distD i j ≤ 3 := by
  simp only [distD]
  split_ifs <;> omega

theorem relD_eight_iff {i j : ℕ} (hi : i < 75735)
    (hj : j < 75735) : relD 8 i j = true ↔ Opp i j := by
  rw [← distD_eq_three_iff hi hj]
  have hle := distD_le i j
  unfold relD
  generalize distD i j = d at hle ⊢
  interval_cases d <;> decide

theorem rankA_getElem {R : Nat} {rr cc : Array Nat} (hr : rr.size = 33) (hc : cc.size = 33)
    {s t : Nat} (hs : s < 33) (ht : t < 33) :
    ((rr.map fun i => cc.map fun j => relD R i j)[s]!)[t]! = relD R rr[s]! cc[t]! := by
  have hs' : s < rr.size := by omega
  have ht' : t < cc.size := by omega
  have hA : (rr.map fun i => cc.map fun j => relD R i j)[s]! =
      cc.map fun j => relD R rr[s]! j := by
    rw [getElem!_pos (rr.map fun i => cc.map fun j => relD R i j) s
        (by rw [Array.size_map]; exact hs'), Array.getElem_map, getElem!_pos rr s hs']
  rw [hA, getElem!_pos (cc.map fun j => relD R rr[s]! j) t
      (by rw [Array.size_map]; exact ht'), Array.getElem_map, getElem!_pos cc t ht']

theorem rankOK_sum {R : Nat} {rr cc inv : Array Nat} (hr : rr.size = 33) (hc : cc.size = 33)
    {s u : Nat} (hs : s < 33) (hu : u < 33)
    (hm : (List.range 33).foldl (fun acc t => acc ^^
      (((rr.map fun i => cc.map fun j => relD R i j)[s]!)[t]! && inv[t]!.testBit u)) false =
        (s == u)) :
    ∑ t ∈ Finset.range 33, bit (relD R rr[s]! cc[t]! && inv[t]!.testBit u) = bit (s == u) := by
  have e := congrArg bit hm
  rw [bit_foldl] at e
  refine Eq.trans ?_ e
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [rankA_getElem hr hc hs ht]

theorem linearIndependent_of_rankOK {R : Nat} {rr cc inv : Array Nat}
    (h : rankOK R rr cc inv = true) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : LinearMap.BilinForm (ZMod 2) W) (x : Nat → W)
    (hx : ∀ s t : Fin 33, f (x rr[s.val]!) (x cc[t.val]!) = bit (relD R rr[s.val]! cc[t.val]!)) :
    LinearIndependent (ZMod 2) fun s : Fin 33 => x rr[s.val]! := by
  simp only [rankOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  have hrs : rr.size = 33 := h.1.1.1.1.1
  have hcs : cc.size = 33 := h.1.1.1.1.2
  have hm := h.2
  rw [Fintype.linearIndependent_iff]
  intro c hcomb u
  have hcol : ∀ t : Fin 33, ∑ s : Fin 33, c s * bit (relD R rr[s.val]! cc[t.val]!) = 0 := by
    intro t
    have := congrArg (fun w => f w (x cc[t.val]!)) hcomb
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun s _ => by rw [hx s t]
  have hinv : ∀ s : Fin 33, ∑ t : Fin 33, bit (relD R rr[s.val]! cc[t.val]!) *
      bit (inv[t.val]!.testBit u.val) = if s = u then 1 else 0 := by
    intro s
    have e2 := rankOK_sum hrs hcs s.2 u.2 (hm s.val s.2 u.val u.2)
    rw [← Fin.sum_univ_eq_sum_range
      (fun t => bit (relD R rr[s.val]! cc[t]! && inv[t]!.testBit u.val)) 33] at e2
    simp only [bit_and] at e2
    rw [e2]
    by_cases hsu : s = u
    · subst hsu; simp [bit]
    · have : (s.val == u.val) = false := by simpa [Fin.ext_iff] using hsu
      simp only [this, hsu, ↓reduceIte]
      rfl
  calc c u = ∑ s : Fin 33, c s * (if s = u then 1 else 0) := by simp
    _ = ∑ s : Fin 33, c s * ∑ t : Fin 33, bit (relD R rr[s.val]! cc[t.val]!) *
          bit (inv[t.val]!.testBit u.val) := Finset.sum_congr rfl fun s _ => by rw [hinv s]
    _ = ∑ t : Fin 33, (∑ s : Fin 33, c s * bit (relD R rr[s.val]! cc[t.val]!)) *
          bit (inv[t.val]!.testBit u.val) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by simp [hcol]

theorem rankOK_lt {R : Nat} {rr cc inv : Array Nat} (h : rankOK R rr cc inv = true) :
    (∀ s < 33, rr[s]! < 75735) ∧ ∀ t < 33, cc[t]! < 75735 := by
  simp only [rankOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq] at h
  have hr : rr.size = 33 := h.1.1.1.1.1
  have hc : cc.size = 33 := h.1.1.1.1.2
  have hrr := h.1.1.2
  have hcc := h.1.2
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · rw [getElem!_pos rr s (by omega)]
    exact hrr _ (Array.getElem_mem _)
  · rw [getElem!_pos cc t (by omega)]
    exact hcc _ (Array.getElem_mem _)

theorem rank_parts :
    rankRels = #[2, 4, 6, 10, 12, 14] ∧
      ∀ r < 6, rankOK rankRels[r]! rankRows[r]! rankCols[r]! rankInv[r]! = true := by
  have h := rankCheck_holds
  simp only [chkRank, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.1, h.2⟩

theorem not_gram_rel {R : ℕ}
    (hR : R = 2 ∨ R = 4 ∨ R = 6 ∨ R = 10 ∨ R = 12 ∨ R = 14) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] (hW : finrank (ZMod 2) W ≤ 32)
    (f : LinearMap.BilinForm (ZMod 2) W) (x : ℕ → W)
    (hx : ∀ i j, i < 75735 → j < 75735 → f (x i) (x j) = bit (relD R i j)) : False := by
  obtain ⟨hrels, hok⟩ := rank_parts
  obtain ⟨r, hr, hRr⟩ : ∃ r < 6, rankRels[r]! = R := by
    rw [hrels]
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩
    · exact ⟨4, by norm_num, rfl⟩
    · exact ⟨5, by norm_num, rfl⟩
  have h := hok r hr
  rw [hRr] at h
  obtain ⟨hrr, hcc⟩ := rankOK_lt h
  have hli := linearIndependent_of_rankOK h f x fun s t => hx _ _ (hrr s s.2) (hcc t t.2)
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  omega

theorem rel_eq_of_gram {R : ℕ} (hR : R < 16) (hR0 : R % 2 = 0)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (hW : finrank (ZMod 2) W ≤ 32) (f : LinearMap.BilinForm (ZMod 2) W) (x : ℕ → W)
    (hx : ∀ i j, i < 75735 → j < 75735 → f (x i) (x j) = bit (relD R i j)) : R = 0 ∨ R = 8 := by
  have : R = 0 ∨ R = 2 ∨ R = 4 ∨ R = 6 ∨ R = 8 ∨ R = 10 ∨ R = 12 ∨ R = 14 := by omega
  rcases this with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact (not_gram_rel (Or.inl h) hW f x hx).elim
  · exact (not_gram_rel (Or.inr (Or.inl h)) hW f x hx).elim
  · exact (not_gram_rel (Or.inr (Or.inr (Or.inl h))) hW f x hx).elim
  · exact Or.inr h
  · exact (not_gram_rel (Or.inr (Or.inr (Or.inr (Or.inl h)))) hW f x hx).elim
  · exact (not_gram_rel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hW f x hx).elim
  · exact (not_gram_rel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) hW f x hx).elim

end CFSG.GF2Type.SmithTypeE.DMod
