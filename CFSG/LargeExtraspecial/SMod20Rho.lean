module

public import CFSG.LargeExtraspecial.SMod20Basic
public import Certificates.Certificate21261

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.SmithE CFSG.F4.Native Module

theorem spanWCheck_holds : chkSpanW = true :=
  Certificates.certificate21261.1

theorem distCheck_holds : chkDist = true :=
  Certificates.certificate21261.2.1

theorem rankCheck_holds : chkRank = true :=
  Certificates.certificate21261.2.2

theorem spanW_parts :
    spanIdx.size = 20 ∧ (∀ i ∈ spanIdx, i < 891) ∧ ∀ m < 20,
      applyCols (spanIdx.map fun i => wtArr[i]!) spanCoef[m]! = 2 ^ m := by
  have h := spanWCheck_holds
  simp only [chkSpanW, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true', decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.2, h.2⟩

theorem spanIdx_lt (s : Fin 20) : spanIdx[s.val]! < 891 := by
  obtain ⟨hs, hlt, -⟩ := spanW_parts
  have hs' : s.val < spanIdx.size := by rw [hs]; exact s.2
  rw [getElem!_pos spanIdx s.val hs']
  exact hlt _ (Array.getElem_mem hs')

theorem span_spanIdx :
    Submodule.span (ZMod 2) (Set.range fun s : Fin 20 => wtV spanIdx[s.val]!) = ⊤ := by
  obtain ⟨hs, -, he⟩ := spanW_parts
  set B := spanIdx.map fun i => wtArr[i]! with hB
  have hBs : B.size = 20 := by rw [hB, Array.size_map, hs]
  have hBget : ∀ s : Fin 20, decode B[s.val]! = wtV spanIdx[s.val]! := by
    intro s
    have hs' : s.val < spanIdx.size := by rw [hs]; exact s.2
    rw [hB, getElem!_pos _ s.val (by rw [Array.size_map]; exact hs'), Array.getElem_map,
      ← getElem!_pos spanIdx s.val hs', wtArr_get (spanIdx_lt s)]
    rfl
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ m : Fin 20, v m • Pi.single m (1 : ZMod 2) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  rw [← decode_two_pow, ← he m m.2, decode_applyCols hBs, colsLin_apply]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨s, (hBget s).symm⟩)

theorem span_wtV :
    Submodule.span (ZMod 2) (Set.range fun i : Fin 891 => wtV i.val) = ⊤ := by
  rw [eq_top_iff, ← span_spanIdx]
  refine Submodule.span_mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨_, spanIdx_lt s⟩, rfl⟩

theorem linearIndependent_spanIdx :
    LinearIndependent (ZMod 2) fun s : Fin 20 => wtV spanIdx[s.val]! :=
  linearIndependent_of_top_le_span_of_card_eq_finrank span_spanIdx.ge
    (by rw [Fintype.card_fin, Module.finrank_fin_fun])

theorem size_filter_filter (p q : Nat → Bool) (l : List Nat) :
    (Array.filter q (List.filter p l).toArray).size = (l.filter fun a => p a && q a).length := by
  rw [List.filter_toArray, List.size_toArray, List.filter_filter]
  exact congrArg List.length (List.filter_congr fun a _ => Bool.and_comm _ _)

theorem meetCard_eq_length {i j : Nat} (hi : i < 891) :
    meetCard i j = ((List.range 693).filter fun a => inPlane i a && inPlane j a).length := by
  unfold meetCard
  rw [planePtsArr_get hi]
  unfold planePts
  exact size_filter_filter _ _ _

theorem meetCard_eq_card {i j : Nat} (hi : i < 891) :
    meetCard i j = (planeSet i ∩ planeSet j).card := by
  have h : (planeSet i ∩ planeSet j).map Fin.valEmbedding =
      (Finset.range 693).filter fun a => inPlane i a && inPlane j a := by
    ext a
    simp only [Finset.mem_map, Finset.mem_inter, mem_planeSet, Fin.valEmbedding_apply,
      Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
      exact ⟨b.2, hb1, hb2⟩
    · rintro ⟨ha, hb1, hb2⟩
      exact ⟨⟨a, ha⟩, ⟨hb1, hb2⟩, rfl⟩
  rw [meetCard_eq_length hi, ← Finset.card_map Fin.valEmbedding, h]
  simp only [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card, Bool.decide_eq_true]

theorem dist_parts {i j : Nat} (hi : i < 891) (hj : j < 891) :
    (meetCard i j = 0 ∨ meetCard i j = 1 ∨ meetCard i j = 5 ∨ meetCard i j = 21) ∧
      (adjM i j = decide (distB i j ≤ 1)) := by
  have h := distCheck_holds
  simp only [chkDist, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h i hi j hj
  refine ⟨?_, h2⟩
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem distB_eq_three_iff {i j : Nat} (hi : i < 891)
    (hj : j < 891) : distB i j = 3 ↔ Opp i j := by
  rw [Opp, Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero, ← meetCard_eq_card hi]
  rcases (dist_parts hi hj).1 with h | h | h | h <;> simp [distB, h]

theorem adjW_iff {i j : Nat} (hi : i < 891) (hj : j < 891) :
    adjW i j = true ↔ distB i j ≤ 1 := by
  have h := (dist_parts hi hj).2
  have hm : ∀ {k : Nat}, k < 891 → maskArr[k]! = wMask k := fun hk => by
    simp [maskArr, getElem!_pos, hk]
  have e : adjM i j = adjW i j := by
    simp only [adjM, adjW, hm hi, hm hj]
  rw [← e, h, decide_eq_true_iff]

theorem distB_le (i j : Nat) : distB i j ≤ 3 := by
  simp only [distB]
  split_ifs <;> omega

theorem linearIndependent_of_rankOK {R : Nat} {rr cc inv : Array Nat}
    (h : rankOK R rr cc inv = true) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : LinearMap.BilinForm (ZMod 2) W) (x : Nat → W)
    (hx : ∀ s t : Fin 21, f (x rr[s.val]!) (x cc[t.val]!) = bit (relB R rr[s.val]! cc[t.val]!)) :
    LinearIndependent (ZMod 2) fun s : Fin 21 => x rr[s.val]! := by
  simp only [rankOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨-, hm⟩ := h
  rw [Fintype.linearIndependent_iff]
  intro c hc u
  have hcol : ∀ t : Fin 21, ∑ s : Fin 21, c s * bit (relB R rr[s.val]! cc[t.val]!) = 0 := by
    intro t
    have := congrArg (fun w => f w (x cc[t.val]!)) hc
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun s _ => by rw [hx s t]
  have hinv : ∀ s : Fin 21, ∑ t : Fin 21, bit (relB R rr[s.val]! cc[t.val]!) *
      bit (inv[t.val]!.testBit u.val) = if s = u then 1 else 0 := by
    intro s
    have e := hm s.val s.2 u.val u.2
    have e2 := congrArg bit e
    rw [bit_foldl, ← Fin.sum_univ_eq_sum_range
      (fun t => bit (relB R rr[s.val]! cc[t]! && inv[t]!.testBit u.val)) 21] at e2
    simp only [bit_and] at e2
    rw [e2]
    by_cases hsu : s = u
    · subst hsu; simp [bit]
    · have : (s.val == u.val) = false := by simpa [Fin.ext_iff] using hsu
      simp only [this, hsu, ↓reduceIte]
      rfl
  calc c u = ∑ s : Fin 21, c s * (if s = u then 1 else 0) := by simp
    _ = ∑ s : Fin 21, c s * ∑ t : Fin 21, bit (relB R rr[s.val]! cc[t.val]!) *
          bit (inv[t.val]!.testBit u.val) := Finset.sum_congr rfl fun s _ => by rw [hinv s]
    _ = ∑ t : Fin 21, (∑ s : Fin 21, c s * bit (relB R rr[s.val]! cc[t.val]!)) *
          bit (inv[t.val]!.testBit u.val) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by simp [hcol]

theorem rank_parts :
    rankRels = #[2, 4, 6, 10, 12, 14] ∧
      ∀ r < 6, rankOK rankRels[r]! rankRows[r]! rankCols[r]! rankInv[r]! = true := by
  have h := rankCheck_holds
  simp only [chkRank, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.1, h.2⟩

theorem rankOK_lt {R : Nat} {rr cc inv : Array Nat} (h : rankOK R rr cc inv = true) :
    (∀ s < 21, rr[s]! < 891) ∧ ∀ t < 21, cc[t]! < 891 := by
  simp only [rankOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq] at h
  have hr : rr.size = 21 := h.1.1.1.1.1
  have hc : cc.size = 21 := h.1.1.1.1.2
  have hrr := h.1.1.2
  have hcc := h.1.2
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · rw [getElem!_pos rr s (by omega)]
    exact hrr _ (Array.getElem_mem _)
  · rw [getElem!_pos cc t (by omega)]
    exact hcc _ (Array.getElem_mem _)

theorem not_gram_rel {R : Nat}
    (hR : R = 2 ∨ R = 4 ∨ R = 6 ∨ R = 10 ∨ R = 12 ∨ R = 14) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] (hW : finrank (ZMod 2) W ≤ 20)
    (f : LinearMap.BilinForm (ZMod 2) W) (x : Nat → W)
    (hx : ∀ i j, i < 891 → j < 891 → f (x i) (x j) = bit (relB R i j)) : False := by
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

theorem rel_eq_of_gram {R : Nat} (hR : R < 16) (hR0 : R % 2 = 0)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (hW : finrank (ZMod 2) W ≤ 20) (f : LinearMap.BilinForm (ZMod 2) W) (x : Nat → W)
    (hx : ∀ i j, i < 891 → j < 891 → f (x i) (x j) = bit (relB R i j)) : R = 0 ∨ R = 8 := by
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

theorem relB_eight_iff {i j : Nat} (hi : i < 891)
    (hj : j < 891) : relB 8 i j = true ↔ Opp i j := by
  rw [← distB_eq_three_iff hi hj, relB]
  have : distB i j = 0 ∨ distB i j = 1 ∨ distB i j = 2 ∨ distB i j = 3 := by
    have := distB_le i j
    omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

theorem exists_linear_of_gram {K : Type*} [CommRing K] {W W' : Type*} [AddCommGroup W]
    [Module K W] [AddCommGroup W'] [Module K W'] {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm K W) (B' : LinearMap.BilinForm K W') {x : ι → W} {y : ι → W'}
    (hx : Submodule.span K (Set.range x) = ⊤) (hy : Submodule.span K (Set.range y) = ⊤)
    (hB' : ∀ v, (∀ w, B' v w = 0) → v = 0) (h : ∀ i j, B' (y i) (y j) = B (x i) (x j)) :
    ∃ L : W →ₗ[K] W', ∀ i, L (x i) = y i := by
  classical
  set Φx := Fintype.linearCombination K x
  set Φy := Fintype.linearCombination K y
  have hsurj : Function.Surjective Φx := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hx]
  have hker : LinearMap.ker Φx ≤ LinearMap.ker Φy := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply hB'
    have hj : ∀ j, B' (Φy c) (y j) = 0 := by
      intro j
      have e : B (Φx c) (x j) = 0 := by rw [hc, map_zero, LinearMap.zero_apply]
      rw [← e, Fintype.linearCombination_apply, Fintype.linearCombination_apply]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h]
    intro w
    have hw : w ∈ Submodule.span K (Set.range y) := by rw [hy]; trivial
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨j, rfl⟩ := hw; exact hj j
    | zero => exact map_zero _
    | add w w' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
    | smul a w _ h1 => rw [map_smul, h1, smul_zero]
  refine ⟨(LinearMap.ker Φx).liftQ Φy hker ∘ₗ
    ((Φx.quotKerEquivOfSurjective hsurj).symm : W →ₗ[K] _), fun i => ?_⟩
  have hxi : Φx (Pi.single i 1) = x i := by
    rw [Fintype.linearCombination_apply_single, one_smul]
  have hyi : Φy (Pi.single i 1) = y i := by
    rw [Fintype.linearCombination_apply_single, one_smul]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hxi,
    ← LinearMap.quotKerEquivOfSurjective_apply_mk Φx hsurj, LinearEquiv.symm_apply_apply,
    Submodule.liftQ_apply, hyi]

open Classical in
theorem linearIndependent_of_gram_opp
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : LinearMap.BilinForm (ZMod 2) W) (x : Nat → W)
    (hx : ∀ i j, i < 891 → j < 891 → f (x i) (x j) = if Opp i j then 1 else 0) :
    LinearIndependent (ZMod 2) fun s : Fin 20 => x spanIdx[s.val]! := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : fModel (∑ s : Fin 20, c s • wtV spanIdx[s.val]!) = 0 := by
    refine LinearMap.ext_on_range span_wtV fun j => ?_
    have := congrArg (fun w => f w (x j.val)) hc
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at this
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hx _ _ (spanIdx_lt s) j.2, fModel_wtV (spanIdx_lt s) j.2]
  have h0 : ∑ s : Fin 20, c s • wtV spanIdx[s.val]! = 0 :=
    fModel_nondegenerate fun w => by rw [key, LinearMap.zero_apply]
  intro i
  simpa using (Fintype.linearIndependent_iffₛ.mp linearIndependent_spanIdx) c 0
    (by simpa using h0) i

end CFSG.LargeExtraspecial.SMod20
