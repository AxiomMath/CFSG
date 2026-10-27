module

public import CFSG.GF2Type.SmithTypeE.LMod.Basic
public import CFSG.LargeExtraspecial.SMod20Rho
public import Certificates.Certificate38602

public section

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6 Module
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_apply decode_xor decode_zero decode_two_pow
  eq_of_decode_eq colsLin colsLin_apply colsLin_single decode_applyCols linearMap_ext_single
  linearEquiv_ext_single bit bit_xor bit_and bit_foldl decode_apply_bit exists_linear_of_gram)

theorem spanWCheck_holds : chkSpanW = true :=
  Certificates.certificate38602.1

theorem rankCheck_holds : chkRank = true :=
  Certificates.certificate38602.2

theorem spanW_parts :
    spanIdx.size = 20 ∧ (∀ i ∈ spanIdx, i < 1395) ∧ ∀ m < 20,
      applyCols (spanIdx.map fun i => wtArr[i]!) spanCoef[m]! = 2 ^ m := by
  have h := spanWCheck_holds
  simp only [chkSpanW, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true', decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.2, h.2⟩

theorem spanIdx_lt (s : Fin 20) : spanIdx[s.val]! < 1395 := by
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
    Submodule.span (ZMod 2) (Set.range fun i : Fin 1395 => wtV i.val) = ⊤ := by
  rw [eq_top_iff, ← span_spanIdx]
  refine Submodule.span_mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨_, spanIdx_lt s⟩, rfl⟩

theorem linearIndependent_spanIdx :
    LinearIndependent (ZMod 2) fun s : Fin 20 => wtV spanIdx[s.val]! :=
  linearIndependent_of_top_le_span_of_card_eq_finrank span_spanIdx.ge
    (by rw [Fintype.card_fin, Module.finrank_fin_fun])

theorem dist_parts {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    (meetCard i j = 0 ∨ meetCard i j = 1 ∨ meetCard i j = 9 ∨ meetCard i j = 49) ∧
      (adjM i j = decide (distB i j ≤ 1)) := by
  obtain ⟨h1, h2, -, h4⟩ := pairs_parts hi hj
  have hc : meetCard i j = 0 ∨ meetCard i j = 1 ∨ meetCard i j = 9 ∨ meetCard i j = 49 := by
    by_cases hij : i = j
    · exact Or.inr (Or.inr (Or.inr (h1 hij)))
    · rcases h2 hij with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  refine ⟨hc, ?_⟩
  rw [h4]
  rcases hc with h | h | h | h <;> simp [distB, h]

theorem distB_eq_three_iff {i j : Nat} (hi : i < 1395)
    (hj : j < 1395) : distB i j = 3 ↔ Opp i j := by
  rw [opp_iff_meetCard hi hj]
  rcases (dist_parts hi hj).1 with h | h | h | h <;> simp [distB, h]

theorem adjW_iff {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    adjW i j = true ↔ distB i j ≤ 1 := by
  have h := (dist_parts hi hj).2
  have hm : ∀ {k : Nat}, k < 1395 → maskArr[k]! = wMask k := fun hk => by
    simp [maskArr, getElem!_pos, hk]
  have e : adjM i j = adjW i j := by
    simp only [adjM, adjW, hm hi, hm hj]
  rw [← e, h, decide_eq_true_iff]

theorem distB_le (i j : Nat) : distB i j ≤ 3 := by
  simp only [distB]
  split <;> try omega
  split <;> try omega
  split <;> omega

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
    (∀ s < 21, rr[s]! < 1395) ∧ ∀ t < 21, cc[t]! < 1395 := by
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
    (hx : ∀ i j, i < 1395 → j < 1395 → f (x i) (x j) = bit (relB R i j)) : False := by
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
    (hx : ∀ i j, i < 1395 → j < 1395 → f (x i) (x j) = bit (relB R i j)) : R = 0 ∨ R = 8 := by
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

theorem relB_eight_iff {i j : Nat} (hi : i < 1395)
    (hj : j < 1395) : relB 8 i j = true ↔ Opp i j := by
  rw [← distB_eq_three_iff hi hj, relB]
  have : distB i j = 0 ∨ distB i j = 1 ∨ distB i j = 2 ∨ distB i j = 3 := by
    have := distB_le i j
    omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

open Classical in
theorem linearIndependent_of_gram_opp
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : LinearMap.BilinForm (ZMod 2) W) (x : Nat → W)
    (hx : ∀ i j, i < 1395 → j < 1395 → f (x i) (x j) = if Opp i j then 1 else 0) :
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

end CFSG.GF2Type.SmithTypeE.LMod
