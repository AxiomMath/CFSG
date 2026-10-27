module

public import Certificates.Data.Kernel.SmithL6KT
public import Certificates.Data.SmithL6Aut
public import Certificates.Data.SmithL6Faith
public import CFSG.Certificates.Kernel.SmithL6KSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel

theorem chkTvList_holds : chkTvList = true := by
  unfold chkTvList
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  refine ⟨⟨⟨tvList_size, fun k hk => ?_⟩, fun n hn => ?_⟩, fun n hn => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := tvP_tvPair hk
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, tvIdxTab_code hk⟩
  · by_cases h : ∃ k < 1953, codeOf (tvPair k) = n
    · obtain ⟨k, hk, rfl⟩ := h
      have hp := tvP_tvPair hk
      have e : ∀ p : Nat × Nat, TvP p → p = (codeOf p / 64, codeOf p % 64) := fun p hp => by
        rw [codeOf_div hp, codeOf_mod hp]
      rw [tvIdxTab_code hk]
      exact ⟨by omega, Or.inr (e _ hp)⟩
    · simp only [not_exists, not_and] at h
      rw [tvIdxTab_none hn h]
      exact ⟨Nat.le_refl _, Or.inl rfl⟩
  · by_cases h1 : n / 64 = 0
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : n % 64 = 0
    · exact Or.inl (Or.inl (Or.inr h2))
    cases h3 : form (n % 64) (n / 64)
    · have hp : TvP (n / 64, n % 64) := ⟨by omega, Nat.mod_lt _ (by omega), h1, h2, h3⟩
      obtain ⟨k, hk, he⟩ := tvPair_surj hp
      have hc : codeOf (tvPair k) = n := by
        rw [he]
        unfold codeOf
        omega
      rw [← hc, tvIdxTab_code hk]
      exact Or.inr hk
    · exact Or.inl (Or.inr rfl)

theorem chkTvImg_holds : chkTvImg = true := by
  unfold chkTvImg
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  intro j hj a ha
  rw [tvTab_get hj ha, tvTab_get hj (tvImg_lt hj ha)]
  exact ⟨tvImg_lt hj ha, tvImg_tvImg hj ha⟩

theorem find?_congr {l : List Nat} {p q : Nat → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem Reach.roots {n m : Nat} {isRoot isRoot' : Nat → Bool} {edge : Nat → Nat → Nat → Bool}
    (h : Reach n m isRoot edge) (hr : ∀ v < n, isRoot v = true → isRoot' v = true) :
    Reach n m isRoot' edge :=
  fun Q hroot hstep => h Q (fun v hv hv' => hroot v hv (hr v hv hv')) hstep

theorem all_all_congr {l : List Nat} {f g : Nat → Nat → Bool}
    (h : ∀ a ∈ l, ∀ b ∈ l, f a b = g a b) :
    (l.all fun a => l.all fun b => f a b) = (l.all fun a => l.all fun b => g a b) := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun H a ha b hb => (h a ha b hb) ▸ H a ha b hb,
    fun H a ha b hb => (h a ha b hb).symm ▸ H a ha b hb⟩

section Packed

variable {C I : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
  (hI : ∀ n < 4096, fldW 11 I n = tvIdxTab[n]!)
include hC

theorem stabCls_eq {a : Nat} (ha : a < 1953) : stabCls a = stabClsK C a := by
  have h0 := tvP_tvPair (k := 0) (by omega)
  have h1 := tvP_tvPair ha
  unfold stabCls stabClsK
  rw [hC a ha, hC 0 (by omega), codeOf_div h0, codeOf_mod h0, codeOf_div h1, codeOf_mod h1]

theorem stabRep_eq {c : Nat} (hc : c < 7) : stabRep c = (repsK C).getD c 0 := by
  unfold stabRep stabReps repsK
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_map, Array.getElem_range,
    getD_of_lt (by simpa using hc), List.getElem_map, List.getElem_range]
  rw [find?_congr (q := fun a => stabClsK C a == c)
    fun a ha => by rw [stabCls_eq hC (List.mem_range.mp ha)]]

include hI

theorem convReach {recs : List (Nat × Nat × Nat)}
    (h : treeK 1953 1953 (· == 0) (convEdgeK C I) [0] recs = true) :
    Reach 1953 1953 (· == 0) (fun g u v => tvImg g u == v) :=
  (reach_of_treeK h).mono fun g hg u hu _ _ he => ⟨g, hg, by
    unfold convEdgeK at he
    rwa [tvImgP_eq hC hI hg hu] at he⟩

theorem stabReach {roots : List Nat} {recs : List (Nat × Nat × Nat)}
    (h : treeK 1953 1953 (fun a => roots.contains a) (stabEdgeK C I) roots recs = true)
    (hreps : repsK C = roots)
    (hcls : (List.range 7).all (fun c => stabClsK C (roots.getD c 0) == c) = true) :
    Reach 1953 1953 (fun a => a == stabRep (stabCls a))
      (fun g u v => tvImg g 0 == 0 && tvImg g u == v && stabCls u == stabCls v) := by
  refine ((reach_of_treeK h).roots fun v hv hr => ?_).mono fun g hg u hu v hv he => ⟨g, hg, ?_⟩
  · have hm : v ∈ roots := List.contains_iff_mem.mp hr
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hm
    have hl : roots.length = 7 := by rw [← hreps, repsK, List.length_map, List.length_range]
    have hc7 : c < 7 := hl ▸ hc
    have e := List.all_eq_true.mp hcls c (List.mem_range.mpr hc7)
    rw [beq_iff_eq, getD_of_lt hc] at e
    rw [beq_iff_eq, stabCls_eq hC hv, e, stabRep_eq hC hc7, hreps, getD_of_lt hc]
  · unfold stabEdgeK at he
    rwa [tvImgP_eq hC hI hg (by omega), tvImgP_eq hC hI hg hu, ← stabCls_eq hC hu,
      ← stabCls_eq hC hv] at he

theorem fixK_sound : ∀ (W : List Nat) (b : Nat), fixK C I b W = true → ∀ b', b ≤ b' → b' < 1953 →
    b' = 0 ∨ ∃ q < 1953, tvImg q 0 = 0 ∧ tvImg q b' ≠ b'
  | [], b, h => fun b' h1 h2 => by
    have h' : decide (1953 ≤ b) = true := h
    have := of_decide_eq_true h'
    omega
  | q :: W, b, h => fun b' h1 h2 => by
    have h' : ((b == 0 || decide (q < 1953) && tvImgP C I q 0 == 0 && tvImgP C I q b != b) &&
        fixK C I (b + 1) W) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · subst e
      have hb := h'.1
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
        bne_iff_ne, ne_eq] at hb
      rcases hb with hb | ⟨⟨hq, h0⟩, hm⟩
      · exact Or.inl hb
      · rw [tvImgP_eq hC hI hq (by omega)] at h0
        rw [tvImgP_eq hC hI hq h2] at hm
        exact Or.inr ⟨q, hq, h0, hm⟩
    · exact fixK_sound W (b + 1) h'.2 b' hlt h2

theorem chkPtFix_of_fixK {W : List Nat} (h : fixK C I 0 W = true) : chkPtFix = true := by
  unfold chkPtFix
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    Bool.and_eq_true, bne_iff_ne, ne_eq]
  intro b hb
  rcases fixK_sound hC hI W 0 h b (Nat.zero_le b) hb with h0 | ⟨q, hq, h1, h2⟩
  · exact Or.inl h0
  · refine Or.inr ⟨q, hq, ?_, ?_⟩
    · rw [tvTab_get hq (by omega)]
      exact h1
    · rw [tvTab_get hq hb]
      exact h2

omit hI in
theorem chkStabCard_of (h : stabCardK C = true) : chkStabCard = true := by
  have e : (fun c => ((List.range 1953).filter fun a => stabCls a == c).length == stabSizes[c]!) =
      fun c => ((List.range 1953).filter fun a => stabClsK C a == c).length == stabSizes[c]! := by
    funext c
    rw [List.filter_congr (q := fun a => stabClsK C a == c)
      fun a ha => by rw [stabCls_eq hC (List.mem_range.mp ha)]]
  unfold chkStabCard
  rw [e]
  exact h

theorem chkStabComm_of (h : stabCommK C I = true) : chkStabComm = true := by
  have hA : (List.range 1953).filter (fun a => decide (stabCls a ≤ 1)) =
      (List.range 1953).filter (fun a => decide (stabClsK C a ≤ 1)) :=
    List.filter_congr fun a ha => by rw [stabCls_eq hC (List.mem_range.mp ha)]
  have hB : (List.range 1953).filter (fun a => stabCls a == 0 || stabCls a == 2) =
      (List.range 1953).filter (fun a => stabClsK C a == 0 || stabClsK C a == 2) :=
    List.filter_congr fun a ha => by rw [stabCls_eq hC (List.mem_range.mp ha)]
  have hl : ∀ (p : Nat → Bool), ∀ a ∈ (List.range 1953).filter p, ∀ b ∈ (List.range 1953).filter p,
      (tvImg a b == b) = (tvImgP C I a b == b) := fun p a ha b hb => by
    rw [tvImgP_eq hC hI (List.mem_range.mp (List.mem_filter.mp ha).1)
      (List.mem_range.mp (List.mem_filter.mp hb).1)]
  unfold chkStabComm
  unfold stabCommK at h
  simp only at h ⊢
  rw [hA, hB, all_all_congr (hl _), all_all_congr (hl _), ← tvImgP_eq hC hI (j := 1) (a := 0)
    (by omega) (by omega), ← tvImgP_eq hC hI (j := 94) (a := 0) (by omega) (by omega),
    ← tvImgP_eq hC hI (j := 1) (a := 94) (by omega) (by omega)]
  exact h

end Packed

theorem decCols_nil_aux (D : List (Nat × Nat × Nat)) (acc : Nat) :
    D.foldl (fun acc e => if (([] : List Nat).getD e.2.1 0).testBit e.2.2 then acc ||| e.1 else acc)
      acc = acc := by
  induction D generalizing acc with
  | nil => rfl
  | cons e D ih =>
    rw [List.foldl_cons, List.getD_nil, Nat.zero_testBit]
    exact ih acc

theorem decCols_nil (D : List (Nat × Nat × Nat)) : decCols D [] = 0 := decCols_nil_aux D 0

theorem getD_map_list {α β : Type} (f : α → β) (d : α) :
    ∀ (L : List α) (k : Nat), (L.map f).getD k (f d) = f (L.getD k d)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => getD_map_list f d L k

theorem chkTvArrInj_of {L : List (List Nat)} {D : List (Nat × Nat × Nat)} {cs : List Nat}
    (hL : ∀ k < 1953, (tvCols k).toList = L.getD k [])
    (hcs : ∀ k < 1953, codeOf (tvPair k) = cs.getD k 0) (hdec : L.map (decCols D) = cs) :
    chkTvArrInj = true := by
  have hc : ∀ k < 1953, codeOf (tvPair k) = decCols D (L.getD k []) := fun k hk => by
    rw [hcs k hk, ← hdec, ← decCols_nil D]
    exact getD_map_list _ _ L k
  unfold chkTvArrInj
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  intro b hb a hab he
  unfold tvArr at he
  rw [ofFn_get! (fun k : Fin 1953 => tvCols k.val) (by omega),
    ofFn_get! (fun k : Fin 1953 => tvCols k.val) hb] at he
  have e := congrArg Array.toList he
  rw [hL a (by omega), hL b hb] at e
  have := codeOf_tvPair_inj (j := a) (k := b) (by omega) hb (by rw [hc a (by omega), hc b hb, e])
  omega

end CFSG.SmithL6.K
