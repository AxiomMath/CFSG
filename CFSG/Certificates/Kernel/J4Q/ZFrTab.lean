module

public import Certificates.Data.Kernel.J4Q.ZFr
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem compT_assoc (a b c : List ℕ) : compT a (compT b c) = compT (compT a b) c := by
  unfold compT
  rw [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  exact (actT_comp a b x).symm

theorem compT_idT_left {t : List ℕ} (ht : lenOK t = true) : compT idT t = t := by
  obtain ⟨-, hx⟩ := lenOK_iff ht
  unfold compT
  conv_rhs => rw [← List.map_id t]
  exact List.map_congr_left fun x hx' => actT_idT (hx x hx')

theorem compT_idT_right {t : List ℕ} (ht : lenOK t = true) : compT t idT = t := by
  obtain ⟨hl, -⟩ := lenOK_iff ht
  unfold compT idT
  rw [List.map_map]
  refine List.ext_getElem (by simp [hl]) fun j hj hj' => ?_
  have hj11 : j < 11 := by simpa using hj
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [actT_two_pow t hj11, List.getD_eq_getElem _ _ (by omega)]

theorem actT_comm {p v : List ℕ} (h : compT p v = compT v p) (x : ℕ) :
    actT p (actT v x) = actT v (actT p x) := by
  rw [← actT_comp, ← actT_comp, h]

theorem comm_compT {p a b : List ℕ} (ha : compT p a = compT a p) (hb : compT p b = compT b p) :
    compT p (compT a b) = compT (compT a b) p := by
  rw [compT_assoc, ha, ← compT_assoc, hb, compT_assoc]

theorem lenOK_zfSeqT (hg : ∀ g < 3, lenOK (zcGenTabs.getD g []) = true) :
    ∀ s : List ℕ, (∀ g ∈ s, g < 3) → lenOK (zfSeqT s) = true
  | [], _ => lenOK_idT
  | g :: s, hs => by
    change lenOK (compT (zcGenTabs.getD g []) (zfSeqT s)) = true
    exact lenOK_compT (hg g (hs g List.mem_cons_self))
      (lenOK_zfSeqT hg s fun x hx => hs x (List.mem_cons_of_mem _ hx))

theorem comm_zfVs {Ts : List (List ℕ)} {p : List ℕ} (hp : lenOK p = true)
    (hc : ∀ i < 4, compT p (Ts.getD i []) = compT (Ts.getD i []) p) :
    ∀ v ∈ zfVs Ts, compT p v = compT v p := by
  intro v hv
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hv
  have key : ∀ (l : List ℕ) (acc : List ℕ), (∀ i ∈ l, i < 4) → compT p acc = compT acc p →
      compT p (l.foldl (fun acc i => if m.testBit i then compT acc (Ts.getD i []) else acc) acc) =
        compT (l.foldl (fun acc i => if m.testBit i then compT acc (Ts.getD i []) else acc) acc) p := by
    intro l
    induction l with
    | nil => intro acc _ h; exact h
    | cons i l ih =>
      intro acc hl h
      simp only [List.foldl_cons]
      refine ih _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ?_
      split_ifs
      · exact comm_compT h (hc i (hl i List.mem_cons_self))
      · exact h
  refine key _ _ (fun i hi => List.mem_range.1 hi) ?_
  rw [compT_idT_right hp, compT_idT_left hp]

@[expose] def zfAll : List (List (List ℕ)) → List (List ℕ)
  | [] => [[]]
  | lv :: C => (List.range lv.length).flatMap fun t => (zfAll C).map (t :: ·)

theorem mem_zfAll : ∀ {C : List (List (List ℕ))} {ts : List ℕ}, ts ∈ zfAll C ↔
    ts.length = C.length ∧ ∀ i < C.length, ts.getD i 0 < (C.getD i []).length
  | [], ts => by
    simp only [zfAll, List.mem_singleton, List.length_nil, Nat.not_lt_zero, false_imp_iff,
      implies_true, and_true]
    exact List.length_eq_zero_iff.symm
  | lv :: C, ts => by
    simp only [zfAll, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨t, ht, r, hr, rfl⟩
      obtain ⟨h1, h2⟩ := mem_zfAll.1 hr
      refine ⟨by simp [h1], fun i hi => ?_⟩
      rcases i with _ | i
      · simpa using ht
      · simpa using h2 i (by simpa using hi)
    · rintro ⟨h1, h2⟩
      obtain ⟨t, r, rfl⟩ : ∃ t r, ts = t :: r := by
        cases ts with
        | nil => simp at h1
        | cons t r => exact ⟨t, r, rfl⟩
      refine ⟨t, by simpa using h2 0 (by simp), r, mem_zfAll.2 ⟨by simpa using h1, fun i hi => ?_⟩, rfl⟩
      simpa using h2 (i + 1) (by simpa using hi)

theorem length_zfAll : ∀ C : List (List (List ℕ)), (zfAll C).length = (C.map List.length).prod
  | [] => rfl
  | lv :: C => by
    simp only [zfAll, List.length_flatMap, List.length_map, length_zfAll C, List.map_const',
      List.length_range, List.sum_replicate, smul_eq_mul, List.map_cons, List.prod_cons]

theorem nodup_zfAll : ∀ C : List (List (List ℕ)), (zfAll C).Nodup
  | [] => List.nodup_singleton _
  | lv :: C => by
    unfold zfAll
    rw [List.nodup_flatMap]
    refine ⟨fun t _ => (nodup_zfAll C).map fun a b h => List.cons_injective h, ?_⟩
    refine List.nodup_range.imp fun {t t'} hne => ?_
    refine List.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨r', -, e⟩ := List.mem_map.1 hx'
    exact hne (List.cons.inj e).1.symm

theorem zfChainOK_cons {lv : List (List ℕ)} {C : List (List (List ℕ))} {b : ℕ} {base : List ℕ}
    (h : zfChainOK (lv :: C) (b :: base) = true) :
    b < 2048 ∧ lv.head? = some [] ∧ (∀ s ∈ lv, ∀ g ∈ s, g < 3) ∧
      (∀ lv' ∈ C, ∀ s ∈ lv', actT (zfSeqT s) b = b) ∧
      (lv.map fun s => actT (zfSeqT s) b).Nodup ∧ zfChainOK C base = true := by
  simp only [zfChainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem zfChain_seq : ∀ {C : List (List (List ℕ))} {base : List ℕ}, zfChainOK C base = true →
    ∀ lv ∈ C, ∀ s ∈ lv, ∀ g ∈ s, g < 3
  | [], _, _ => by simp
  | lv :: C, b :: base, h => by
    obtain ⟨-, -, h3, -, -, h6⟩ := zfChainOK_cons h
    intro lv' hlv'
    rcases List.mem_cons.1 hlv' with rfl | hlv'
    · exact h3
    · exact zfChain_seq h6 lv' hlv'
  | _ :: _, [], h => by simp [zfChainOK] at h

theorem lenOK_zfP (hg : ∀ g < 3, lenOK (zcGenTabs.getD g []) = true) :
    ∀ (C : List (List (List ℕ))) (ts : List ℕ), (∀ lv ∈ C, ∀ s ∈ lv, ∀ g ∈ s, g < 3) →
      lenOK (zfP C ts) = true
  | [], _, _ => lenOK_idT
  | _ :: _, [], _ => lenOK_idT
  | lv :: C, t :: ts, hs => by
    change lenOK (compT (zfSeqT (lv.getD t [])) (zfP C ts)) = true
    refine lenOK_compT (lenOK_zfSeqT hg _ ?_) (lenOK_zfP hg C ts fun l hl => hs l (List.mem_cons_of_mem _ hl))
    intro g hgs
    by_cases ht : t < lv.length
    · rw [List.getD_eq_getElem _ _ ht] at hgs
      exact hs lv List.mem_cons_self _ (List.getElem_mem ht) g hgs
    · rw [List.getD_eq_default _ _ (by omega)] at hgs
      simp at hgs

theorem zfP_fix : ∀ (C : List (List (List ℕ))) (ts : List ℕ) {b : ℕ}, b < 2048 →
    (∀ lv ∈ C, ∀ s ∈ lv, actT (zfSeqT s) b = b) → (∀ i < C.length, ts.getD i 0 < (C.getD i []).length) →
    actT (zfP C ts) b = b
  | [], _, _, hb, _, _ => actT_idT hb
  | _ :: _, [], _, hb, _, _ => actT_idT hb
  | lv :: C, t :: ts, b, hb, hfix, hts => by
    change actT (compT (zfSeqT (lv.getD t [])) (zfP C ts)) b = b
    rw [actT_comp, zfP_fix C ts hb (fun l hl => hfix l (List.mem_cons_of_mem _ hl))
      (fun i hi => by simpa using hts (i + 1) (by simpa using hi))]
    have ht : t < lv.length := by simpa using hts 0 (by simp)
    rw [List.getD_eq_getElem _ _ ht]
    exact hfix lv List.mem_cons_self _ (List.getElem_mem ht)

theorem zfP_inj (hg : ∀ g < 3, lenOK (zcGenTabs.getD g []) = true)
    (hinj : ∀ s : List ℕ, (∀ g ∈ s, g < 3) → ∀ c < 2048, ∀ d < 2048,
      actT (zfSeqT s) c = actT (zfSeqT s) d → c = d) :
    ∀ {C : List (List (List ℕ))} {base : List ℕ}, zfChainOK C base = true →
      ∀ ts ∈ zfAll C, ∀ ts' ∈ zfAll C, zfP C ts = zfP C ts' → ts = ts'
  | [], [], _, ts, hts, ts', hts', _ => by
    simp only [zfAll, List.mem_singleton] at hts hts'
    rw [hts, hts']
  | lv :: C, b :: base, h, ts, hts, ts', hts', e => by
    obtain ⟨hb, -, hseq, hfix, hnd, hC⟩ := zfChainOK_cons h
    obtain ⟨hl, hr⟩ := mem_zfAll.1 hts
    obtain ⟨hl', hr'⟩ := mem_zfAll.1 hts'
    obtain ⟨t, r, rfl⟩ : ∃ t r, ts = t :: r := by
      cases ts with
      | nil => simp at hl
      | cons t r => exact ⟨t, r, rfl⟩
    obtain ⟨t', r', rfl⟩ : ∃ t r, ts' = t :: r := by
      cases ts' with
      | nil => simp at hl'
      | cons t r => exact ⟨t, r, rfl⟩
    have ht : t < lv.length := by simpa using hr 0 (by simp)
    have ht' : t' < lv.length := by simpa using hr' 0 (by simp)
    have hrC : ∀ i < C.length, r.getD i 0 < (C.getD i []).length :=
      fun i hi => by simpa using hr (i + 1) (by simpa using hi)
    have hrC' : ∀ i < C.length, r'.getD i 0 < (C.getD i []).length :=
      fun i hi => by simpa using hr' (i + 1) (by simpa using hi)
    change compT (zfSeqT (lv.getD t [])) (zfP C r) = compT (zfSeqT (lv.getD t' [])) (zfP C r') at e
    have eb := congrArg (fun T => actT T b) e
    simp only [actT_comp, zfP_fix C r hb hfix hrC, zfP_fix C r' hb hfix hrC'] at eb
    have htt : t = t' := by
      rw [List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ ht'] at eb
      have := (List.Nodup.getElem_inj_iff hnd (i := t) (j := t') (hi := by simpa using ht)
        (hj := by simpa using ht')).1 (by simpa using eb)
      exact this
    subst htt
    have hs : ∀ g ∈ lv.getD t [], g < 3 := by
      rw [List.getD_eq_getElem _ _ ht]
      exact hseq _ (List.getElem_mem ht)
    have hCs := zfChain_seq hC
    obtain ⟨hlen, hlt⟩ := lenOK_iff (lenOK_zfP hg C r hCs)
    obtain ⟨hlen', hlt'⟩ := lenOK_iff (lenOK_zfP hg C r' hCs)
    have er : zfP C r = zfP C r' := by
      unfold compT at e
      refine List.ext_getElem (by omega) fun j hj hj' => ?_
      have := congrArg (fun l => l[j]?) e
      simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
        Option.map_some, Option.some.injEq] at this
      exact hinj _ hs _ (by simpa using hlt _ (List.getElem_mem hj)) _
        (by simpa using hlt' _ (List.getElem_mem hj')) this
    rw [zfP_inj hg hinj hC r (mem_zfAll.2 ⟨by simpa using hl, hrC⟩) r'
      (mem_zfAll.2 ⟨by simpa using hl', hrC'⟩) er]
  | [], _ :: _, h, _, _, _, _, _ => by simp [zfChainOK] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [zfChainOK] at h

theorem zfBtGo_complete (hg : ∀ g < 3, lenOK (zcGenTabs.getD g []) = true)
    {Ts : List (List ℕ)} (hTs : ∀ T ∈ Ts, lenOK T = true) :
    ∀ (C : List (List (List ℕ))) (base bs P tup ts : List ℕ),
      zfChainOK C base = true → lenOK P = true → (∀ b ∈ bs, b < 2048) →
      (∀ lv ∈ C, ∀ s ∈ lv, ∀ b ∈ bs, actT (zfSeqT s) b = b) →
      ts ∈ zfAll C →
      (∀ T ∈ Ts, compT (compT P (zfP C ts)) T = compT T (compT P (zfP C ts))) →
      (∀ v ∈ zfVs Ts, compT (compT P (zfP C ts)) v = compT v (compT P (zfP C ts))) →
      (tup.reverse ++ ts) ∈ zfBtGo Ts (zfVs Ts) C base bs P tup
  | [], [], bs, P, tup, ts, _, hP, _, _, hts, hc, _ => by
    simp only [zfAll, List.mem_singleton] at hts
    subst hts
    have e : compT P (zfP [] []) = P := compT_idT_right hP
    rw [e] at hc
    simp only [zfBtGo, List.append_nil]
    have hall : (Ts.all fun T => compT P T == compT T P) = true :=
      List.all_eq_true.2 fun T hT => beq_iff_eq.2 (hc T hT)
    simp only [hall, ↓reduceIte]
    exact List.mem_singleton_self _
  | lv :: C, b :: base, bs, P, tup, ts, h, hP, hbs, hfixbs, hts, hc, hv => by
    obtain ⟨hb, -, hseq, hfix, -, hC⟩ := zfChainOK_cons h
    obtain ⟨hl, hr⟩ := mem_zfAll.1 hts
    obtain ⟨t, r, rfl⟩ : ∃ t r, ts = t :: r := by
      cases ts with
      | nil => simp at hl
      | cons t r => exact ⟨t, r, rfl⟩
    have ht : t < lv.length := by simpa using hr 0 (by simp)
    have hrC : ∀ i < C.length, r.getD i 0 < (C.getD i []).length :=
      fun i hi => by simpa using hr (i + 1) (by simpa using hi)
    have hs : ∀ g ∈ lv.getD t [], g < 3 := by
      rw [List.getD_eq_getElem _ _ ht]
      exact hseq _ (List.getElem_mem ht)
    set P2 := compT P (zfSeqT (lv.getD t [])) with hP2
    have hp : compT P (zfP (lv :: C) (t :: r)) = compT P2 (zfP C r) := by
      change compT P (compT (zfSeqT (lv.getD t [])) (zfP C r)) = _
      rw [compT_assoc]
    rw [hp] at hc hv
    have hagree : ∀ x ∈ bs ++ [b], actT (compT P2 (zfP C r)) x = actT P2 x := by
      intro x hx
      rw [actT_comp]
      congr 1
      rcases List.mem_append.1 hx with hx | hx
      · exact zfP_fix C r (hbs x hx) (fun l hl s hsl => hfixbs l (List.mem_cons_of_mem _ hl) s hsl x hx) hrC
      · rw [List.mem_singleton.1 hx]
        exact zfP_fix C r hb hfix hrC
    have hcons : zfCons (zfVs Ts) (bs ++ [b]) P2 = true := by
      unfold zfCons
      refine List.all_eq_true.2 fun bj hbj => List.all_eq_true.2 fun bl hbl =>
        List.all_eq_true.2 fun v hvm => ?_
      rw [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      by_cases e : actT v bj = bl
      · right
        rw [← hagree bl hbl, ← hagree bj hbj, ← e]
        exact actT_comm (hv v hvm) bj
      · left
        exact e
    have hrec := zfBtGo_complete hg hTs C base (bs ++ [b]) P2 (t :: tup) r hC
      (lenOK_compT hP (lenOK_zfSeqT hg _ hs))
      (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hbs x hx
        · rw [List.mem_singleton.1 hx]; exact hb)
      (fun l hl s hsl x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hfixbs l (List.mem_cons_of_mem _ hl) s hsl x hx
        · rw [List.mem_singleton.1 hx]; exact hfix l hl s hsl)
      (mem_zfAll.2 ⟨by simpa using hl, hrC⟩) hc hv
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hrec
    simp only [zfBtGo, List.mem_flatMap, List.mem_range]
    refine ⟨t, ht, ?_⟩
    rw [← hP2]
    simp only [hcons, ↓reduceIte]
    exact hrec
  | [], _ :: _, _, _, _, _, h, _, _, _, _, _, _ => by simp [zfChainOK] at h
  | _ :: _, [], _, _, _, _, h, _, _, _, _, _, _ => by simp [zfChainOK] at h

theorem zfBt_complete (hg : ∀ g < 3, lenOK (zcGenTabs.getD g []) = true)
    {Ts : List (List ℕ)} (hTs : ∀ T ∈ Ts, lenOK T = true) {C : List (List (List ℕ))}
    {base : List ℕ} (hC : zfChainOK C base = true) {ts : List ℕ} (hts : ts ∈ zfAll C)
    (hc : ∀ i < 4, compT (zfP C ts) (Ts.getD i []) = compT (Ts.getD i []) (zfP C ts))
    (hc' : ∀ T ∈ Ts, compT (zfP C ts) T = compT T (zfP C ts)) :
    ts ∈ zfBt Ts C base := by
  have hp := lenOK_zfP hg C ts (zfChain_seq hC)
  have e : compT idT (zfP C ts) = zfP C ts := compT_idT_left hp
  have h := zfBtGo_complete hg hTs C base [] idT [] ts hC lenOK_idT (by simp) (by simp) hts
    (by rw [e]; exact hc') (by rw [e]; exact comm_zfVs hp hc)
  simpa [zfBt] using h

end CFSG.QuasithinUnique.A5

end
