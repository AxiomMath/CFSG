module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3.FilterN

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def encL (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + b * encL b l

@[expose] def decL (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => n % b :: decL b k (n / b)

theorem encL_lt {b : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a < b) → encL b l < b ^ l.length
  | [], _ => by simp [encL]
  | a :: l, h => by
    have ha := h a (by simp)
    have hl := encL_lt (l := l) (fun x hx => h x (by simp [hx]))
    have hm : b * (encL b l + 1) ≤ b * b ^ l.length := Nat.mul_le_mul_left _ hl
    simp only [encL, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (b ^ l.length) b]
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega

theorem decL_encL {b : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a < b) → decL b l.length (encL b l) = l
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (by simp)
    have hb : 0 < b := by omega
    simp only [List.length_cons, decL, encL]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt ha, Nat.zero_add, decL_encL (fun x hx => h x (by simp [hx]))]

theorem decL_getD (b : ℕ) : ∀ (k n i : ℕ), i < k → (decL b k n).getD i 0 = n / b ^ i % b
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, 0, _ => by simp [decL]
  | k + 1, n, i + 1, h => by
    simp only [decL, List.getD_cons_succ]
    rw [decL_getD b k (n / b) i (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ']

theorem decL_getD_mod (b n j : ℕ) : (decL b 8 n).getD (j % 8) 0 = n / b ^ (j % 8) % b :=
  decL_getD b 8 n _ (Nat.mod_lt _ (by decide))

theorem decL_mod (b : ℕ) : ∀ (k n : ℕ), decL b k (n % b ^ k) = decL b k n
  | 0, _ => rfl
  | k + 1, n => by
    simp only [decL]
    rw [Nat.pow_succ', Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, decL_mod b k]

theorem range_map_wf {b : ℕ} (f : ℕ → ℕ) (hf : ∀ i, f i < b) :
    ((List.range 8).map f).length = 8 ∧ ∀ a ∈ (List.range 8).map f, a < b := by
  refine ⟨by simp, fun a ha => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  exact hf i

@[expose] def pd (p i : ℕ) : ℕ := p % 16777216 / 8 ^ i % 8

@[expose] def qd (p i : ℕ) : ℕ := p / 16777216 / 8 ^ i % 8

@[expose] def decP (v p : ℕ) : FW :=
  ⟨decL 2 8 v, decL 8 8 (p % 16777216), decL 8 8 (p / 16777216)⟩

@[expose] def mulP (p1 p2 : ℕ) : ℕ :=
  encL 8 ((List.range 8).map fun i => pd p1 (pd p2 i)) +
    16777216 * encL 8 ((List.range 8).map fun i => qd p2 (qd p1 i))

@[expose] def invP (p : ℕ) : ℕ := p / 16777216 % 16777216 + 16777216 * (p % 16777216)

@[expose] def mulV (v1 p1 v2 : ℕ) : ℕ :=
  encL 2 ((List.range 8).map fun i => (v1 / 2 ^ i % 2 + v2 / 2 ^ (qd p1 i) % 2) % 2)

@[expose] def invV (v p : ℕ) : ℕ := encL 2 ((List.range 8).map fun i => v / 2 ^ (pd p i) % 2)

@[expose] def oneP : ℕ := encL 8 (List.range 8) + 16777216 * encL 8 (List.range 8)

theorem decP_enc {v p q : List ℕ} (hv : v.length = 8) (hv' : ∀ a ∈ v, a < 2) (hp : p.length = 8)
    (hp' : ∀ a ∈ p, a < 8) (hq : q.length = 8) (hq' : ∀ a ∈ q, a < 8) :
    decP (encL 2 v) (encL 8 p + 16777216 * encL 8 q) = ⟨v, p, q⟩ := by
  have e2 := encL_lt hp'
  have e3 := encL_lt hq'
  have d1 := decL_encL hv'
  have d2 := decL_encL hp'
  have d3 := decL_encL hq'
  rw [hp] at e2 d2
  rw [hq] at e3 d3
  rw [hv] at d1
  simp only [Nat.reducePow] at e2 e3
  simp only [decP]
  have h2 : (encL 8 p + 16777216 * encL 8 q) % 16777216 = encL 8 p := by omega
  have h3 : (encL 8 p + 16777216 * encL 8 q) / 16777216 = encL 8 q := by omega
  rw [h2, h3, d1, d2, d3]

theorem decP_one : decP 0 oneP = oneF := by decide +kernel

theorem mulF_decP (v1 p1 v2 p2 : ℕ) : mulF (decP v1 p1) (decP v2 p2) =
    ⟨(List.range 8).map fun i => (v1 / 2 ^ i % 2 + v2 / 2 ^ (qd p1 i) % 2) % 2,
      (List.range 8).map fun i => pd p1 (pd p2 i),
      (List.range 8).map fun i => qd p2 (qd p1 i)⟩ := by
  unfold mulF decP
  rw [FW.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> refine List.map_congr_left fun i hi => ?_ <;>
  · have hi : i < 8 := List.mem_range.mp hi
    have e : ∀ b x, (decL b 8 x).getD i 0 = x / b ^ i % b := fun b x => decL_getD b 8 x i hi
    simp only [e, decL_getD_mod, pd, qd]

theorem decP_mul (v1 p1 v2 p2 : ℕ) :
    mulF (decP v1 p1) (decP v2 p2) = decP (mulV v1 p1 v2) (mulP p1 p2) := by
  rw [mulF_decP]
  unfold mulV mulP
  obtain ⟨a1, a2⟩ := range_map_wf (b := 2)
    (fun i => (v1 / 2 ^ i % 2 + v2 / 2 ^ (qd p1 i) % 2) % 2) fun i => Nat.mod_lt _ (by decide)
  obtain ⟨b1, b2⟩ := range_map_wf (b := 8) (fun i => pd p1 (pd p2 i))
    fun i => Nat.mod_lt _ (by decide)
  obtain ⟨c1, c2⟩ := range_map_wf (b := 8) (fun i => qd p2 (qd p1 i))
    fun i => Nat.mod_lt _ (by decide)
  exact (decP_enc a1 a2 b1 b2 c1 c2).symm

theorem decP_inv (v p : ℕ) : invF (decP v p) = decP (invV v p) (invP p) := by
  obtain ⟨a1, a2⟩ := range_map_wf (b := 2) (fun i => v / 2 ^ (pd p i) % 2)
    fun i => Nat.mod_lt _ (by decide)
  have d1 := decL_encL a2
  rw [a1] at d1
  have h2 : invP p % 16777216 = p / 16777216 % 16777216 := by unfold invP; omega
  have h3 : invP p / 16777216 = p % 16777216 := by unfold invP; omega
  have hm : decL 8 8 (p / 16777216 % 16777216) = decL 8 8 (p / 16777216) :=
    decL_mod 8 8 (p / 16777216)
  unfold invF
  simp only [decP, invV, d1, h2, h3, hm, FW.mk.injEq, and_true]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < 8 := List.mem_range.mp hi
  have e : ∀ b x, (decL b 8 x).getD i 0 = x / b ^ i % b := fun b x => decL_getD b 8 x i hi
  simp only [e, decL_getD_mod, pd]

@[expose] def letP (ps : List ℕ) (l : ℕ) : ℕ :=
  if l < ps.length then ps.getD l oneP else invP (ps.getD (l - ps.length) oneP)

@[expose] def letV (vs ps : List ℕ) (l : ℕ) : ℕ :=
  if l < ps.length then vs.getD l 0
  else invV (vs.getD (l - ps.length) 0) (ps.getD (l - ps.length) oneP)

@[expose] def evalP (ps : List ℕ) : List ℕ → ℕ
  | [] => oneP
  | l :: w => mulP (letP ps l) (evalP ps w)

@[expose] def evalV (vs ps : List ℕ) : List ℕ → ℕ
  | [] => 0
  | l :: w => mulV (letV vs ps l) (letP ps l) (evalV vs ps w)

theorem getD_map_decP (ns : List (ℕ × ℕ)) (i : ℕ) :
    (ns.map fun x => decP x.1 x.2).getD i oneF = decP (ns.getD i (0, oneP)).1 (ns.getD i (0, oneP)).2 := by
  rw [← decP_one, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ns[i]? <;> simp

theorem getD_map_snd (ns : List (ℕ × ℕ)) (i : ℕ) :
    (ns.map Prod.snd).getD i oneP = (ns.getD i (0, oneP)).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ns[i]? <;> simp

theorem getD_map_fst (ns : List (ℕ × ℕ)) (i : ℕ) :
    (ns.map Prod.fst).getD i 0 = (ns.getD i (0, oneP)).1 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ns[i]? <;> simp

theorem letterF_decP (ns : List (ℕ × ℕ)) (l : ℕ) :
    letterF (ns.map fun x => decP x.1 x.2) l =
      decP (letV (ns.map Prod.fst) (ns.map Prod.snd) l) (letP (ns.map Prod.snd) l) := by
  unfold letterF letV letP
  simp only [List.length_map]
  split_ifs
  · rw [getD_map_decP, getD_map_snd, getD_map_fst]
  · rw [getD_map_decP, getD_map_snd, getD_map_fst, decP_inv]

theorem evalF_decP (ns : List (ℕ × ℕ)) (w : List ℕ) :
    evalF (ns.map fun x => decP x.1 x.2) w =
      decP (evalV (ns.map Prod.fst) (ns.map Prod.snd) w) (evalP (ns.map Prod.snd) w) := by
  induction w with
  | nil =>
    simp only [evalF, List.map_nil, List.foldr_nil, evalV, evalP]
    exact decP_one.symm
  | cons l w ih =>
    simp only [evalF, List.map_cons, List.foldr_cons, evalV, evalP] at ih ⊢
    rw [ih, letterF_decP, decP_mul]

@[expose] def filterN (g4 : List (ℕ × ℕ)) (rels : List (List ℕ)) (cands : List FW)
    (perms : List (List ℕ × List ℕ)) (masks : List (List ℕ)) : Bool :=
  perms.all fun pq => masks.all fun l =>
    !(rels.all fun r => decide (eqPF
      (decP (evalV (g4.map Prod.fst ++ [encL 2 l])
          (g4.map Prod.snd ++ [encL 8 pq.1 + 16777216 * encL 8 pq.2]) r)
        (evalP (g4.map Prod.snd ++ [encL 8 pq.1 + 16777216 * encL 8 pq.2]) r)) oneF)) ||
      decide (∃ e ∈ cands, eqPF e ⟨l, pq.1, pq.2⟩)

theorem filterN_append (g4 : List (ℕ × ℕ)) (rels : List (List ℕ)) (cands : List FW)
    (p1 p2 : List (List ℕ × List ℕ)) (masks : List (List ℕ)) :
    filterN g4 rels cands (p1 ++ p2) masks =
      (filterN g4 rels cands p1 masks && filterN g4 rels cands p2 masks) := by
  simp only [filterN, List.all_append]

theorem filter_ok_of (D : PairData) (g4 : List (ℕ × ℕ)) (perms : List (List ℕ × List ℕ))
    (hg : [ofWr D.a, ofWr D.b, ofWr D.c, ofWr D.d] = g4.map fun x => decP x.1 x.2)
    (hp : D.goodPerms.map (fun g => ((ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q)) =
      perms)
    (hwp : ∀ pq ∈ perms, pq.1.length = 8 ∧ (∀ a ∈ pq.1, a < 8) ∧ pq.2.length = 8 ∧
      ∀ a ∈ pq.2, a < 8)
    (hwm : ∀ l ∈ masksN, l.length = 8 ∧ ∀ a ∈ l, a < 2)
    (h : filterN g4 D.rels (D.candsF.map Prod.fst) perms masksN = true) :
    ∀ g ∈ D.goodPerms, ∀ l ∈ masksN,
      (∀ r ∈ D.rels, eqPF (evalF (D.gensF ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p,
        (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩) r) oneF) →
        ∃ e ∈ D.candsF, eqPF e.1 ⟨l, (ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q⟩ := by
  intro g hg' l hl hrels
  have hmem : ((ofWr (⟨0, gp g⟩ : Wr 8)).p, (ofWr (⟨0, gp g⟩ : Wr 8)).q) ∈ perms := by
    rw [← hp]
    exact List.mem_map_of_mem hg'
  generalize (ofWr (⟨0, gp g⟩ : Wr 8)).p = P at hmem hrels ⊢
  generalize (ofWr (⟨0, gp g⟩ : Wr 8)).q = Q at hmem hrels ⊢
  obtain ⟨w1, w2, w3, w4⟩ := hwp _ hmem
  obtain ⟨w5, w6⟩ := hwm l hl
  have hx : decP (encL 2 l) (encL 8 P + 16777216 * encL 8 Q) = ⟨l, P, Q⟩ :=
    decP_enc w5 w6 w1 w2 w3 w4
  have hgens : D.gensF ⟨l, P, Q⟩ =
      (g4 ++ [(encL 2 l, encL 8 P + 16777216 * encL 8 Q)]).map fun x => decP x.1 x.2 := by
    rw [List.map_append, ← hg, List.map_singleton, hx]
    rfl
  have hsnd : g4.map Prod.snd ++ [encL 8 P + 16777216 * encL 8 Q] =
      (g4 ++ [(encL 2 l, encL 8 P + 16777216 * encL 8 Q)]).map Prod.snd := by
    simp
  have hfst : g4.map Prod.fst ++ [encL 2 l] =
      (g4 ++ [(encL 2 l, encL 8 P + 16777216 * encL 8 Q)]).map Prod.fst := by
    simp
  have hall : (D.rels.all fun r => decide (eqPF
      (decP (evalV (g4.map Prod.fst ++ [encL 2 l])
          (g4.map Prod.snd ++ [encL 8 P + 16777216 * encL 8 Q]) r)
        (evalP (g4.map Prod.snd ++ [encL 8 P + 16777216 * encL 8 Q]) r)) oneF)) = true := by
    rw [List.all_eq_true]
    intro r hr
    rw [decide_eq_true_iff, hsnd, hfst, ← evalF_decP, ← hgens]
    exact hrels r hr
  unfold filterN at h
  rw [List.all_eq_true] at h
  have h1 := h _ hmem
  rw [List.all_eq_true] at h1
  have h2 := h1 l hl
  simp only [hall, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h2
  obtain ⟨c, hc', hc''⟩ := h2
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc'
  exact ⟨e, he, hc''⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3.FilterN
