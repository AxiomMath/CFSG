module

public import Certificates.Data.Kernel.Misc.G22W
public import CFSG.Certificates.Kernel.Mat8PSound
public import CFSG.Certificates.Kernel.G2Three.Tables
public import CFSG.Quasithin.H13.L32NKGCertInputs

public section

namespace CFSG.KC.G22W

open CFSG.KD.G22W CFSG.KD.BfsK CFSG.KC.Mat8P CFSG.Quasithin.H13.KGCert

@[expose] def colsK (x : ℕ) : List ℕ :=
  [Nat.land x 255, Nat.land (Nat.shiftRight x 8) 255, Nat.land (Nat.shiftRight x 16) 255,
    Nat.land (Nat.shiftRight x 24) 255, Nat.land (Nat.shiftRight x 32) 255,
    Nat.land (Nat.shiftRight x 40) 255]

@[expose] def VC (a : List ℕ) : Prop := a.length = 6 ∧ ∀ c ∈ a, c < 64

theorem unpackM_cols (x : ℕ) : unpackM x = colsK x ++
    [Nat.land (Nat.shiftRight x 48) 255, Nat.land (Nat.shiftRight x 56) 255] := rfl

theorem good_facts {x : ℕ} (h : goodK x = true) :
    unpackM x = colsK x ++ [64, 128] ∧ VC (colsK x) := by
  simp only [goodK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨?_, rfl, ?_⟩
  · rw [unpackM_cols, h6, h7]
  · intro c hc
    simp only [colsK, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem mv8_app (a : List ℕ) (ha : a.length = 6) (v : ℕ) (hv : v < 64) :
    CFSG.Quasithin.H13.Mat8Cert.mv8 (a ++ [64, 128]) v = mulVecC a v := by
  have h6 : v.testBit 6 = false := Nat.testBit_lt_two_pow (by omega)
  have h7 : v.testBit 7 = false := Nat.testBit_lt_two_pow (by omega)
  match a, ha with
  | [a0, a1, a2, a3, a4, a5], _ =>
    simp only [CFSG.Quasithin.H13.Mat8Cert.mv8, mulVecC, CFSG.Quasithin.H13.Mat8Cert.bt, bt, h6,
      h7, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      Bool.false_eq_true, ↓reduceIte, Nat.xor_zero]

theorem mv8_app_64 (a : List ℕ) (ha : a.length = 6) :
    CFSG.Quasithin.H13.Mat8Cert.mv8 (a ++ [64, 128]) 64 = 64 ∧
      CFSG.Quasithin.H13.Mat8Cert.mv8 (a ++ [64, 128]) 128 = 128 := by
  match a, ha with
  | [a0, a1, a2, a3, a4, a5], _ =>
    constructor <;> simp only [CFSG.Quasithin.H13.Mat8Cert.mv8, CFSG.Quasithin.H13.Mat8Cert.bt,
      List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      (by decide : Nat.testBit 64 0 = false), (by decide : Nat.testBit 64 1 = false),
      (by decide : Nat.testBit 64 2 = false), (by decide : Nat.testBit 64 3 = false),
      (by decide : Nat.testBit 64 4 = false), (by decide : Nat.testBit 64 5 = false),
      (by decide : Nat.testBit 64 6 = true), (by decide : Nat.testBit 64 7 = false),
      (by decide : Nat.testBit 128 0 = false), (by decide : Nat.testBit 128 1 = false),
      (by decide : Nat.testBit 128 2 = false), (by decide : Nat.testBit 128 3 = false),
      (by decide : Nat.testBit 128 4 = false), (by decide : Nat.testBit 128 5 = false),
      (by decide : Nat.testBit 128 6 = false), (by decide : Nat.testBit 128 7 = true),
      Bool.false_eq_true, ↓reduceIte, Nat.zero_xor, Nat.xor_zero]

theorem mul8_app (a b : List ℕ) (ha : a.length = 6) (hb : VC b) :
    CFSG.Quasithin.H13.Mat8Cert.mul8 (a ++ [64, 128]) (b ++ [64, 128]) = mulC a b ++ [64, 128] := by
  obtain ⟨h1, h2⟩ := mv8_app_64 a ha
  rw [CFSG.Quasithin.H13.Mat8Cert.mul8, List.map_append, mulC]
  congr 1
  · exact List.map_congr_left fun v hv => mv8_app a ha v (hb.2 v hv)
  · simp only [List.map_cons, List.map_nil, h1, h2]

theorem mulP_cols {x y : ℕ} {a b : List ℕ} (hx : unpackM x = a ++ [64, 128]) (ha : a.length = 6)
    (hy : unpackM y = b ++ [64, 128]) (hb : VC b) :
    unpackM (mulP x y) = mulC a b ++ [64, 128] := by
  rw [← mul8_unpackM, hx, hy, mul8_app a b ha hb]

theorem cols_inj {x y : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hgx : goodK x = true)
    (hgy : goodK y = true) (h : colsK x = colsK y) : x = y :=
  unpackM_inj hx hy (by rw [(good_facts hgx).1, (good_facts hgy).1, h])

theorem recX_lt (R : ℕ → ℕ) (o t : ℕ) : recX R o t < 2 ^ 64 :=
  lt_of_le_of_lt Nat.and_le_right (by unfold M64; norm_num)

theorem mvK_eq {x : ℕ} (h : goodK x = true) (v : ℕ) (hv : v < 64) :
    mvK x v = mulVecC (colsK x) v := by
  rw [mvK, mv8R_eq, (good_facts h).1, mv8_app _ rfl v hv]

theorem oneP_cols : unpackM oneP = oneC ++ [64, 128] := oneP_eq

theorem code36_inj {a b : List ℕ} (ha : VC a) (hb : VC b) (h : code36 a = code36 b) :
    a = b := by
  obtain ⟨la, ca⟩ := ha
  obtain ⟨lb, cb⟩ := hb
  match a, la, b, lb with
  | [a0, a1, a2, a3, a4, a5], _, [b0, b1, b2, b3, b4, b5], _ =>
    have := ca a0 (by simp); have := ca a1 (by simp); have := ca a2 (by simp)
    have := ca a3 (by simp); have := ca a4 (by simp); have := ca a5 (by simp)
    have := cb b0 (by simp); have := cb b1 (by simp); have := cb b2 (by simp)
    have := cb b3 (by simp); have := cb b4 (by simp); have := cb b5 (by simp)
    simp only [code36, List.foldr_cons, List.foldr_nil] at h
    simp only [List.cons.injEq, and_true]
    omega

section Recs

variable {R : ℕ → ℕ} {n hi : ℕ}

@[expose] noncomputable def E (R : ℕ → ℕ) (t : ℕ) : List ℕ := colsK (numX R t)

@[expose] def gC (g : Bool) : List ℕ := if g then gAc else gBc

theorem prod_raw (hP : prodK R n hi = true) (hm : n ≤ 64 * hi) :
    ∀ t < n, goodK (numX R t) = true ∧ posQ R t true < n ∧
      mulP (R 0) (numX R t) = numX R (posQ R t true) ∧ posQ R t false < n ∧
      mulP (R 1) (numX R t) = numX R (posQ R t false) := by
  intro t ht
  have h := CFSG.KC.G2Three.allBelow_g2 hP hm t ht
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem eq_of_unpack {x : ℕ} {a b : List ℕ} (hx : unpackM x = b ++ [64, 128])
    (h : unpackM x = a ++ [64, 128]) : a = b := by
  rw [hx] at h
  exact (List.append_cancel_right h).symm

theorem prod_facts (hP : prodK R n hi = true) (hm : n ≤ 64 * hi)
    (hA : unpackM (R 0) = gAc ++ [64, 128]) (hB : unpackM (R 1) = gBc ++ [64, 128]) :
    ∀ t < n, goodK (numX R t) = true ∧ VC (E R t) ∧ ∀ g, posQ R t g < n ∧
      mulC (gC g) (E R t) = E R (posQ R t g) := by
  intro t ht
  obtain ⟨hg, hq1, he1, hq2, he2⟩ := prod_raw hP hm t ht
  obtain ⟨hu, hv⟩ := good_facts hg
  refine ⟨hg, hv, fun g => ?_⟩
  cases g
  · refine ⟨hq2, ?_⟩
    have hu' := (good_facts (prod_raw hP hm _ hq2).1).1
    exact eq_of_unpack hu' (by rw [← he2]; exact mulP_cols hB rfl hu hv)
  · refine ⟨hq1, ?_⟩
    have hu' := (good_facts (prod_raw hP hm _ hq1).1).1
    exact eq_of_unpack hu' (by rw [← he1]; exact mulP_cols hA rfl hu hv)

theorem E_inj (hP : prodK R n hi = true) (hm : n ≤ 64 * hi) {hiT : ℕ}
    (hT : sortX R n hiT = true) (hTm : n ≤ 64 * hiT) :
    ∀ t < n, ∀ t' < n, E R t = E R t' → t = t' := by
  intro t ht t' ht' h
  exact CFSG.KC.G2Three.sort_inj hT hTm t ht t' ht' (cols_inj (recX_lt R 2 t) (recX_lt R 2 t')
    (prod_raw hP hm t ht).1 (prod_raw hP hm t' ht').1 h)

abbrev SW := Std.HashSet (List ℕ) × List (List Bool) × List (List Bool × List ℕ)

abbrev SI := ℕ × Bool × List ℕ × List ℕ

def Rel (R : ℕ → ℕ) (n : ℕ) (a : SW) (b : SI) : Prop :=
  b.2.1 = true → b.1 ≤ n ∧ (∀ y, a.1.contains y = true ↔ ∃ t < b.1, E R t = y) ∧
    a.2.1.map evalWord = b.2.2.1.map (E R) ∧ a.2.2.map Prod.snd = b.2.2.2.map (E R) ∧
    (∀ p ∈ a.2.2, p.2 = evalWord p.1) ∧ ∀ t ∈ b.2.2.2, t < n

def stepH (wx : List Bool × List ℕ) (st : SW) (g : Bool) : SW :=
  let y := mulC (if g then gAc else gBc) wx.2
  if st.1.contains y then st else (st.1.insert y, (g :: wx.1) :: st.2.1, (g :: wx.1, y) :: st.2.2)

theorem step_rel
    (hfac : ∀ t < n, VC (E R t) ∧ ∀ g, posQ R t g < n ∧ mulC (gC g) (E R t) = E R (posQ R t g))
    (hinj : ∀ t < n, ∀ t' < n, E R t = E R t' → t = t') {t : ℕ} (ht : t < n)
    {wx : List Bool × List ℕ} (hw1 : wx.2 = E R t) (hw2 : wx.2 = evalWord wx.1) (g : Bool)
    (a : SW) (b : SI) (h : Rel R n a b) : Rel R n (stepH wx a g) (stepI (posQ R) t b g) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨c, ok, acc, fr⟩ := b
  obtain ⟨hq, hmul⟩ := (hfac t ht).2 g
  have hy : mulC (if g then gAc else gBc) wx.2 = E R (posQ R t g) := by
    rw [hw1]
    exact hmul
  have hev : evalWord (g :: wx.1) = E R (posQ R t g) := by
    rw [← hy, hw2]
    rfl
  unfold Rel at h ⊢
  unfold stepH
  simp only [stepI, Nat.add_eq] at h ⊢
  rw [hy]
  by_cases hlt : posQ R t g < c
  · rw [Nat.blt_eq.mpr hlt, cond_true]
    intro hok
    have hin : a1.contains (E R (posQ R t g)) = true := ((h hok).2.1 _).2 ⟨_, hlt, rfl⟩
    rw [if_pos hin]
    exact h hok
  · have hb : Nat.blt (posQ R t g) c = false := by
      cases hc : Nat.blt (posQ R t g) c
      · rfl
      · exact absurd (Nat.blt_eq.mp hc) hlt
    rw [hb, cond_false]
    by_cases heq : posQ R t g = c
    · rw [Nat.beq_eq.mpr heq, cond_true]
      intro hok
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h hok
      have hout : a1.contains (E R (posQ R t g)) = false := by
        cases hm : a1.contains (E R (posQ R t g))
        · rfl
        · obtain ⟨t', ht', he⟩ := (h2 _).1 hm
          have := hinj t' (by omega) _ hq he
          omega
      rw [if_neg (by rw [hout]; exact Bool.false_ne_true)]
      refine ⟨by omega, fun y => ?_, ?_, ?_, ?_, ?_⟩
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, h2]
        constructor
        · rintro (e | ⟨t', ht', e⟩)
          · exact ⟨c, by omega, by rw [← heq]; exact e⟩
          · exact ⟨t', by omega, e⟩
        · rintro ⟨t', ht', e⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | ht'
          · exact Or.inr ⟨t', ht', e⟩
          · subst ht'
            exact Or.inl (by rw [heq]; exact e)
      · simp only [List.map_cons, h3, hev]
      · simp only [List.map_cons, h4]
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hev.symm
        · exact h5 p hp
      · intro t' ht'
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact hq
        · exact h6 t' ht'
    · have hb' : Nat.beq (posQ R t g) c = false := by
        cases hc : Nat.beq (posQ R t g) c
        · rfl
        · exact absurd (Nat.beq_eq.mp hc) heq
      rw [hb', cond_false]
      intro hok
      exact absurd hok Bool.false_ne_true

theorem runI_cons (Q : ℕ → Bool → ℕ) (t : ℕ) (l : List ℕ) (st : SI) :
    runI Q (t :: l) st = runI Q l (stepI Q t (stepI Q t st true) false) := by
  simp only [runI] <;> rfl

theorem fold_rel
    (hfac : ∀ t < n, VC (E R t) ∧ ∀ g, posQ R t g < n ∧ mulC (gC g) (E R t) = E R (posQ R t g))
    (hinj : ∀ t < n, ∀ t' < n, E R t = E R t' → t = t') :
    ∀ (fr : List (List Bool × List ℕ)) (frP : List ℕ), fr.map Prod.snd = frP.map (E R) →
      (∀ p ∈ fr, p.2 = evalWord p.1) → (∀ t ∈ frP, t < n) → ∀ (a : SW) (b : SI), Rel R n a b →
      Rel R n (fr.foldl (fun st wx => [true, false].foldl (stepH wx) st) a) (runI (posQ R) frP b)
  | [], [], _, _, _, _, _, h => by simpa [runI] using h
  | [], _ :: _, he, _, _, _, _, _ => by simp at he
  | _ :: _, [], he, _, _, _, _, _ => by simp at he
  | wx :: fr, t :: frP, he, hw, ht, a, b, h => by
    simp only [List.map_cons, List.cons.injEq] at he
    rw [List.foldl_cons, runI_cons]
    have ht0 := ht t List.mem_cons_self
    have hw0 := hw wx List.mem_cons_self
    refine fold_rel hfac hinj fr frP he.2 (fun p hp => hw p (List.mem_cons_of_mem _ hp))
      (fun t' ht' => ht t' (List.mem_cons_of_mem _ ht')) _ _ ?_
    simp only [List.foldl_cons, List.foldl_nil]
    exact step_rel hfac hinj ht0 he.1 hw0 false _ _ (step_rel hfac hinj ht0 he.1 hw0 true _ _ h)

theorem stepI_false (Q : ℕ → Bool → ℕ) (t : ℕ) :
    ∀ (st : SI) (g : Bool), st.2.1 = false → (stepI Q t st g).2.1 = false
  | (c, ok, acc, fr), g, h => by
    simp only at h
    subst h
    simp only [stepI]
    cases Nat.blt (Q t g) c <;> cases Nat.beq (Q t g) c <;> rfl

theorem runI_false (Q : ℕ → Bool → ℕ) :
    ∀ (l : List ℕ) (st : SI), st.2.1 = false → (runI Q l st).2.1 = false
  | [], _, h => h
  | t :: l, st, h => by
    rw [runI_cons]
    exact runI_false Q l _ (stepI_false Q t _ _ (stepI_false Q t _ _ h))

theorem bfsI_cons (Q : ℕ → Bool → ℕ) (fuel c : ℕ) (ok : Bool) (acc : List ℕ) (t : ℕ)
    (fr : List ℕ) :
    bfsI Q (fuel + 1) c ok acc (t :: fr) =
      bfsI Q fuel (runI Q (t :: fr) (c, ok, acc, [])).1 (runI Q (t :: fr) (c, ok, acc, [])).2.1
        (runI Q (t :: fr) (c, ok, acc, [])).2.2.1 (runI Q (t :: fr) (c, ok, acc, [])).2.2.2 := by
  simp only [bfsI] <;> rfl

theorem bfsI_false (Q : ℕ → Bool → ℕ) :
    ∀ (fuel c : ℕ) (ok : Bool) (acc fr : List ℕ), ok = false → (bfsI Q fuel c ok acc fr).1 = false
  | 0, _, _, _, _, h => h
  | _ + 1, _, _, _, [], h => h
  | fuel + 1, c, ok, acc, t :: fr, h => by
    rw [bfsI_cons]
    exact bfsI_false Q fuel _ _ _ _ (runI_false Q _ _ h)

theorem bfs_rel
    (hfac : ∀ t < n, VC (E R t) ∧ ∀ g, posQ R t g < n ∧ mulC (gC g) (E R t) = E R (posQ R t g))
    (hinj : ∀ t < n, ∀ t' < n, E R t = E R t' → t = t') :
    ∀ (fuel : ℕ) (a : SW) (b : SI), Rel R n a b →
      (bfsI (posQ R) fuel b.1 b.2.1 b.2.2.1 b.2.2.2).1 = true →
      (bfsWords fuel a.1 a.2.1 a.2.2).map evalWord =
        (bfsI (posQ R) fuel b.1 b.2.1 b.2.2.1 b.2.2.2).2.map (E R)
  | 0, _, _, h, hok => (h hok).2.2.1
  | fuel + 1, ⟨a1, a2, a3⟩, ⟨c, ok, acc, fr⟩, h, hok => by
    dsimp only at hok ⊢
    cases ok with
    | false =>
      rw [bfsI_false _ _ _ _ _ _ rfl] at hok
      exact absurd hok Bool.false_ne_true
    | true =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h rfl
      dsimp only at h1 h2 h3 h4 h5 h6
      match a3, fr, h4, h5, h6, hok with
      | [], [], _, _, _, _ => simp only [bfsWords, bfsI]; exact h3
      | [], _ :: _, he, _, _, _ => simp at he
      | _ :: _, [], he, _, _, _ => simp at he
      | wx :: a3', t :: fr', he, h5', h6', hok' =>
        rw [bfsI_cons] at hok' ⊢
        simp only [bfsWords]
        exact bfs_rel hfac hinj fuel _ _ (fold_rel hfac hinj (wx :: a3') (t :: fr') he h5' h6'
          (a1, a2, []) (c, true, acc, []) (fun _ => ⟨h1, h2, h3, rfl, by simp, by simp⟩)) hok'

theorem isDesc_eq : ∀ (l : List ℕ) (n : ℕ), isDesc l n = true → l = (List.range n).reverse
  | [], n, h => by
    simp only [isDesc, Nat.beq_eq] at h
    subst h
    rfl
  | _ :: _, 0, h => by simp [isDesc] at h
  | x :: l, n + 1, h => by
    simp only [isDesc, Bool.and_eq_true, Nat.beq_eq] at h
    rw [isDesc_eq l n h.2, h.1, List.range_succ, List.reverse_append]
    rfl

theorem colsK_oneP : colsK oneP = oneC := by decide

theorem g22Elems_eq (hS : searchK R n = true) (hn : 0 < n)
    (hfac : ∀ t < n, VC (E R t) ∧ ∀ g, posQ R t g < n ∧ mulC (gC g) (E R t) = E R (posQ R t g))
    (hinj : ∀ t < n, ∀ t' < n, E R t = E R t' → t = t') :
    E R 0 = oneC ∧ g22Elems = (List.range n).reverse.map (E R) := by
  simp only [searchK, Bool.and_eq_true, Nat.beq_eq] at hS
  obtain ⟨h0, hok, hd⟩ := hS
  have hE0 : E R 0 = oneC := by rw [E, h0, colsK_oneP]
  refine ⟨hE0, ?_⟩
  have key := bfs_rel hfac hinj 200 ((∅ : Std.HashSet (List ℕ)).insert oneC, [[]], [([], oneC)])
    (1, true, [0], [0]) (fun _ => ⟨hn, fun y => ?_, ?_, ?_, ?_, ?_⟩) hok
  · rw [g22Elems, g22Words, key, isDesc_eq _ _ hd]
  · dsimp only
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq]
    constructor
    · rintro rfl
      exact ⟨0, Nat.one_pos, hE0⟩
    · rintro ⟨t, ht, rfl⟩
      rw [show t = 0 by omega, hE0]
  · simp [evalWord, hE0]
  · simp [hE0]
  · simp [evalWord]
  · simpa using hn

end Recs

theorem mem_map_range {R : ℕ → ℕ} {n : ℕ} {x : List ℕ} :
    x ∈ (List.range n).reverse.map (E R) ↔ ∃ t < n, E R t = x := by
  simp [List.mem_map, List.mem_reverse, List.mem_range]

theorem cert7102_of {R : ℕ → ℕ} {n hi hiT : ℕ} (hn : 0 < n) (hm : n ≤ 64 * hi)
    (hTm : n ≤ 64 * hiT) (hA : unpackM (R 0) = gAc ++ [64, 128])
    (hB : unpackM (R 1) = gBc ++ [64, 128]) (hS : searchK R n = true) (hP : prodK R n hi = true)
    (hT : sortX R n hiT = true) {o₂ : ℕ} (hW : stabK R o₂ n hi = true) :
    g22Elems.length = n ∧ oneC ∈ g22Elems ∧ g22ValidCheck = true ∧ g22ClosedCheck = true ∧
      g22StabCheck = true ∧ g22NodupCheck = true := by
  have hfac' := prod_facts hP hm hA hB
  have hfac : ∀ t < n, VC (E R t) ∧ ∀ g, posQ R t g < n ∧
      mulC (gC g) (E R t) = E R (posQ R t g) := fun t ht => (hfac' t ht).2
  have hinj := E_inj hP hm hT hTm
  obtain ⟨hE0, hEq⟩ := g22Elems_eq hS hn hfac hinj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEq, List.length_map, List.length_reverse, List.length_range]
  · rw [hEq]
    exact mem_map_range.2 ⟨0, hn, hE0⟩
  · rw [g22ValidCheck, hEq, List.all_eq_true]
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_map_range.1 hx
    obtain ⟨hl, hc⟩ := (hfac t ht).1
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨hl, hc⟩
  · simp only [g22ClosedCheck, hEq, List.all_eq_true, Bool.and_eq_true,
      Std.HashSet.contains_ofList, List.contains_iff_mem]
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_map_range.1 hx
    obtain ⟨hq1, he1⟩ := (hfac t ht).2 true
    obtain ⟨hq2, he2⟩ := (hfac t ht).2 false
    exact ⟨mem_map_range.2 ⟨_, hq1, he1.symm⟩, mem_map_range.2 ⟨_, hq2, he2.symm⟩⟩
  · rw [g22StabCheck, List.all_eq_true]
    intro v' hv'
    rw [List.mem_range] at hv'
    dsimp only
    rw [List.all_eq_true]
    intro z hz
    rw [List.mem_filter, hEq] at hz
    obtain ⟨hzm, hzv⟩ := hz
    obtain ⟨t, ht, rfl⟩ := mem_map_range.1 hzm
    rw [beq_iff_eq] at hzv
    rw [Bool.or_eq_true]
    by_cases hinv : mulC (E R t) (E R t) = oneC ∧ E R t ≠ oneC
    · right
      have hg := (hfac' t ht).1
      have hv := (hfac t ht).1
      have hu : unpackM (numX R t) = E R t ++ [64, 128] := (good_facts hg).1
      have hsq : mulP (numX R t) (numX R t) = oneP := by
        apply unpackM_inj (mulP_lt _ _) oneP_lt
        rw [mulP_cols hu hv.1 hu hv, hinv.1, oneP_cols]
      have hne : numX R t ≠ oneP := by
        intro e
        apply hinv.2
        rw [E, e, colsK_oneP]
      have hst := CFSG.KC.G2Three.allBelow_g2 hW hm t ht
      try dsimp only at hst
      have hne' : Nat.beq (numX R t) oneP = false := by
        cases hb : Nat.beq (numX R t) oneP
        · rfl
        · exact absurd (Nat.beq_eq.mp hb) hne
      rw [Nat.beq_eq.mpr hsq, hne'] at hst
      simp only [Bool.not_false, Bool.and_self, cond_true] at hst
      have hw := CFSG.KC.G2Three.allBelow_g2 hst (by norm_num) (v' + 1) (by omega)
      try dsimp only at hw
      have hv1 : Nat.beq (v' + 1) 0 = false := rfl
      have hv2 : Nat.beq (mvK (numX R t) (v' + 1)) (v' + 1) = true := by
        rw [Nat.beq_eq, mvK_eq hg _ (by omega)]
        exact hzv
      rw [hv1, hv2] at hw
      simp only [Bool.not_true, Bool.or_false, Bool.false_or, witOK, Bool.and_eq_true,
        Nat.blt_eq, Nat.beq_eq, Bool.not_eq_true'] at hw
      obtain ⟨⟨hγ, hγv⟩, hγc⟩ := hw
      set γ := witAt R o₂ (recF R 2 4 t) (v' + 1)
      have hgγ := (hfac' γ hγ).1
      have hvγ := (hfac γ hγ).1
      have huγ : unpackM (numX R γ) = E R γ ++ [64, 128] := (good_facts hgγ).1
      rw [List.any_eq_true]
      refine ⟨E R γ, List.mem_filter.2 ⟨by rw [hEq]; exact mem_map_range.2 ⟨γ, hγ, rfl⟩, ?_⟩, ?_⟩
      · rw [beq_iff_eq]
        exact (mvK_eq hgγ (v' + 1) (by omega)).symm.trans hγv
      · rw [bne_iff_ne]
        intro e
        have : mulP (numX R γ) (numX R t) = mulP (numX R t) (numX R γ) := by
          apply unpackM_inj (mulP_lt _ _) (mulP_lt _ _)
          rw [mulP_cols huγ hvγ.1 hu hv, mulP_cols hu hv.1 huγ hvγ, e]
        rw [this] at hγc
        simp at hγc
    · left
      rw [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
      rcases not_and_or.mp hinv with h | h
      · exact Or.inl h
      · exact Or.inr (not_not.mp h)
  · rw [g22NodupCheck, decide_eq_true_eq, isChain_mergeSort_iff, hEq, List.map_map]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (List.nodup_reverse.mpr List.nodup_range)
    rw [List.mem_reverse, List.mem_range] at hx hy
    exact hinj x hx y hy (code36_inj (hfac x hx).1 (hfac y hy).1 e)

end CFSG.KC.G22W

end
