module

public import CFSG.Certificates.Kernel.SporSch.Co1RankGrpSound
public import CFSG.Certificates.Kernel.SporSch.Co1RankCandSound

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC CFSG.KC.Loop CFSG.KC.Co1RankCoord CFSG.KC.Co1RankRec CFSG.KC.Co1RankBnd

@[expose] noncomputable def candT (T : Co1RankTab.Dat) : Co1RankCand.Dat :=
  ⟨T.d, T.Kt, T.NCt, T.PHt, T.T2A, T.nU, T.UC, []⟩

@[expose] noncomputable def repP (R : List Reps) (n i : ℕ) :
    List ℕ × ℕ × List (ℕ × ℕ × List ℕ × List ℕ) :=
  getD ([], 0, []) (getD [] R n) i

@[expose] noncomputable def repN (R : List Reps) (r : ℕ) : ℕ := lenA (getD [] R (r - 1))

@[expose] noncomputable def repGs (R : List Reps) (r a : ℕ) : List ℕ := (repP R (r - 1) a).1

@[expose] noncomputable def repSt (Dr : Co1RankRec.Dat) (r a : ℕ) : List ℕ :=
  repS (getD [] Dr.S (r - 1)) a

theorem chkR_brec {e t c : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp_all

theorem chkR_testBit_lor (a b i : ℕ) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_lor a b i

theorem chkR_testBit_land (a b i : ℕ) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_land a b i

theorem chkR_testBit_shr (a i j : ℕ) : (Nat.shiftRight a i).testBit j = a.testBit (i + j) :=
  Nat.testBit_shiftRight a

theorem chkR_bit1 (a i : ℕ) : a.testBit i = Nat.beq (Nat.land (Nat.shiftRight a i) 1) 1 := by
  have e : Nat.land (Nat.shiftRight a i) 1 = a / 2 ^ i % 2 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem chkR_uDist (T : Co1RankTab.Dat) : ∀ m acc, Nat.rec (motive := fun _ => Nat → Bool)
    (fun _ => true)
    (fun u ih acc => strictB (uC T u) fun x =>
      bIf(Nat.beq (fld(acc, x, 1)) 1, false,
        strictB (Nat.lor acc (Nat.shiftLeft 1 x)) fun a => ih a)) m acc = true →
    (∀ u < m, acc.testBit (uC T u) = false) ∧ ∀ u < m, ∀ v < m, uC T u = uC T v → u = v
  | 0, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, acc, h => by
    change strictB (uC T m) _ = true at h
    rw [strictB_ck] at h
    rcases chkR_brec h with ⟨-, h⟩ | ⟨hb, h⟩
    · exact absurd h Bool.false_ne_true
    rw [strictB_ck] at h
    have hm : acc.testBit (uC T m) = false := by rw [chkR_bit1]; exact hb
    obtain ⟨h1, h2⟩ := chkR_uDist T m _ h
    have h1' : ∀ u < m, acc.testBit (uC T u) = false ∧ uC T m ≠ uC T u := by
      intro u hu
      have := h1 u hu
      rw [chkR_testBit_lor, shl1, Nat.testBit_two_pow, Bool.or_eq_false_iff] at this
      exact ⟨this.1, of_decide_eq_false this.2⟩
    refine ⟨fun u hu => ?_, fun u hu v hv e => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact (h1' u hu).1
      · exact hm
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
      · exact h2 u hu v hv e
      · exact absurd e.symm (h1' u hu).2
      · exact absurd e (h1' v hv).2
      · rfl

theorem chkR_loop4 (f : ℕ → Bool) : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun n ih => bAnd(f n, ih)) m = true →
    ∀ n < m, f n = true
  | 0, _, n, hn => absurd hn (Nat.not_lt_zero _)
  | m + 1, h, n, hn => by
    obtain ⟨h1, h2⟩ := bAnd_ck h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · exact chkR_loop4 f m h2 n hn
    · exact h1

theorem chkR_rank {T : Co1RankTab.Dat} {r : ℕ} {S Sn : List (List (List ℕ))} {nN : ℕ} :
    ∀ (R : Reps) (i : ℕ) (X : List (List (ℕ × ℕ))),
    List.rec (motive := fun _ => Nat → List (List (Nat × Nat)) → Bool)
      (fun _ X => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) X)
      (fun p _ ih i X => List.rec (motive := fun _ => Bool) false (fun xs X' _ =>
        Prod.rec (motive := fun _ => Bool) (fun gs q => Prod.rec (motive := fun _ => Bool)
          (fun Ts _ => bAnd(Co1RankRec.repOK T r Sn nN gs Ts (repS S i) xs, ih (Nat.succ i) X')) q)
          p) X) R i X = true →
    ∀ j < lenA R, Co1RankRec.repOK T r Sn nN (getD ([], 0, []) R j).1 (getD ([], 0, []) R j).2.1
      (repS S (i + j)) (getD [] X j) = true
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, _, [], h, _, _ => absurd h Bool.false_ne_true
  | (gs, Ts, es) :: R, i, xs :: X, h, j, hj => by
    obtain ⟨h1, h2⟩ := bAnd_ck h
    cases j with
    | zero => exact h1
    | succ j =>
      have := chkR_rank R (i + 1) X h2 j (Nat.lt_of_succ_lt_succ hj)
      have e : i + (j + 1) = i + 1 + j := by omega
      rw [e]
      exact this

theorem chkR_inner (C : Co1RankCoord.Dat) (g : ℕ) : ∀ L : List ℕ,
    List.rec (motive := fun _ => Bool) true
      (fun h _ ih2 => bAnd(Nat.beq (mulC C g h) (mulC C h g), ih2)) L = true →
    ∀ h ∈ L, mulC C g h = mulC C h g
  | [], _, _, hh => by cases hh
  | x :: L, h, y, hy => by
    obtain ⟨h1, h2⟩ := bAnd_ck h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Nat.eq_of_beq_eq_true h1
    · exact chkR_inner C g L h2 y hy

theorem chkR_gens (C : Co1RankCoord.Dat) (gs : List ℕ) : ∀ L : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun g _ ih =>
      bAnd(Nat.beq (mulC C g g) 0,
      bAnd(List.rec (motive := fun _ => Bool) true
        (fun h _ ih2 => bAnd(Nat.beq (mulC C g h) (mulC C h g), ih2)) gs, ih))) L = true →
    ∀ g ∈ L, mulC C g g = 0 ∧ ∀ h ∈ gs, mulC C g h = mulC C h g
  | [], _, _, hg => by cases hg
  | x :: L, h, y, hy => by
    obtain ⟨h1, h⟩ := bAnd_ck h
    obtain ⟨h2, h3⟩ := bAnd_ck h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨Nat.eq_of_beq_eq_true h1, chkR_inner C y gs h2⟩
    · exact chkR_gens C gs L h3 y hy

theorem chkR_memL {x : ℕ} : ∀ L : List ℕ, List.rec (motive := fun _ => Bool) false
    (fun e _ ih => bIf(Nat.beq e x, true, ih)) L = true → x ∈ L
  | [], h => absurd h Bool.false_ne_true
  | e :: L, h => by
    rcases chkR_brec h with ⟨hc, -⟩ | ⟨-, h⟩
    · rw [Nat.eq_of_beq_eq_true hc]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (chkR_memL L h)

theorem chkR_set (T : Co1RankTab.Dat) (El : List ℕ) : ∀ (s : List ℕ) (lo : ℕ),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun k _ ih lo => bAnd(Nat.ble lo k, bAnd(Nat.blt k T.nU,
        bAnd(Co1RankRec.memL El (uC T k), ih (Nat.succ k))))) s lo = true →
    (∀ k ∈ s, lo ≤ k ∧ k < T.nU ∧ uC T k ∈ El) ∧ s.Pairwise (· < ·)
  | [], _, _ => ⟨fun _ hk => (by cases hk), List.Pairwise.nil⟩
  | k :: s, lo, h => by
    obtain ⟨h1, h⟩ := bAnd_ck h
    obtain ⟨h2, h⟩ := bAnd_ck h
    obtain ⟨h3, h4⟩ := bAnd_ck h
    obtain ⟨ih1, ih2⟩ := chkR_set T El s (k + 1) h4
    have hk : lo ≤ k ∧ k < T.nU ∧ uC T k ∈ El :=
      ⟨Nat.le_of_ble_eq_true h1, by simpa [Nat.blt_eq] using h2, chkR_memL El h3⟩
    refine ⟨fun k' hk' => ?_, List.Pairwise.cons (fun k' hk' => ?_) ih2⟩
    · rcases List.mem_cons.1 hk' with rfl | hk'
      · exact hk
      · obtain ⟨a, b, c⟩ := ih1 k' hk'
        exact ⟨by omega, b, c⟩
    · have := (ih1 k' hk').1
      omega

theorem chkR_repOK {T : Co1RankTab.Dat} {r : ℕ} {Sn : List (List (List ℕ))} {nN : ℕ}
    {gs : List ℕ} {Ts : ℕ} {s : List ℕ} {X : List (ℕ × ℕ)}
    (h : Co1RankRec.repOK T r Sn nN gs Ts s X = true) :
    gs.length = r ∧ (∀ g ∈ gs, mulC (Co1RankTab.toC T) g g = 0 ∧
      ∀ g' ∈ gs, mulC (Co1RankTab.toC T) g g' = mulC (Co1RankTab.toC T) g' g) ∧
      s.length = 2 ^ r - 1 ∧ getL s 0 = 0 ∧
      Co1RankRec.setOK T (spanL (Co1RankTab.toC T) gs) s = true ∧
      Co1RankRec.recsOK T Sn nN (Co1RankRec.bitsL s) Ts X = true := by
  unfold Co1RankRec.repOK at h
  obtain ⟨h1, h⟩ := bAnd_ck h
  obtain ⟨h2, h⟩ := bAnd_ck h
  obtain ⟨h3, h⟩ := bAnd_ck h
  obtain ⟨h4, h⟩ := bAnd_ck h
  obtain ⟨h5, h6⟩ := bAnd_ck h
  refine ⟨?_, chkR_gens _ gs gs h2, ?_, Nat.eq_of_beq_eq_true h4, h5, h6⟩
  · rw [← lenL_eq]
    exact Nat.eq_of_beq_eq_true h1
  · rw [← lenL_eq, ← shl1]
    exact Nat.eq_of_beq_eq_true h3

theorem chkR_recs (T : Co1RankTab.Dat) (Sn : List (List (List ℕ))) (nN sb Ts : ℕ) :
    ∀ (X : List (ℕ × ℕ)) (t : ℕ), List.rec (motive := fun _ => Nat → Bool)
      (fun t => Nat.beq (Nat.shiftRight Ts (Nat.mul T.nU t)) 0)
      (fun p _ ih t => Prod.rec (motive := fun _ => Bool) (fun a w =>
        bAnd(Nat.blt a nN, bAnd(Co1RankRec.wordOK T.nG w,
        strictB (Co1RankRec.imgB T.P w (repS Sn a)) fun M =>
        bAnd(Nat.beq (Nat.land sb M) sb,
        bAnd(Nat.beq (fld(Ts, Nat.mul T.nU t, mask T.nU)) M, ih (Nat.succ t)))))) p) X t = true →
    ∀ q, Ts.testBit q = true → T.nU * t ≤ q → ∃ a < nN, ∃ w, Co1RankRec.wordOK T.nG w = true ∧
      Nat.land sb (Co1RankRec.imgB T.P w (repS Sn a)) = sb ∧
      (Co1RankRec.imgB T.P w (repS Sn a)).testBit (q % T.nU) = true
  | [], t, h, q, hq, hle => by
    have h0 := Nat.eq_of_beq_eq_true h
    have := chkR_testBit_shr Ts (Nat.mul T.nU t) (q - T.nU * t)
    rw [h0, Nat.zero_testBit, Nat.mul_eq, Nat.add_sub_of_le hle, hq] at this
    exact absurd this Bool.false_ne_true
  | (a, w) :: X, t, h, q, hq, hle => by
    obtain ⟨h1, h⟩ := bAnd_ck h
    obtain ⟨h2, h⟩ := bAnd_ck h
    rw [strictB_ck] at h
    obtain ⟨h3, h⟩ := bAnd_ck h
    obtain ⟨h4, h5⟩ := bAnd_ck h
    by_cases hq' : T.nU * (t + 1) ≤ q
    · exact chkR_recs T Sn nN sb Ts X (t + 1) h5 q hq hq'
    · rw [Nat.mul_succ] at hq'
      refine ⟨a, by simpa [Nat.blt_eq] using h1, w, h2, Nat.eq_of_beq_eq_true h3, ?_⟩
      have hj : q - T.nU * t < T.nU := by omega
      have hmod : q % T.nU = q - T.nU * t := by
        have e : q = q - T.nU * t + T.nU * t := by omega
        rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj, Nat.add_sub_cancel]
      rw [hmod, ← Nat.eq_of_beq_eq_true h4, testBit_fld, Nat.mul_eq, Nat.add_sub_of_le hle, hq]
      simpa using hj

theorem chkR_imgB (P : List ℕ) (w : ℕ) : ∀ (L : List ℕ) (j : ℕ),
    (Co1RankRec.imgB P w L).testBit j = true → ∃ k ∈ L, walkPn P 8 w k = j
  | [], j, h => by
    change Nat.testBit 0 j = true at h
    rw [Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | k :: L, j, h => by
    change (Nat.lor (Nat.shiftLeft 1 (Co1RankRec.walkP P w k)) (Co1RankRec.imgB P w L)).testBit j
      = true at h
    rw [chkR_testBit_lor, shl1, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨k, List.mem_cons_self, by rw [← walkP_eq]; exact of_decide_eq_true h⟩
    · obtain ⟨k', hk', e⟩ := chkR_imgB P w L j h
      exact ⟨k', List.mem_cons_of_mem _ hk', e⟩

theorem chkR_bitsL : ∀ (L : List ℕ) (k : ℕ), k ∈ L → (Co1RankRec.bitsL L).testBit k = true
  | [], _, h => by cases h
  | a :: L, k, h => by
    change (Nat.lor (Nat.shiftLeft 1 a) (Co1RankRec.bitsL L)).testBit k = true
    rw [chkR_testBit_lor, shl1, Nat.testBit_two_pow, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (decide_eq_true rfl)
    · exact Or.inr (chkR_bitsL L k h)

theorem chkR_sound {T : Co1RankTab.Dat} {R : List Reps} {Dr : Co1RankRec.Dat}
    (h : chkR T R Dr = true) :
    (∀ u < T.nU, uC T u ≠ 0) ∧ (∀ u < T.nU, ∀ v < T.nU, uC T u = uC T v → u = v) ∧
    lenA R = 4 ∧ 0 < lenA (getD [] R 0) ∧
    ∀ n < 4, ∀ i < lenA (getD [] R n),
      (repP R n i).1.length = n + 1 ∧
      (∀ g ∈ (repP R n i).1, mulC (Co1RankTab.toC T) g g = 0) ∧
      (∀ g ∈ (repP R n i).1, ∀ g' ∈ (repP R n i).1,
        mulC (Co1RankTab.toC T) g g' = mulC (Co1RankTab.toC T) g' g) ∧
      (repS (getD [] Dr.S n) i).length = 2 ^ (n + 1) - 1 ∧ 0 ∈ repS (getD [] Dr.S n) i ∧
      (repS (getD [] Dr.S n) i).Nodup ∧
      (∀ k ∈ repS (getD [] Dr.S n) i,
        k < T.nU ∧ uC T k ∈ spanL (Co1RankTab.toC T) (repP R n i).1) ∧
      ∀ q, (repP R n i).2.1 / 2 ^ q % 2 = 1 →
        ∃ a' < lenA (getD [] R (n + 1)), ∃ wd, wordOKn T.nG 8 wd = true ∧
          (∀ k ∈ repS (getD [] Dr.S n) i, ∃ k' ∈ repS (getD [] Dr.S (n + 1)) a',
            walkPn T.P 8 wd k' = k) ∧
          ∃ k' ∈ repS (getD [] Dr.S (n + 1)) a', walkPn T.P 8 wd k' = q % T.nU := by
  unfold Co1RankRec.chkR at h
  obtain ⟨hu, h⟩ := bAnd_ck h
  obtain ⟨-, h⟩ := bAnd_ck h
  obtain ⟨hl4, h⟩ := bAnd_ck h
  obtain ⟨-, h⟩ := bAnd_ck h
  obtain ⟨-, h⟩ := bAnd_ck h
  obtain ⟨hpos, h⟩ := bAnd_ck h
  have hU := chkR_uDist T T.nU 1 hu
  refine ⟨fun u hu' e => ?_, hU.2, Nat.eq_of_beq_eq_true hl4, by simpa [Nat.blt_eq] using hpos, ?_⟩
  · have := hU.1 u hu'
    rw [e] at this
    exact absurd this (by decide)
  intro n hn i hi
  have hr := chkR_loop4 (fun n => Co1RankRec.rankOK T (Nat.succ n) (getD [] Dr.S n)
    (getD [] Dr.S (Nat.succ n)) (lenA (getD [] R (Nat.succ n))) (getD [] R n) (getD [] Dr.X n)) 4 h
    n hn
  have hrep := chkR_rank (getD [] R n) 0 (getD [] Dr.X n) hr i hi
  rw [Nat.zero_add] at hrep
  obtain ⟨hlen, hgs, hslen, hs0, hset, hrecs⟩ := chkR_repOK hrep
  obtain ⟨hset1, hset2⟩ := chkR_set T _ _ 0 hset
  refine ⟨hlen, fun g hg => (hgs g hg).1, fun g hg => (hgs g hg).2, hslen, ?_,
    hset2.imp Nat.ne_of_lt, fun k hk => ⟨(hset1 k hk).2.1, (hset1 k hk).2.2⟩, ?_⟩
  · have h0mem : ∀ s : List ℕ, s.length = 2 ^ (n + 1) - 1 → getL s 0 = 0 → 0 ∈ s := by
      intro s hl hg
      cases s with
      | nil =>
        have h1 : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
        have hl' : 0 = 2 ^ (n + 1) - 1 := hl
        omega
      | cons a s =>
        have ha : a = 0 := hg
        rw [ha]
        exact List.mem_cons_self
    exact h0mem _ hslen hs0
  · intro q hq
    have hb : (repP R n i).2.1.testBit q = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      exact decide_eq_true hq
    obtain ⟨a, ha, w, hw, hsub, hbit⟩ := chkR_recs T _ _ _ _ _ 0 hrecs q hb (by omega)
    refine ⟨a, ha, w, by rw [← wordOK_eq]; exact hw, fun k hk => ?_, chkR_imgB _ _ _ _ hbit⟩
    have hk' : (Nat.land (Co1RankRec.bitsL (repS (getD [] Dr.S n) i))
        (Co1RankRec.imgB T.P w (repS (getD [] Dr.S (n + 1)) a))).testBit k = true := by
      rw [hsub]
      exact chkR_bitsL _ _ hk
    rw [chkR_testBit_land, Bool.and_eq_true] at hk'
    exact chkR_imgB _ _ _ _ hk'.2

theorem sameTab_sound {C : Co1RankCand.Dat} {T : Co1RankTab.Dat} (h : sameTab C T = true) :
    C.d = T.d ∧ C.Kt = T.Kt ∧ C.NCt = T.NCt ∧ C.PHt = T.PHt ∧ C.T2A = T.T2A ∧ C.nU = T.nU ∧
      C.UC = T.UC := by
  have hb : ∀ a b : Bool, Bool.rec (motive := fun _ => Bool) false b a = true →
      a = true ∧ b = true := by decide
  have hrow : ∀ a b : List Nat, List.rec (motive := fun _ => List Nat → Bool)
      (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
      (fun x _ ih2 b => List.rec (motive := fun _ => Bool) false
        (fun y b' _ => bAnd(Nat.beq x y, ih2 b')) b) a b = true → a = b := by
    intro a
    induction a with
    | nil =>
      intro b hab
      cases b with
      | nil => rfl
      | cons y b => exact absurd hab Bool.false_ne_true
    | cons x a ih =>
      intro b hab
      cases b with
      | nil => exact absurd hab Bool.false_ne_true
      | cons y b =>
        obtain ⟨h1, h2⟩ := hb _ _ hab
        rw [Nat.eq_of_beq_eq_true h1, ih b h2]
  have hll : ∀ A B : List (List Nat), eqLL A B = true → A = B := by
    intro A
    induction A with
    | nil =>
      intro B hAB
      cases B with
      | nil => rfl
      | cons b B => exact absurd hAB Bool.false_ne_true
    | cons a A ih =>
      intro B hAB
      cases B with
      | nil => exact absurd hAB Bool.false_ne_true
      | cons b B =>
        obtain ⟨h1, h2⟩ := hb _ _ hAB
        rw [hrow a b h1, ih B h2]
  obtain ⟨h1, h⟩ := hb _ _ h
  obtain ⟨h2, h⟩ := hb _ _ h
  obtain ⟨h3, h⟩ := hb _ _ h
  obtain ⟨h4, h⟩ := hb _ _ h
  obtain ⟨h5, h⟩ := hb _ _ h
  obtain ⟨h6, h7⟩ := hb _ _ h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, hll _ _ h5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7⟩

theorem bndOK_gs {C : Co1RankCand.Dat} (h : bndOK C = true) :
    ∀ p ∈ C.reps, ∀ g ∈ p.1, g < 2 ^ (C.d + 7) := by
  have hb : ∀ a b : Bool, Bool.rec (motive := fun _ => Bool) false b a = true →
      a = true ∧ b = true := by decide
  have hlt : ∀ (m : Nat) (L : List Nat), allLt m L = true → ∀ g ∈ L, g < m := by
    intro m L
    induction L with
    | nil => intro _ g hg; cases hg
    | cons x L ih =>
      intro hL g hg
      obtain ⟨h1, h2⟩ := hb _ _ hL
      rcases List.mem_cons.1 hg with rfl | hg
      · simpa [Nat.blt_eq] using h1
      · exact ih h2 g hg
  have e : Nat.shiftLeft 1 (Nat.add C.d 7) = 2 ^ (C.d + 7) := by
    change 1 <<< (C.d + 7) = _
    rw [Nat.one_shiftLeft]
  unfold bndOK at h
  intro p hp
  generalize C.reps = L at h hp
  induction L with
  | nil => cases hp
  | cons q L ih =>
    obtain ⟨gs, Ts, es⟩ := q
    obtain ⟨h1, h2⟩ := hb _ _ h
    obtain ⟨-, h3⟩ := hb _ _ h2
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [← e]
      exact hlt _ _ h1
    · exact ih h3 hp

theorem getD_cons_zero {α : Type} (a x : α) (L : List α) : getD a (x :: L) 0 = x := rfl

theorem getD_cons_succ {α : Type} (a x : α) (L : List α) (k : ℕ) :
    getD a (x :: L) (k + 1) = getD a L k := rfl

theorem lenA_eq {α : Type} (L : List α) : lenA L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih => exact congrArg Nat.succ ih

theorem getD_mem {α : Type} (a : α) : ∀ (L : List α) (i : ℕ), i < lenA L → getD a L i ∈ L
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: L, 0, _ => by rw [getD_cons_zero]; exact List.mem_cons_self
  | x :: L, i + 1, h => by
    rw [getD_cons_succ]
    exact List.mem_cons_of_mem _ (getD_mem a L i (by rw [lenA_eq] at h ⊢; simpa using h))

theorem getD_of_le {α : Type} (a : α) : ∀ (L : List α) (i : ℕ), lenA L ≤ i → getD a L i = a
  | [], _, _ => rfl
  | x :: L, 0, h => absurd h (by rw [lenA_eq]; simp)
  | x :: L, i + 1, h => by
    rw [getD_cons_succ]
    exact getD_of_le a L i (by rw [lenA_eq] at h ⊢; simpa using h)

theorem uC_eq (T : Co1RankTab.Dat) (u : ℕ) :
    uC T u = T.UC / 2 ^ ((T.d + 7) * u) % 2 ^ (T.d + 7) := by
  rw [uC, land_mask]
  change T.UC >>> ((T.d + 7) * u) % 2 ^ (T.d + 7) = _
  rw [Nat.shiftRight_eq_div_pow]

theorem repOK_of_checks {G : Type*} [Group G] [Finite G] {T : Co1RankTab.Dat} {R : List Reps}
    {Dr : Co1RankRec.Dat} (b w : ℕ → G) (hR : chkR T R Dr = true)
    (hC : ∀ n < 4, ∀ p ∈ getD [] R n, ∃ C : Co1RankCand.Dat, Co1RankCand.chkC C = true ∧ bndOK C = true ∧
      sameTab C T = true ∧ p ∈ C.reps) :
    ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < repN R r,
      RepOK (Co1RankTab.toC T) b w (fun z => Co1RankCand.in2A (candT T) z = true) (uC T) T.nU T.nG T.P
        (repN R) (repGs R) (repSt Dr) r a := by
  obtain ⟨-, -, -, -, hrep⟩ := chkR_sound hR
  intro r hr1 hr4 a ha
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hn : n < 4 := by omega
  have e1 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
  have e2 : n + 1 + 1 - 1 = n + 1 := Nat.add_sub_cancel (n + 1) 1
  have ha' : a < lenA (getD [] R n) := by rw [repN, e1] at ha; exact ha
  obtain ⟨hlen, hsq, hcm, hslen, hs0, hnd, hsm, hrec⟩ := hrep n hn a ha'
  have hgs : repGs R (n + 1) a = (repP R n a).1 := by rw [repGs, e1]
  have hSt : ∀ a, repSt Dr (n + 1) a = repS (getD [] Dr.S n) a := fun a => by rw [repSt, e1]
  have hSt' : ∀ a, repSt Dr (n + 1 + 1) a = repS (getD [] Dr.S (n + 1)) a := fun a => by
    rw [repSt, e2]
  have hN' : repN R (n + 1 + 1) = lenA (getD [] R (n + 1)) := by rw [repN, e2]
  have hpm := getD_mem ([], 0, []) (getD [] R n) a ha'
  obtain ⟨C, hchk, hbnd, hsame, hpC⟩ := hC n hn _ hpm
  obtain ⟨hd, hKt, hNC, hPH, hT2, hnU, hUC⟩ := sameTab_sound hsame
  have hlt := bndOK_gs hbnd _ hpC
  obtain ⟨d, Kt, NCt, PHt, T2A, nU, UC, reps⟩ := C
  simp only at hd hKt hNC hPH hT2 hnU hUC hlt
  subst hd hKt hNC hPH hT2 hnU hUC
  have hcand := @chkC_cand _ hchk hbnd (repP R n a).1 (repP R n a).2.1 (repP R n a).2.2 hpC
  have hnU0 : 0 < T.nU := (hsm 0 hs0).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgs, hlen]
  · rw [hgs]; exact hlt
  · rw [hgs]; exact hcm
  · rw [hgs]; exact hsq
  · rw [hSt]; exact hslen
  · rw [hSt]; exact hs0
  · rw [hSt]; exact hnd
  · rw [hSt, hgs]; exact hsm
  · intro x hx hxx hxc
    rw [hgs] at hxc ⊢
    rcases hcand hx hxx hxc with h1 | h2 | ⟨q, hq, hqx⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · right; right
      obtain ⟨a', ha'', wd, hwd, hsub, k', hk', hku⟩ := hrec q hq
      refine ⟨q % T.nU, Nat.mod_lt _ hnU0, by rw [uC_eq]; exact hqx, a', by rw [hN']; exact ha'',
        wd, hwd, fun k hk => ?_, k', by rw [hSt']; exact hk', hku⟩
      rw [hSt] at hk
      obtain ⟨k'', hk'', e⟩ := hsub k hk
      exact ⟨k'', by rw [hSt']; exact hk'', e⟩

theorem repN_of_checks {T : Co1RankTab.Dat} {R : List Reps} {Dr : Co1RankRec.Dat}
    (hR : chkR T R Dr = true) :
    0 < repN R 1 ∧ repN R 5 = 0 ∧ (∀ u < T.nU, uC T u ≠ 0) ∧
      ∀ u < T.nU, ∀ v < T.nU, uC T u = uC T v → u = v := by
  obtain ⟨h0, hinj, hlen, hpos, -⟩ := chkR_sound hR
  refine ⟨hpos, ?_, h0, hinj⟩
  change lenA (getD [] R 4) = 0
  rw [getD_of_le [] R 4 (by rw [hlen])]
  rfl

end CFSG.KS.SporSch.Co1Rank

end
