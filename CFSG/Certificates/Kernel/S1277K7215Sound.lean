module

public import Certificates.Data.Kernel.S1277K7215
public import CFSG.Certificates.Kernel.S1277K7214Sound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.KS.C7215

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm CFSG.KC.C7214 CFSG.KC.C7215
  CFSG.KS.S1277ML CFSG.KS.S1277Gm CFSG.KS.C7214

theorem valid_ofP (p : ℕ) : (B6.ofP p).Valid :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem beqB_eq (B C : B6) : beqB B C = (B == C) := by
  rw [Bool.eq_iff_iff, beqB_iff, beq_iff_eq]

theorem pw4B_eq {B : B6} (hB : B.Valid) (k : B6 → Bool) : pw4B B k = k (B.pow 4) := by
  unfold pw4B
  simp only [forceB_eq, compK_eq]
  have h2 : B.comp (B.comp B6.id) = B.pow 2 := rfl
  rw [h2, ← pow_add hB 2 2]

theorem pw5B_eq {B : B6} (hB : B.Valid) (k : B6 → Bool) : pw5B B k = k (B.pow 5) := by
  unfold pw5B
  rw [pw4B_eq hB]
  simp only [forceB_eq, compK_eq]
  rfl

theorem invB_eq {B : B6} (hB : B.Valid) (k : B6 → Bool) : invB B k = k (inv6 B) := by
  unfold invB
  simp only [forceB_eq, compK_eq]
  have h3 : B.comp (B.comp (B.comp B6.id)) = B.pow 3 := rfl
  have h2 : B.comp (B.comp B6.id) = B.pow 2 := rfl
  rw [h3, h2, ← pow_add hB 3 3, ← pow_add hB 6 6, ← pow_add hB 12 2, ← pow_add hB 3 12,
    ← pow_add hB 15 14, ← pow_add hB 15 15, ← pow_add hB 30 29]
  rfl

theorem twoK_eq {B : B6} (hB : B.Valid) : twoK B = two6 B := by
  unfold twoK two6
  rw [pw4B_eq hB, beqB_eq]

theorem twoK_comp {B : B6} (hB : B.Valid) (C : B6) : twoK (B.comp C) = two6 (B.comp C) :=
  twoK_eq (valid_comp hB C)

theorem ord3K_eq (B : B6) : ord3K B = ord3 B := by
  unfold ord3K ord3
  rw [andB_eq, notB_eq, beqB_eq, beqB_eq, powK_eq]
  rfl

theorem conjK_eq {g : B6} (hg : g.Valid) (x : B6) (k : B6 → Bool) :
    conjK g x k = k ((g.comp x).comp (inv6 g)) := by
  unfold conjK
  rw [invB_eq hg]
  simp only [forceB_eq, compK_eq]

theorem notB_true {a : Bool} (h : notB a = true) : a = false := by
  cases a
  · rfl
  · exact absurd h (by decide)

theorem memB_false {B : B6} {L : List B6} (h : B ∉ L) : memB B L = false := by
  cases e : memB B L
  · rfl
  · exact absurd ((memB_iff _ _).1 e) h

theorem memN_eq (c : ℕ) (l : List ℕ) : memN c l = l.contains c := by
  rw [Bool.eq_iff_iff, memN_iff, List.contains_iff_mem]

theorem allL_of {f : ℕ → Bool} {l : List ℕ} (h : ∀ x ∈ l, f x = true) : allL f l = true := by
  rw [allL_eq, List.all_eq_true]
  exact h

theorem s0_valid : ∀ s ∈ s0, s.Valid := by decide

theorem l1_valid : ∀ s ∈ l1, s.Valid := by decide

theorem l2_valid : ∀ s ∈ l2, s.Valid := by decide

theorem beqMc_iff (A C : Mc) : beqMc A C = true ↔ A = C := by
  obtain ⟨a0, a1, a2⟩ := A
  obtain ⟨c0, c1, c2⟩ := C
  simp only [beqMc, andB_eq, Bool.and_eq_true, Nat.beq_eq, Mc.mk.injEq]

theorem memMc_iff (A : Mc) (L : List Mc) : memMc A L = true ↔ A ∈ L := by
  unfold memMc
  rw [anyG_eq, List.any_eq_true]
  simp only [beqMc_iff, exists_eq_right']

theorem ofIdx_of_valid {A : Mc} (h : validMc A = true) :
    Mc.ofIdx (A.c0 + 64 * A.c1 + 4096 * A.c2) = A := by
  obtain ⟨a0, a1, a2⟩ := A
  simp only [validMc, andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  simp only [Mc.ofIdx, Mc.mk.injEq]
  omega

theorem mem_of_maskMc (I : List ℕ) : ∀ (L : List Mc) (m : ℕ), maskMc I L m = true →
    ∀ n ∈ I, m.testBit n = true ∨ ∃ A ∈ L, Mc.ofIdx n = A := by
  intro L
  induction L with
  | nil =>
    intro m h n hn
    have e := allL_true h n hn
    rw [bitN_eq] at e
    exact Or.inl e
  | cons A L ih =>
    intro m h n hn
    cases hv : validMc A
    · change Bool.rec (motive := fun _ => Bool) (maskMc I L m) _ (validMc A) = true at h
      rw [hv] at h
      rcases ih m h n hn with e | ⟨B, hB, e⟩
      · exact Or.inl e
      · exact Or.inr ⟨B, List.mem_cons_of_mem _ hB, e⟩
    · change Bool.rec (motive := fun _ => Bool) _
        (strictB (m ||| (1 <<< (A.c0 + (64 * A.c1 + 4096 * A.c2)))) (maskMc I L))
        (validMc A) = true at h
      rw [hv, strictB_ml] at h
      rcases ih _ h n hn with e | ⟨B, hB, e⟩
      · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
          decide_eq_true_iff] at e
        rcases e with e | e
        · exact Or.inl e
        · refine Or.inr ⟨A, List.mem_cons_self, ?_⟩
          rw [← e, ← Nat.add_assoc]
          exact ofIdx_of_valid hv
      · exact Or.inr ⟨B, List.mem_cons_of_mem _ hB, e⟩

theorem forceMc_eq (A : Mc) (k : Mc → Bool) : forceMc A k = k A := by
  unfold forceMc
  simp only [strictB_ml]

theorem addS_eq (gens : List Mc) (x : Mc) (k : ℕ → List Mc → Bool) : ∀ s l,
    addS gens x k s l = k (bfsAddK gens (s, l) x).1 (bfsAddK gens (s, l) x).2 := by
  induction gens with
  | nil => intro s l; rfl
  | cons g gs ih =>
    intro s l
    change forceMc (mulF x g) (fun y => Bool.rec (motive := fun _ => Bool)
      (strictB (insS s (mcIdx y)) fun s' => addS gs x k s' (y :: l)) (addS gs x k s l)
        (memS s (mcIdx y))) = _
    rw [forceMc_eq]
    unfold bfsAddK
    rw [List.foldl_cons]
    cases h : memS s (mcIdx (mulF x g))
    · simp only [h, strictB_ml, cond_false]
      exact ih _ _
    · simp only [h, cond_true]
      exact ih _ _

theorem foldS_eq (gens : List Mc) : ∀ (fr : List Mc) (k : ℕ → List Mc → Bool) s l,
    foldS gens fr k s l =
      k (fr.foldl (bfsAddK gens) (s, l)).1 (fr.foldl (bfsAddK gens) (s, l)).2 := by
  intro fr
  induction fr with
  | nil => intro k s l; rfl
  | cons x fr ih =>
    intro k s l
    change addS gens x (foldS gens fr k) s l = _
    rw [addS_eq, ih, List.foldl_cons]

theorem bfsS_eq (gens : List Mc) (k : List Mc → Bool) : ∀ (n s : ℕ) (al fr : List Mc),
    bfsS gens n k s al fr = k (bfsK gens n (s, al, fr)) := by
  intro n
  induction n with
  | zero => intro s al fr; rfl
  | succ n ih =>
    intro s al fr
    cases fr with
    | nil =>
      change k al = _
      simp [bfsK]
    | cons x fr =>
      change foldS gens (x :: fr) (fun s' nw => bfsS gens n k s' (al ++ nw) nw) s [] = _
      rw [foldS_eq, ih]
      simp [bfsK, bfsStepK]

theorem genK_eq (I : List ℕ) (gens : List Mc) :
    genK I gens = maskMc I (bfsK gens 64 (insS 0 (mcIdx Mc.one), [Mc.one], [Mc.one])) 0 :=
  bfsS_eq gens _ 64 _ _ _

theorem genAll_of {I : List ℕ} (hI : gmList = I.map Mc.ofIdx) {gens : List Mc}
    (h : genK I gens = true) : genAll gens = true := by
  unfold genAll
  rw [List.all_eq_true]
  intro g hg
  rw [hI] at hg
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hg
  rw [genK_eq] at h
  rcases mem_of_maskMc I _ 0 h n hn with e | ⟨A, hA, hAe⟩
  · exact absurd e (by simp)
  · rw [List.contains_iff_mem, closureM_eq, hAe]
    exact hA

theorem snd1 (G : List B6) (h : ck1 G = true) :
    ∀ B ∈ G, (∀ D ∈ G, B.comp D = D.comp B) → B ∈ zs6 := by
  intro B hB hc
  obtain ⟨ha, h⟩ := andB_true h
  obtain ⟨hb, h⟩ := andB_true h
  rcases orB_true (allG_true h B hB) with e | e
  · exact (memB_iff _ _).1 e
  · rw [compK_eq, compK_eq, compK_eq, compK_eq, (beqB_iff _ _).2 (hc _ ((memB_iff _ _).1 ha)),
      (beqB_iff _ _).2 (hc _ ((memB_iff _ _).1 hb))] at e
    exact absurd e (by decide)

theorem sndN (G : List B6) (hv : ∀ g ∈ G, g.Valid) (l : List ℕ) (R : List B6)
    (h : ckN (G.filter (presv l)) R = true) :
    ∀ g ∈ G, presv l g = true → ∀ r ∈ R, (g.comp r).comp (inv6 g) ∈ R := by
  intro g hg hp r hr
  have e := allG_true h g (List.mem_filter.2 ⟨hg, hp⟩)
  rw [invB_eq (hv g hg)] at e
  have e := allG_true e r hr
  rw [compK_eq, compK_eq] at e
  exact (memB_iff _ _).1 e

theorem sndT (G : List B6) (hv : ∀ g ∈ G, g.Valid) (l : List ℕ) (R : List B6)
    (h : ckT (G.filter (presv l)) R = true) :
    ∀ u ∈ G, presv l u = true → two6 u = true → u ∉ R →
      ∃ g ∈ G, presv l g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false := by
  intro u hu hp h2 hn
  have e := imp_of_orB (allG_true h u (List.mem_filter.2 ⟨hu, hp⟩)) (by rw [twoK_eq (hv u hu)]; exact h2)
  have e := right_of_orB e (memB_false hn)
  obtain ⟨g, hgF, e⟩ := anyG_true e
  obtain ⟨hg, hpg⟩ := List.mem_filter.1 hgF
  rw [conjK_eq (hv g hg)] at e
  simp only [compK_eq, twoK_comp (hv u hu)] at e
  exact ⟨g, hg, hpg, notB_true e⟩

theorem snd6 (h : ck6 = true) : ∀ p ∈ l2c, ∃ r ∈ r2, ∃ c ∈ List.range 64, ∃ r' ∈ r2,
    ∃ c' ∈ List.range 64, p = (c ^^^ r.app c) ^^^ (c' ^^^ r'.app c') := by
  intro p hp
  unfold ck6 at h
  rw [strictB_ml] at h
  obtain ⟨r, hr, e⟩ := anyG_true (allL_true h p hp)
  obtain ⟨c, hc, e⟩ := anyL_true e
  rw [bitN_eq] at e
  unfold commM at e
  rw [testBit_maskBelow, Bool.and_eq_true] at e
  obtain ⟨r', hr', e⟩ := anyG_true e.2
  obtain ⟨c', hc', e⟩ := anyL_true e
  have e := Nat.eq_of_beq_eq_true e
  rw [appK_eq, appK_eq] at e
  refine ⟨r, hr, c, hc, r', hr', c', hc', ?_⟩
  change Nat.xor p (Nat.xor c (r.app c)) = Nat.xor c' (r'.app c') at e
  change p = Nat.xor (Nat.xor c (r.app c)) (Nat.xor c' (r'.app c'))
  rw [← e]
  change p = (c ^^^ r.app c) ^^^ (p ^^^ (c ^^^ r.app c))
  rw [Nat.xor_comm p, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem snd7 (h : ck7 = true) : ∀ p ∈ l2c, ∃ s ∈ s0, ∃ c ∈ List.range 64, c ^^^ s.app c = p := by
  intro p hp
  obtain ⟨s, hs, e⟩ := anyG_true (allL_true h p hp)
  obtain ⟨c, hc, e⟩ := anyL_true e
  refine ⟨s, hs, c, hc, ?_⟩
  rw [← appK_eq]
  exact Nat.eq_of_beq_eq_true e

theorem snd8 (F : List B6) (h : ck8 F = true) : ∀ c ∈ List.range 64, c ∉ p1c →
    spanHas (p1c ++ F.map (·.app c)) (List.range 64) = true := by
  intro c hc hp
  have h1 := right_of_orB (allL_true h c hc) (by
    cases e : memN c p1c
    · rfl
    · exact absurd ((memN_iff _ _).1 e) hp)
  exact spanHas_of _ (by simpa only [appK_eq] using h1)

theorem snd9 (F : List B6) (h : ck9 F = true) : ∀ c ∈ p1c, c ≠ 0 →
    spanHas (F.map (·.app c)) p1c = true := by
  intro c hc h0
  exact right_of_orB (allL_true h c hc) (CFSG.KS.C7214.beq_false_of_ne h0)

theorem samePL_eq {A C : Mc} (h : samePL A C = true) :
    presv p1c A.toB6 = presv p1c C.toB6 ∧ presv l2c A.toB6 = presv l2c C.toB6 := by
  obtain ⟨h1, h2⟩ := andB_true h
  rw [eqB_eq, beq_iff_eq, presvK_eq, presvK_eq] at h1 h2
  exact ⟨h1, h2⟩

theorem snd10_aux : ∀ (I W : List ℕ), ck10 I W = true → ∀ n ∈ I, ∃ s ∈ s0m, ∃ s' ∈ s0m,
    ((s.mul (Mc.ofIdx n)).mul s') ∈ dreps ∧
      presv p1c ((s.mul (Mc.ofIdx n)).mul s').toB6 = presv p1c (Mc.ofIdx n).toB6 ∧
      presv l2c ((s.mul (Mc.ofIdx n)).mul s').toB6 = presv l2c (Mc.ofIdx n).toB6 := by
  intro I
  induction I with
  | nil =>
    intro W _ n hn
    exact absurd hn List.not_mem_nil
  | cons n I ih =>
    intro W h m hm
    cases W with
    | nil =>
      change false = true at h
      exact absurd h Bool.false_ne_true
    | cons w W =>
      change andB _ (andB _ (andB _ (andB _ (andB _ (ck10 I W))))) = true at h
      obtain ⟨-, h⟩ := andB_true h
      obtain ⟨h1, h⟩ := andB_true h
      obtain ⟨h2, h⟩ := andB_true h
      obtain ⟨h3, h⟩ := andB_true h
      obtain ⟨h4, h⟩ := andB_true h
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [mulF_eq, mulF_eq] at h3 h4
        exact ⟨_, (memMc_iff _ _).1 h1, _, (memMc_iff _ _).1 h2, (memMc_iff _ _).1 h3,
          samePL_eq h4⟩
      · exact ih W h m hm

theorem snd10 {I W : List ℕ} (hI : gmList = I.map Mc.ofIdx) (h : ck10 I W = true) :
    ∀ g ∈ gmList, ∃ s ∈ s0m, ∃ s' ∈ s0m, (s.mul g).mul s' ∈ dreps ∧
      presv p1c ((s.mul g).mul s').toB6 = presv p1c g.toB6 ∧
      presv l2c ((s.mul g).mul s').toB6 = presv l2c g.toB6 := by
  intro g hg
  rw [hI] at hg
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hg
  exact snd10_aux I W h n hn

theorem presvK_false {l : List ℕ} {B : B6} (h : presv l B = false) : presvK l B = false := by
  rw [presvK_eq]
  exact h

theorem snd11 {I : List ℕ} (hI : gmList = I.map Mc.ofIdx) {D : List Mc} (h : ck11 I D = true) :
    ∀ r ∈ D, presv p1c r.toB6 = false → presv l2c r.toB6 = false →
      genAll (s0m ++ [r]) = true := by
  intro r hr h1 h2
  have e := right_of_orB (allG_true h r hr) (presvK_false h1)
  exact genAll_of hI (right_of_orB e (presvK_false h2))

theorem snd12 {I : List ℕ} (hI : gmList = I.map Mc.ofIdx) {D : List Mc} (h : ck12 I D = true) :
    ∀ r ∈ D, presv p1c r.toB6 = false → presv l2c r.toB6 = true →
      ∀ r' ∈ dreps, presv p1c r'.toB6 = true → presv l2c r'.toB6 = false →
        genAll (s0m ++ [r, r']) = true := by
  intro r hr h1 h2 r' hr' h3 h4
  have e := right_of_orB (allG_true h r hr) (presvK_false h1)
  have e := imp_of_orB e (by rw [presvK_eq]; exact h2)
  have e := imp_of_orB (allG_true e r' hr') (by rw [presvK_eq]; exact h3)
  exact genAll_of hI (right_of_orB e (presvK_false h4))

theorem sndY (G : List B6) (hv : ∀ g ∈ G, g.Valid) (l : List ℕ) (L : List B6)
    (h : ckY (G.filter (presv l)) L = true) :
    ∀ y ∈ G, presv l y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ L ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false := by
  intro y hy hp h3
  have e := imp_of_orB (allG_true h y (List.mem_filter.2 ⟨hy, hp⟩)) (by rw [ord3K_eq]; exact h3)
  rcases orB_true e with e | e
  · exact Or.inl ((memB_iff _ _).1 e)
  rcases orB_true e with e | e
  · exact Or.inr (Or.inl ((memB_iff _ _).1 e))
  obtain ⟨s, hs, e⟩ := anyG_true e
  rw [conjK_eq (s0_valid s hs)] at e
  obtain ⟨e1, e2⟩ := andB_true e
  rw [invB_eq (valid_comp (valid_comp (s0_valid s hs) _) _)] at e1
  simp only [compK_eq, twoK_comp (hv y hy)] at e1 e2
  exact Or.inr (Or.inr ⟨s, hs, notB_true e1, notB_true e2⟩)

theorem sndU (G : List B6) (hv : ∀ g ∈ G, g.Valid) (l : List ℕ) (L : List B6)
    (hL : ∀ y ∈ L, y.Valid) (h : ckU (G.filter (presv l)) L = true) :
    ∀ u ∈ G, presv l u = true → two6 u = true → u ∉ L → ∀ y ∈ L, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false := by
  intro u hu hp h2 hn y hy h3
  have e := imp_of_orB (allG_true h u (List.mem_filter.2 ⟨hu, hp⟩)) (by rw [twoK_eq (hv u hu)]; exact h2)
  have e := right_of_orB e (memB_false hn)
  have e := imp_of_orB (allG_true e y hy) (by rw [ord3K_eq]; exact h3)
  rw [invB_eq (hL y hy)] at e
  simp only [compK_eq, twoK_comp (hv u hu)] at e
  rcases orB_true e with e | e
  · exact Or.inl (notB_true e)
  · exact Or.inr (notB_true e)

theorem sndO (f p : B6 → Bool) (hf : ∀ B, f B = p B) (G : List B6) (hv : ∀ g ∈ G, g.Valid)
    (L : List B6) (h : ckO f G L = true) : ∀ g ∈ G, p g = true → g.pow 15 = B6.id → g ∈ L := by
  intro g hg h1 h2
  have e := imp_of_orB (allG_true h g hg) (by rw [hf]; exact h1)
  have e := imp_of_orB e ((eq15B_iff (hv g hg)).2 h2)
  exact (memB_iff _ _).1 e

theorem fixP1K_eq (B : B6) : fixP1K B = fixP1 B := by
  unfold fixP1K fixP1
  rw [allL_eq]
  congr 1
  funext c
  rw [nbeq, appK_eq]

theorem onQuotK_eq (B : B6) : onQuotK B = onQuot B := by
  unfold onQuotK onQuot
  rw [andB_eq, presvK_eq, allL_eq]
  congr 2
  funext c
  rw [memN_eq, appK_eq]
  rfl

theorem inLZ_true {L : List B6} {B : B6} (h : inLZ L B = true) : ∃ a ∈ L, ∃ z ∈ zs6, B = a.comp z := by
  obtain ⟨a, ha, e⟩ := anyG_true h
  obtain ⟨z, hz, e⟩ := anyG_true e
  rw [compK_eq] at e
  exact ⟨a, ha, z, hz, beqB_true e⟩

theorem sndZo (G : List B6) (hv : ∀ g ∈ G, g.Valid) (l : List ℕ) (L : List B6)
    (h : ckZo (G.filter (presv l)) L = true) :
    ∀ g ∈ G, presv l g = true → g.pow 15 = B6.id → ∃ a ∈ L, ∃ z ∈ zs6, g = a.comp z := by
  intro g hg hp h1
  exact inLZ_true (imp_of_orB (allG_true h g (List.mem_filter.2 ⟨hg, hp⟩))
    ((eq15B_iff (hv g hg)).2 h1))

theorem sndZs (G : List B6) (l : List ℕ) (L : List B6)
    (h : ckZs (G.filter (presv l)) L = true) :
    ∀ g ∈ G, presv l g = true → ∃ a ∈ L, ∃ z ∈ zs6, g.comp g = a.comp z := by
  intro g hg hp
  have e := allG_true h g (List.mem_filter.2 ⟨hg, hp⟩)
  rw [compK_eq] at e
  exact inLZ_true e

theorem snd23 (G : List B6) (hv : ∀ g ∈ G, g.Valid) (h : ck23 G = true) :
    ∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL →
      ∀ g ∈ G, g.pow 5 = B6.id → g ≠ B6.id → g.app c ≠ c := by
  intro c hc h0 ho g hg h5 h1 e
  have e1 := imp_of_orB (allG_true h g hg) (by rw [pw5B_eq (hv g hg), beqB_eq, h5]; exact beq_self_eq_true _)
  have e1 := right_of_orB e1 (beqB_false h1)
  have e1 := right_of_orB (allL_true e1 c hc) (CFSG.KS.C7214.beq_false_of_ne h0)
  have e1 := right_of_orB e1 (by
    cases e : memN c oVecL
    · rfl
    · exact absurd ((memN_iff _ _).1 e) ho)
  rw [appK_eq, e] at e1
  exact absurd e1 (by simp [notB_eq])

theorem snd24 (G : List B6) (hv : ∀ g ∈ G, g.Valid) (h : ck24 G = true) :
    ∀ c ∈ oVecL, ∃ g ∈ G, g.pow 5 = B6.id ∧ g ≠ B6.id ∧ g.app c = c := by
  intro c hc
  obtain ⟨g, hg, e⟩ := anyG_true (allL_true h c hc)
  obtain ⟨e1, e⟩ := andB_true e
  obtain ⟨e2, e3⟩ := andB_true e
  rw [pw5B_eq (hv g hg)] at e1
  refine ⟨g, hg, beqB_true e1, fun h1 => ?_, ?_⟩
  · rw [h1] at e2
    exact absurd e2 (by decide)
  · rw [← appK_eq]
    exact Nat.eq_of_beq_eq_true e3

theorem snd25 (N : List B6) (h : ck25 N = true) :
    ∀ B ∈ N, (∀ p ∈ oPts, pn (B.app p) = p) → B ∈ zs6 := by
  intro B hB h1
  refine (memB_iff _ _).1 (imp_of_orB (allG_true h B hB) (allL_of fun p hp => ?_))
  rw [appK_eq, h1 p hp]
  exact Nat.beq_refl _

end CFSG.KS.C7215

end
