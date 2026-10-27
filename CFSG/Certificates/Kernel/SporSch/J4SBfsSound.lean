
module

public import Certificates.Data.Kernel.SporSch.J4SBfs
public import CFSG.Certificates.Kernel.SporSch.J4SColsSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.C11

open CFSG.Sporadic.J4Schreier

@[expose] def tabA (n : Nat) (T : Nat → Nat) : Array Nat := Array.ofFn (n := n) fun i => T i.val

theorem tabA_get {n : Nat} {T : Nat → Nat} {i : Nat} (hi : i < n) : (tabA n T)[i]! = T i := by
  rw [tabA, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

section Proofs

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw

theorem forIn_yield_foldl' {σ : Type} (g : σ → Nat → σ) (f : Nat → σ → Id (ForInStep σ))
    (hf : ∀ h s, f h s = pure (.yield (g s h))) :
    ∀ (l : List Nat) (init : σ), (forIn l init f : Id σ) = pure (l.foldl g init) := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons a l ih =>
    intro init
    rw [List.forIn_cons, hf, List.foldl_cons]
    exact ih _

def iStep (gens : Array (Array Nat)) (p i : Nat) (st : Array Bool × Array Nat × Array Nat × Array Nat)
    (g : Nat) : Array Bool × Array Nat × Array Nat × Array Nat :=
  if (!st.1[app11 gens[g]! p]!) = true then
    (st.1.set! (app11 gens[g]! p) true, st.2.1.push (app11 gens[g]! p), st.2.2.1.push i,
      st.2.2.2.push g)
  else st

def oStep (gens : Array (Array Nat))
    (st : Array Bool × Array Nat × Array Nat × Array Nat × Nat) (_ : Nat) :
    Array Bool × Array Nat × Array Nat × Array Nat × Nat :=
  if st.2.2.2.2 < st.2.1.size then
    (((List.range gens.size).foldl (iStep gens st.2.1[st.2.2.2.2]! st.2.2.2.2)
        (st.1, st.2.1, st.2.2.1, st.2.2.2.1)).1,
      ((List.range gens.size).foldl (iStep gens st.2.1[st.2.2.2.2]! st.2.2.2.2)
        (st.1, st.2.1, st.2.2.1, st.2.2.2.1)).2.1,
      ((List.range gens.size).foldl (iStep gens st.2.1[st.2.2.2.2]! st.2.2.2.2)
        (st.1, st.2.1, st.2.2.1, st.2.2.2.1)).2.2.1,
      ((List.range gens.size).foldl (iStep gens st.2.1[st.2.2.2.2]! st.2.2.2.2)
        (st.1, st.2.1, st.2.2.1, st.2.2.2.1)).2.2.2, st.2.2.2.2 + 1)
  else st

theorem bfs11_eq (gens : Array (Array Nat)) (s : Nat) :
    bfs11 gens s =
      (((List.range 2048).foldl (oStep gens)
          ((Array.replicate 2048 false).set! s true, #[s], #[0], #[0], 0)).2.1,
        ((List.range 2048).foldl (oStep gens)
          ((Array.replicate 2048 false).set! s true, #[s], #[0], #[0], 0)).2.2.1,
        ((List.range 2048).foldl (oStep gens)
          ((Array.replicate 2048 false).set! s true, #[s], #[0], #[0], 0)).2.2.2.1) := by
  unfold bfs11
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [forIn_yield_foldl' (oStep gens)]
  · generalize (List.range 2048).foldl (oStep gens) _ = R
    rfl
  · intro x st
    obtain ⟨seen, pts, par, lab, i⟩ := st
    by_cases hi : i < pts.size
    · simp only [hi, ↓reduceIte, oStep]
      rw [forIn_yield_foldl' (iStep gens pts[i]! i)]
      · rfl
      · intro g st'
        obtain ⟨seen', pts', par', lab'⟩ := st'
        unfold iStep
        by_cases hs : (!seen'[app11 gens[g]! pts[i]!]!) = true
        · simp only [hs, ↓reduceIte]
        · simp only [hs, ↓reduceIte, Bool.false_eq_true]
    · simp only [hi, ↓reduceIte, oStep]

def lexP (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b < d)

theorem lexLt_iff (a b c d : Nat) : lexLt a b c d = true ↔ lexP a b c d := by
  unfold lexLt lexP
  rw [Orb.bIf_eq, Orb.bAnd_eq]
  by_cases h1 : a < c
  · have hb : Nat.blt a c = true := by simpa using h1
    simp [hb, h1]
  · have hb : Nat.blt a c = false := by
      cases h' : Nat.blt a c
      · rfl
      · exact absurd (by simpa using h') h1
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, h1,
      false_or]

structure BF (G : Nat → Nat) (k s n : Nat) (PT PAR LAB POS : Nat → Nat) : Prop where
  n0 : 0 < n
  n2 : n ≤ 2048
  pt0 : PT 0 = s
  par0 : PAR 0 = 0
  lab0 : LAB 0 = 0
  ptlt : ∀ i < n, PT i < 2048
  pos : ∀ i < n, POS (PT i) = i
  edge : ∀ i < n, 0 < i → PAR i < i ∧ LAB i < k ∧ PT i = appK (G (LAB i)) (PT (PAR i))
  mono : ∀ i < n, 0 < i → i + 1 < n → lexP (PAR i) (LAB i) (PAR (i + 1)) (LAB (i + 1))
  first : ∀ i < n, ∀ g < k, appK (G g) (PT i) < 2048 ∧ POS (appK (G g) (PT i)) < n ∧
    PT (POS (appK (G g) (PT i))) = appK (G g) (PT i) ∧
    (POS (appK (G g) (PT i)) = 0 ∨
      ¬ lexP i g (PAR (POS (appK (G g) (PT i)))) (LAB (POS (appK (G g) (PT i)))))

theorem listed_of {n : Nat} {PT POS : Nat → Nat} {q : Nat} (h : listedK n PT POS q = true) :
    q < 2048 ∧ POS q < n ∧ PT (POS q) = q := by
  unfold listedK at h
  simp only [Orb.bAnd_eq, Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem bf_of {G : Nat → Nat} {k s n : Nat} {PT PAR LAB POS : Nat → Nat}
    (h : bfsK G k s n PT PAR LAB POS = true) : BF G k s n PT PAR LAB POS := by
  unfold bfsK at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨n0, n2, -, pt0, par0, lab0, hpt, -, hedge, hmono, hfirst⟩ := h
  refine ⟨n0, n2, pt0, par0, lab0, fun i hi => ?_, fun i hi => ?_, fun i hi h0 => ?_, fun i hi h0 h1 => ?_,
    fun i hi g hg => ?_⟩
  · have := Orb.allN_iff.1 hpt i hi
    simp only [Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this.1
  · have := Orb.allN_iff.1 hpt i hi
    simp only [Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this.2
  · have := Orb.allN_iff.1 hedge i hi
    unfold edgeK at this
    have hb : Nat.beq i 0 = false := by
      cases h' : Nat.beq i 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') (by omega)
    rw [hb] at this
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  · have := Orb.allN_iff.1 hmono i hi
    have hb : Nat.beq i 0 = false := by
      cases h' : Nat.beq i 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') (by omega)
    have hb1 : Nat.blt (Nat.succ i) n = true := by simpa using h1
    rw [hb, hb1] at this
    exact (lexLt_iff _ _ _ _).1 this
  · have h2 := Orb.allN_iff.1 (by
      have := Orb.allN_iff.1 hfirst i hi
      rw [Orb.strictB_eq] at this
      exact this) g hg
    rw [Orb.strictB_eq] at h2
    unfold firstK at h2
    simp only [Orb.bAnd_eq, Bool.and_eq_true, Orb.strictB_eq] at h2
    obtain ⟨hl, hj⟩ := h2
    obtain ⟨l1, l2, l3⟩ := listed_of hl
    refine ⟨l1, l2, l3, ?_⟩
    rw [Orb.bIf_eq, Orb.bIf_eq] at hj
    by_cases hz : POS (appK (G g) (PT i)) = 0
    · exact Or.inl hz
    · right
      have hb : Nat.beq (POS (appK (G g) (PT i))) 0 = false := by
        cases h' : Nat.beq (POS (appK (G g) (PT i))) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') hz
      rw [hb] at hj
      simp only [Bool.false_eq_true, ↓reduceIte] at hj
      intro hl'
      rw [ite_eq_left ((lexLt_iff _ _ _ _).2 hl')] at hj
      exact Bool.noConfusion hj

theorem lex_trans {a b c d e f : Nat} (h1 : lexP a b c d) (h2 : lexP c d e f) : lexP a b e f := by
  unfold lexP at *
  omega

theorem mono_all {G : Nat → Nat} {k s n : Nat} {PT PAR LAB POS : Nat → Nat}
    (B : BF G k s n PT PAR LAB POS) :
    ∀ x y, 0 < x → x < y → y < n → lexP (PAR x) (LAB x) (PAR y) (LAB y) := by
  intro x y hx hxy hy
  induction y with
  | zero => omega
  | succ y ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hxy with h1 | h1
    · exact lex_trans (ih h1 (by omega)) (B.mono y (by omega) (by omega) hy)
    · subst h1
      exact B.mono x (by omega) hx hy

theorem pt_inj {G : Nat → Nat} {k s n : Nat} {PT PAR LAB POS : Nat → Nat}
    (B : BF G k s n PT PAR LAB POS) : ∀ i < n, ∀ j < n, PT i = PT j → i = j := by
  intro i hi j hj e
  rw [← B.pos i hi, ← B.pos j hj, e]

structure BInv (n : Nat) (PT PAR LAB : Nat → Nat) (h g c : Nat)
    (st : Array Bool × Array Nat × Array Nat × Array Nat) : Prop where
  c1 : 1 ≤ c
  cn : c ≤ n
  disc : ∀ j < n, (j < c ↔ (j = 0 ∨ lexP (PAR j) (LAB j) h g))
  pts : st.2.1 = ((List.range c).map PT).toArray
  par : st.2.2.1 = ((List.range c).map PAR).toArray
  lab : st.2.2.2 = ((List.range c).map LAB).toArray
  ssz : st.1.size = 2048
  seen : ∀ a < 2048, (st.1[a]! = true ↔ ∃ j < c, PT j = a)

theorem arr_get' (p : Nat → Nat) {m y : Nat} (hy : y < m) :
    ((List.range m).map p).toArray[y]! = p y := by
  rw [getElem!_pos _ y (by simpa using hy)]
  simp

theorem push_range' (p : Nat → Nat) (m : Nat) :
    (((List.range m).map p).toArray).push (p m) = ((List.range (m + 1)).map p).toArray := by
  rw [List.range_succ, List.map_append]
  simp

theorem iStep_inv {gens : Array (Array Nat)} {G : Nat → Nat} {k s n : Nat}
    {PT PAR LAB POS : Nat → Nat} (hg : gens.size = k ∧ ∀ g < k, gens[g]! = unpack11 (G g))
    (B : BF G k s n PT PAR LAB POS) {h g c : Nat} (hh : h < n) (hgk : g < k)
    {st : Array Bool × Array Nat × Array Nat × Array Nat} (I : BInv n PT PAR LAB h g c st) :
    ∃ c', BInv n PT PAR LAB h (g + 1) c' (iStep gens (PT h) h st g) := by
  have hq : app11 gens[g]! (PT h) = appK (G g) (PT h) := by rw [hg.2 g hgk, app_eq]
  obtain ⟨q1, q2, q3, q4⟩ := B.first h hh g hgk
  have hmono := mono_all B
  unfold iStep
  rw [hq]
  generalize hqv : appK (G g) (PT h) = q at q1 q2 q3 q4
  generalize hj : POS q = j at q2 q3 q4
  have hlex : ∀ j' < n, 0 < j' → (lexP (PAR j') (LAB j') h (g + 1) ↔
      lexP (PAR j') (LAB j') h g ∨ (PAR j' = h ∧ LAB j' = g)) := by
    intro j' _ _
    unfold lexP
    omega
  have hpair : ∀ j' < n, 0 < j' → PAR j' = h → LAB j' = g → j' = j := by
    intro j' hj' h0 e1 e2
    obtain ⟨-, -, e3⟩ := B.edge j' hj' h0
    rw [e1, e2, hqv] at e3
    rw [← hj, ← e3, B.pos j' hj']
  by_cases hjc : j < c
  · have hseen : st.1[q]! = true := (I.seen q q1).2 ⟨j, hjc, q3⟩
    have hb : ((!st.1[q]!) = true) = False := by rw [hseen]; simp
    simp only [hb, ↓reduceIte]
    refine ⟨c, I.c1, I.cn, fun j' hj' => ?_, I.pts, I.par, I.lab, I.ssz, I.seen⟩
    rw [I.disc j' hj']
    rcases Nat.eq_zero_or_pos j' with h0 | h0
    · simp [h0]
    · rw [hlex j' hj' h0]
      constructor
      · rintro (h1 | h1)
        · exact absurd h1 (by omega)
        · exact Or.inr (Or.inl h1)
      · rintro (h1 | h1 | ⟨e1, e2⟩)
        · exact Or.inl h1
        · exact Or.inr h1
        · have := hpair j' hj' h0 e1 e2
          subst this
          exact (I.disc j' hj').1 hjc
  · have hj0 : j ≠ 0 := fun e => hjc (by rw [e]; exact I.c1)
    have hnl : ¬ lexP (PAR j) (LAB j) h g := fun hl => hjc ((I.disc j q2).2 (Or.inr hl))
    have hle := q4.resolve_left hj0
    have hpj : PAR j = h ∧ LAB j = g := by
      unfold lexP at hnl hle
      omega
    have hcj : c = j := by
      by_contra hne
      have hlt : c < j := by omega
      have hcn : c < n := by omega
      have hc0 : 0 < c := I.c1
      have := hmono c j hc0 hlt q2
      rw [hpj.1, hpj.2] at this
      exact absurd ((I.disc c hcn).2 (Or.inr this)) (Nat.lt_irrefl c)
    subst hcj
    have hnot : st.1[q]! = false := by
      cases e : st.1[q]!
      · rfl
      · obtain ⟨j', hj', e'⟩ := (I.seen q q1).1 e
        have := pt_inj B j' (by omega) c q2 (by rw [e', q3])
        omega
    have hb : ((!st.1[q]!) = true) = True := by rw [hnot]; simp
    simp only [hb, ↓reduceIte]
    refine ⟨c + 1, by omega, by omega, fun j' hj' => ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · rcases Nat.eq_zero_or_pos j' with h0 | h0
      · simp [h0]
      · rw [hlex j' hj' h0]
        constructor
        · intro h1
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h2 | h2
          · rcases (I.disc j' hj').1 h2 with h3 | h3
            · omega
            · exact Or.inr (Or.inl h3)
          · subst h2
            exact Or.inr (Or.inr hpj)
        · rintro (h1 | h1 | ⟨e1, e2⟩)
          · omega
          · exact Nat.lt_succ_of_lt ((I.disc j' hj').2 (Or.inr h1))
          · have := hpair j' hj' h0 e1 e2
            omega
    · dsimp only
      rw [I.pts, ← q3, push_range']
    · dsimp only
      rw [I.par, ← hpj.1, push_range']
    · dsimp only
      rw [I.lab, ← hpj.2, push_range']
    · dsimp only
      rw [Array.size_set!, I.ssz]
    · dsimp only
      by_cases haq : a = q
      · subst haq
        rw [Array.getElem!_set!_self _ _ _ (by rw [I.ssz]; exact q1)]
        exact ⟨fun _ => ⟨c, Nat.lt_succ_self c, q3⟩, fun _ => rfl⟩
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm haq), I.seen a ha]
        constructor
        · rintro ⟨j', hj', e⟩
          exact ⟨j', by omega, e⟩
        · rintro ⟨j', hj', e⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h1 | h1
          · exact ⟨j', h1, e⟩
          · subst h1
            exact absurd (e.symm.trans q3) haq

theorem inner_inv {gens : Array (Array Nat)} {G : Nat → Nat} {k s n : Nat}
    {PT PAR LAB POS : Nat → Nat} (hg : gens.size = k ∧ ∀ g < k, gens[g]! = unpack11 (G g))
    (B : BF G k s n PT PAR LAB POS) {h : Nat} (hh : h < n) :
    ∀ g ≤ k, ∀ {c : Nat} {st : Array Bool × Array Nat × Array Nat × Array Nat},
      BInv n PT PAR LAB h 0 c st →
      ∃ c', BInv n PT PAR LAB h g c' ((List.range g).foldl (iStep gens (PT h) h) st) := by
  intro g
  induction g with
  | zero => intro _ c st I; exact ⟨c, I⟩
  | succ g ih =>
    intro hg' c st I
    obtain ⟨c', I'⟩ := ih (by omega) I
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact iStep_inv hg B hh (by omega) I'

def OInv (n : Nat) (PT PAR LAB : Nat → Nat) (m : Nat)
    (st : Array Bool × Array Nat × Array Nat × Array Nat × Nat) : Prop :=
  st.2.2.2.2 = min m n ∧ ∃ c, BInv n PT PAR LAB (min m n) 0 c (st.1, st.2.1, st.2.2.1, st.2.2.2.1)

theorem outer_inv {gens : Array (Array Nat)} {G : Nat → Nat} {k s n : Nat}
    {PT PAR LAB POS : Nat → Nat} (hg : gens.size = k ∧ ∀ g < k, gens[g]! = unpack11 (G g))
    (B : BF G k s n PT PAR LAB POS) :
    ∀ m : Nat, OInv n PT PAR LAB m ((List.range m).foldl (oStep gens)
      ((Array.replicate 2048 false).set! s true, #[s], #[0], #[0], 0)) := by
  have hs : s < 2048 := by rw [← B.pt0]; exact B.ptlt 0 B.n0
  intro m
  induction m with
  | zero =>
    rw [List.range_zero, List.foldl_nil]
    refine ⟨by simp, 1, le_refl 1, B.n0, fun j hj => ?_, ?_, ?_, ?_, by simp, fun a ha => ?_⟩
    · simp only [Nat.zero_min]
      constructor
      · intro h
        exact Or.inl (by omega)
      · rintro (h | h)
        · omega
        · unfold lexP at h
          omega
    · simp [B.pt0]
    · simp [B.par0]
    · simp [B.lab0]
    · dsimp only
      by_cases has : a = s
      · subst has
        rw [Array.getElem!_set!_self _ _ _ (by simpa using hs)]
        exact ⟨fun _ => ⟨0, Nat.zero_lt_one, B.pt0⟩, fun _ => rfl⟩
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm has), getElem!_pos _ a (by simpa using ha)]
        simp only [Array.getElem_replicate, Bool.false_eq_true, false_iff]
        rintro ⟨j, hj, e⟩
        have : j = 0 := by omega
        subst this
        exact has (e.symm.trans B.pt0)
  | succ m ih =>
    obtain ⟨hi, c, I⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl (oStep gens) _ = st at hi I ⊢
    obtain ⟨seen, pts, par, lab, i⟩ := st
    dsimp only at hi I
    by_cases hm : m < n
    · have e1 : min m n = m := by omega
      have e2 : min (m + 1) n = m + 1 := by omega
      rw [e1] at hi I
      subst i
      have hmc : m < c := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · have := I.c1
          omega
        · refine (I.disc m hm).2 (Or.inr ?_)
          unfold lexP
          have := (B.edge m hm h0).1
          omega
      have hsz : pts.size = c := by
        have := I.pts
        dsimp only at this
        rw [this]
        simp
      have hp : pts[m]! = PT m := by
        have := I.pts
        dsimp only at this
        rw [this, arr_get' PT hmc]
      have ho : oStep gens (seen, pts, par, lab, m) m =
          (((List.range gens.size).foldl (iStep gens (PT m) m) (seen, pts, par, lab)).1,
          ((List.range gens.size).foldl (iStep gens (PT m) m) (seen, pts, par, lab)).2.1,
          ((List.range gens.size).foldl (iStep gens (PT m) m) (seen, pts, par, lab)).2.2.1,
          ((List.range gens.size).foldl (iStep gens (PT m) m) (seen, pts, par, lab)).2.2.2,
          m + 1) := by
        unfold oStep
        dsimp only
        rw [ite_eq_left (by omega), hp]
      rw [ho, hg.1]
      obtain ⟨c', I'⟩ := inner_inv hg B hm k (le_refl k) I
      refine ⟨by rw [e2], c', ?_⟩
      rw [e2]
      refine ⟨I'.c1, I'.cn, fun j hj => ?_, I'.pts, I'.par, I'.lab, I'.ssz, I'.seen⟩
      rw [I'.disc j hj]
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · simp [h0]
      · have := (B.edge j hj h0).2.1
        unfold lexP
        constructor
        · rintro (h1 | h1)
          · exact Or.inl h1
          · right
            omega
        · rintro (h1 | h1)
          · exact Or.inl h1
          · right
            omega
    · have e1 : min m n = n := by omega
      have e2 : min (m + 1) n = n := by omega
      rw [e1] at hi I
      subst i
      have hcn : c = n := by
        refine le_antisymm I.cn ?_
        by_contra hlt
        have hc : c < n := by omega
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · have := I.c1
          omega
        · have h1 := (I.disc c hc).2 (Or.inr (by
            unfold lexP
            have := (B.edge c hc h0).1
            omega))
          omega
      have hsz : pts.size = c := by
        have := I.pts
        dsimp only at this
        rw [this]
        simp
      have ho : oStep gens (seen, pts, par, lab, n) m = (seen, pts, par, lab, n) := by
        unfold oStep
        dsimp only
        rw [ite_eq_right (by omega)]
      rw [ho]
      unfold OInv
      rw [e2]
      exact ⟨rfl, c, I⟩

theorem tabA_eq {n : Nat} (T : Nat → Nat) : ((List.range n).map T).toArray = tabA n T := by
  apply Array.ext
  · simp [tabA]
  · intro i h1 _
    simp [tabA]

theorem bfsK_sound_proved {gens : Array (Array Nat)} {G : Nat → Nat} {k s n : Nat}
    {PT PAR LAB POS : Nat → Nat}
    (hg : gens.size = k ∧ ∀ g < k, gens[g]! = unpack11 (G g))
    (h : bfsK G k s n PT PAR LAB POS = true) :
    bfs11 gens s = (tabA n PT, tabA n PAR, tabA n LAB) ∧
      bfsOK gens s n (tabA n PT, tabA n PAR, tabA n LAB) = true := by
  have B := bf_of h
  suffices key : ∀ R, OInv n PT PAR LAB 2048 R →
      (R.2.1, R.2.2.1, R.2.2.2.1) = (tabA n PT, tabA n PAR, tabA n LAB) ∧
        bfsOK gens s n (tabA n PT, tabA n PAR, tabA n LAB) = true by
    have hO := outer_inv hg B 2048
    rw [bfs11_eq]
    exact key _ hO
  intro R hO
  obtain ⟨hi, c, I⟩ := hO
  have e1 : min 2048 n = n := by have := B.n2; omega
  rw [e1] at I
  have hcn : c = n := by
    refine le_antisymm I.cn ?_
    by_contra hlt
    have hc : c < n := by omega
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := I.c1
      omega
    · have h1 := (I.disc c hc).2 (Or.inr (by
        unfold lexP
        have := (B.edge c hc h0).1
        omega))
      omega
  subst hcn
  refine ⟨?_, ?_⟩
  · have hp := I.pts
    have hpa := I.par
    have hl := I.lab
    dsimp only at hp hpa hl
    rw [hp, hpa, hl, tabA_eq, tabA_eq, tabA_eq]
  · unfold bfsOK
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨by simp [tabA], by simp [tabA]⟩, by simp [tabA]⟩, ?_⟩, fun i hi => ?_⟩
    · rw [tabA_get B.n0, B.pt0]
    · refine ⟨⟨by rw [tabA_get hi]; exact B.ptlt i hi, ?_⟩, fun j hj => ?_⟩
      · rcases Nat.eq_zero_or_pos i with h0 | h0
        · exact Or.inl h0
        · right
          obtain ⟨e1, e2, e3⟩ := B.edge i hi h0
          rw [tabA_get hi, tabA_get hi, hg.1]
          refine ⟨⟨e1, e2⟩, ?_⟩
          rw [tabA_get (T := PT) (i := PAR i) (by omega), tabA_get (T := PT) hi, hg.2 _ e2,
            app_eq]
          exact e3
      · rw [tabA_get (by omega), tabA_get hi]
        intro e
        have := pt_inj B j (by omega) i hi e
        omega

theorem closedK_sound_proved {gens : Array (Array Nat)} {G : Nat → Nat} {k n : Nat}
    {PT POS : Nat → Nat}
    (hg : gens.size = k ∧ ∀ g < k, gens[g]! = unpack11 (G g))
    (h : closedK G k n PT POS = true) : closedOK gens (tabA n PT) n = true := by
  unfold closedK at h
  unfold closedOK
  refine List.all_eq_true.2 fun i hi => List.all_eq_true.2 fun g hgm => ?_
  have hi' := List.mem_range.1 hi
  have hg' : g < k := by rw [← hg.1]; exact List.mem_range.1 hgm
  have h1 := Orb.allN_iff.1 h i hi'
  rw [Orb.strictB_eq] at h1
  obtain ⟨l1, l2, l3⟩ := listed_of (Orb.allN_iff.1 h1 g hg')
  refine List.any_eq_true.2 ⟨POS (appK (G g) (PT i)), List.mem_range.2 l2, ?_⟩
  rw [tabA_get l2, tabA_get hi', hg.2 g hg', app_eq, l3]
  exact beq_self_eq_true _

end Proofs

theorem bfsK_sound {gens : Array (Array Nat)} {G : Nat → Nat} {k s n : Nat}
    {PT PAR LAB POS : Nat → Nat}
    (hg : gens.size = k ∧ ∀ g < k, gens[g]! = unpack11 (G g))
    (h : bfsK G k s n PT PAR LAB POS = true) :
    bfs11 gens s = (tabA n PT, tabA n PAR, tabA n LAB) ∧
      bfsOK gens s n (tabA n PT, tabA n PAR, tabA n LAB) = true :=
  bfsK_sound_proved hg h

theorem closedK_sound {gens : Array (Array Nat)} {G : Nat → Nat} {k n : Nat} {PT POS : Nat → Nat}
    (hg : gens.size = k ∧ ∀ g < k, gens[g]! = unpack11 (G g))
    (h : closedK G k n PT POS = true) : closedOK gens (tabA n PT) n = true :=
  closedK_sound_proved hg h

end CFSG.KS.SporSch.C11

end
