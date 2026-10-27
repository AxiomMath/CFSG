module

public import Certificates.Data.Kernel.BfsPinKeyRun
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinSetSound
import all CFSG.Certificates.Kernel.Spor.PrimSound

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs
open CFSG.KLie.CT (fget)

theorem keyM_eq {n w : Nat} {ps : List Nat} (hn : n < 2 ^ 32) (hps : ∀ p ∈ ps, p < n)
    (g t : Nat) : keyM n w (mask w) ps g t = keyK n w ps (pcomp n w (mask w) g t) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have e1 := CFSG.KS.PF.pg_pcomp (w := w) (p := g) (q := t) hn (hps p List.mem_cons_self)
    have e2 := ih fun q hq => hps q (List.mem_cons_of_mem p hq)
    change Nat.add (pg w (mask w) g (pg w (mask w) t p)) (Nat.mul n (keyM n w (mask w) ps g t)) =
      Nat.add (pg w (mask w) (pcomp n w (mask w) g t) p)
        (Nat.mul n (keyK n w ps (pcomp n w (mask w) g t)))
    rw [e1, e2]

theorem genStepB_eq (n w m : Nat) (ps : List Nat) (T : Nat → Nat) (t row g k c : Nat) :
    genStepB n w m ps T t row g k c =
      if c = 0 then 0
      else if fget row k 16 < c then
        (if keyK n w ps (T (fget row k 16)) = keyM n w m ps g t then c else 0)
      else if fget row k 16 = c then (if T c = pcomp n w m g t then c + 1 else 0) else 0 := by
  unfold genStepB
  simp only [strictN_app, nIf_ite, Nat.beq_eq, Nat.blt_eq]

theorem genStepB_zero (n w m : Nat) (ps : List Nat) (T : Nat → Nat) (t row g k : Nat) :
    genStepB n w m ps T t row g k 0 = 0 := by
  simp only [genStepB_eq, ↓reduceIte]

private theorem genStepB_cases {n w m : Nat} {ps : List Nat} {T : Nat → Nat} {t row g k c : Nat}
    (h0 : genStepB n w m ps T t row g k c ≠ 0) :
    ((∃ j < c, keyK n w ps (T j) = keyM n w m ps g t) ∧ genStepB n w m ps T t row g k c = c) ∨
      (T c = pcomp n w m g t ∧ genStepB n w m ps T t row g k c = c + 1) := by
  have hv := genStepB_eq n w m ps T t row g k c
  generalize genStepB n w m ps T t row g k c = r at h0 hv ⊢
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hv
    exact absurd hv h0
  simp only [h1, ↓reduceIte] at hv
  by_cases h2 : fget row k 16 < c
  · simp only [h2, ↓reduceIte] at hv
    by_cases h3 : keyK n w ps (T (fget row k 16)) = keyM n w m ps g t
    · simp only [h3, ↓reduceIte] at hv
      exact Or.inl ⟨⟨_, h2, h3⟩, hv⟩
    · simp only [h3, ↓reduceIte] at hv
      exact absurd hv h0
  · simp only [h2, ↓reduceIte] at hv
    by_cases h4 : fget row k 16 = c
    · by_cases h5 : T c = pcomp n w m g t
      · simp only [h4, h5, ↓reduceIte] at hv
        exact Or.inr ⟨h5, hv⟩
      · simp only [h4, h5, ↓reduceIte] at hv
        exact absurd hv h0
    · simp only [h4, ↓reduceIte] at hv
      exact absurd hv h0

@[expose] noncomputable def pointFB (n w m : Nat) (ps : List Nat) (G T E : Nat → Nat) (i len : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => ih (Nat.succ lo) (genStepB n w m ps T (T i) (E i) (G lo) lo c)) len

@[expose] noncomputable def pointRecB (n w m ng : Nat) (ps : List Nat) (G T E : Nat → Nat)
    (i r : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (genStepB n w m ps T (T i) (E i)
      (G (Nat.sub (Nat.sub ng r) (nat_lit 1))) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) r

private theorem pointRecB_eq {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ r, r ≤ ng → ∀ c, pointRecB n w m ng ps G T E i r c = pointFB n w m ps G T E i r (ng - r) c
  | 0, _, _ => rfl
  | r + 1, h, c => by
    have e1 : Nat.sub (Nat.sub ng r) (nat_lit 1) = ng - (r + 1) := by
      change ng - r - 1 = ng - (r + 1)
      omega
    have e2 : Nat.succ (ng - (r + 1)) = ng - r := by omega
    have s1 : pointRecB n w m ng ps G T E i (r + 1) c = pointRecB n w m ng ps G T E i r
        (genStepB n w m ps T (T i) (E i) (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
          (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) := strictN_app _ _
    have s2 : pointFB n w m ps G T E i (r + 1) (ng - (r + 1)) c = pointFB n w m ps G T E i r
        (Nat.succ (ng - (r + 1)))
        (genStepB n w m ps T (T i) (E i) (G (ng - (r + 1))) (ng - (r + 1)) c) := rfl
    rw [s1, s2, e1, e2, pointRecB_eq i r (by omega)]

private theorem pointStepB_eq {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (i c : Nat) :
    pointStepB n w m ng ps G T E i c = pointFB n w m ps G T E i ng 0 c := by
  have h := pointRecB_eq (n := n) (w := w) (m := m) (ng := ng) (ps := ps) (G := G) (T := T)
    (E := E) i ng (Nat.le_refl ng) c
  rw [Nat.sub_self] at h
  rw [← h]
  unfold pointStepB
  rw [strictN_app, strictN_app]
  rfl

private theorem pointFB_foldl {n w m : Nat} {ps : List Nat} {G T E : Nat → Nat} (i : Nat) :
    ∀ len lo c, pointFB n w m ps G T E i len lo c =
      (List.range' lo len).foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c
  | 0, _, _ => rfl
  | len + 1, lo, c => by
    rw [List.range'_succ, List.foldl_cons]
    exact pointFB_foldl i len (lo + 1) _

private theorem pointStepB_foldl {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (i c : Nat) :
    pointStepB n w m ng ps G T E i c =
      (List.range ng).foldl (fun c k => genStepB n w m ps T (T i) (E i) (G k) k c) c := by
  rw [pointStepB_eq, pointFB_foldl, List.range_eq_range']

private def StB (key : Array Nat → Nat) (U : Nat → Array Nat) (c : Nat) (pts : Array (Array Nat))
    (idx : Std.HashMap Nat Nat) : Prop :=
  pts.size = c ∧ (∀ j < c, pts[j]! = U j) ∧ (∀ j < c, idx[key (U j)]? = some j) ∧
    ∀ m j, idx[m]? = some j → j < c ∧ key (U j) = m

section Search

variable {act : Nat → Array Nat → Array Nat} {key : Array Nat → Nat} {U : Nat → Array Nat}
  {N : Nat}

private theorem gF_stB (hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b)
    {c i k r : Nat} {pts : Array (Array Nat)} {par lab row : Array Nat} {idx : Std.HashMap Nat Nat}
    (hs : StB key U c pts idx) (hi : i < c)
    (hr : ((∃ j < c, key (act k (U i)) = key (U j)) ∧ r = c) ∨ (act k (U i) = U c ∧ r = c + 1))
    (hrN : r ≤ N) :
    StB key U r (gF act key i (pts, par, lab, idx, row) k).1
      (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 := by
  have hpi : pts[i]! = U i := hs.2.1 i hi
  simp only [gF]
  split
  · next j heq =>
    rw [Std.HashMap.get?_eq_getElem?, hpi] at heq
    obtain ⟨hj, hkj⟩ := hs.2.2.2 _ _ heq
    rcases hr with ⟨-, rfl⟩ | ⟨e, rfl⟩
    · exact hs
    · rw [e] at hkj
      exact absurd (hinj j (by omega) c (by omega) hkj) (by omega)
  · next heq =>
    rw [Std.HashMap.get?_eq_getElem?, hpi] at heq
    rcases hr with ⟨⟨j, hj, e⟩, -⟩ | ⟨e, rfl⟩
    · rw [e, hs.2.2.1 j hj] at heq
      exact absurd heq (by simp)
    · dsimp only
      rw [hpi, e]
      have hne : ∀ j < c, key (U c) ≠ key (U j) := fun j hj h' => by
        have := hinj c (by omega) j (by omega) h'
        omega
      refine ⟨by rw [Array.size_push, hs.1], fun j hj => ?_, fun j hj => ?_, fun m j h => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [push_get_lt _ _ (by rw [hs.1]; exact hj)]
          exact hs.2.1 j hj
        · exact push_get_of_eq _ _ hs.1
      · rw [Std.HashMap.getElem?_insert]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · simp only [beq_iff_eq, hne j hj, ↓reduceIte]
          exact hs.2.2.1 j hj
        · simp only [beq_self_eq_true, ↓reduceIte, hs.1]
      · rw [Std.HashMap.getElem?_insert] at h
        split at h
        · next e' =>
          rw [beq_iff_eq] at e'
          cases h
          have := hs.1
          exact ⟨by omega, by rw [hs.1, e']⟩
        · obtain ⟨hj, e'⟩ := hs.2.2.2 m j h
          exact ⟨by omega, e'⟩

private theorem foldl_zeroB {g : Nat → Nat → Nat} (hz : ∀ k, g k 0 = 0) :
    ∀ L : List Nat, L.foldl (fun c k => g k c) 0 = 0
  | [] => rfl
  | k :: L => by rw [List.foldl_cons, hz, foldl_zeroB hz L]

private theorem foldl_monoB {g : Nat → Nat → Nat} (hz : ∀ k, g k 0 = 0) {P : Nat → Prop}
    (hg : ∀ k, P k → ∀ c, g k c ≠ 0 → c ≤ g k c) :
    ∀ L : List Nat, (∀ k ∈ L, P k) → ∀ c, L.foldl (fun c k => g k c) c ≠ 0 →
      c ≤ L.foldl (fun c k => g k c) c
  | [], _, _, _ => le_rfl
  | k :: L, hL, c, h => by
    rw [List.foldl_cons] at h ⊢
    have h1 : g k c ≠ 0 := fun e => h (by rw [e, foldl_zeroB hz])
    exact le_trans (hg k (hL k List.mem_cons_self) c h1)
      (foldl_monoB hz hg L (fun k' hk' => hL k' (List.mem_cons_of_mem k hk')) _ h)

private theorem fold_stB (hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b)
    {g : Nat → Nat → Nat} {i ng : Nat} (hz : ∀ k, g k 0 = 0)
    (hg : ∀ k < ng, ∀ c, g k c ≠ 0 →
      ((∃ j < c, key (act k (U i)) = key (U j)) ∧ g k c = c) ∨
        (act k (U i) = U c ∧ g k c = c + 1)) :
    ∀ (L : List Nat), (∀ k ∈ L, k < ng) → ∀ (c : Nat) (pts : Array (Array Nat))
      (par lab row : Array Nat) (idx : Std.HashMap Nat Nat), StB key U c pts idx → i < c →
      L.foldl (fun c k => g k c) c ≠ 0 → L.foldl (fun c k => g k c) c ≤ N →
      StB key U (L.foldl (fun c k => g k c) c) (L.foldl (gF act key i) (pts, par, lab, idx, row)).1
        (L.foldl (gF act key i) (pts, par, lab, idx, row)).2.2.2.1
  | [], _, _, _, _, _, _, _, hs, _, _, _ => hs
  | k :: L, hL, c, pts, par, lab, row, idx, hs, hi, h0, hN => by
    rw [List.foldl_cons] at h0 hN ⊢
    have hk := hL k List.mem_cons_self
    have hL' : ∀ k' ∈ L, k' < ng := fun k' hk' => hL k' (List.mem_cons_of_mem k hk')
    have h1 : g k c ≠ 0 := fun e => h0 (by rw [e, foldl_zeroB hz])
    have hmono : ∀ k < ng, ∀ c, g k c ≠ 0 → c ≤ g k c := fun k hk c h => by
      rcases hg k hk c h with ⟨-, e⟩ | ⟨-, e⟩ <;> omega
    have hc1 := hmono k hk c h1
    have hle := foldl_monoB hz hmono L hL' (g k c) h0
    have hs1 := gF_stB (row := row) (par := par) (lab := lab) hinj hs hi (hg k hk c h1) (by omega)
    exact fold_stB hinj hz hg L hL' (g k c) _ (gF act key i (pts, par, lab, idx, row) k).2.1
      (gF act key i (pts, par, lab, idx, row) k).2.2.1
      (gF act key i (pts, par, lab, idx, row) k).2.2.2.2
      (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 hs1 (by omega) h0 hN

end Search

private theorem pointStepB_mono {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} {i c : Nat}
    (h : pointStepB n w m ng ps G T E i c ≠ 0) : c ≤ pointStepB n w m ng ps G T E i c := by
  rw [pointStepB_foldl] at h ⊢
  exact foldl_monoB (P := fun _ => True) (fun k => genStepB_zero n w m ps T (T i) (E i) (G k) k)
    (fun k _ c' h' => by rcases genStepB_cases h' with ⟨-, e⟩ | ⟨-, e⟩ <;> omega)
    _ (fun _ _ => trivial) c h

theorem runFB_succ {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (len lo c : Nat) :
    runFB n w m ng ps G T E (len + 1) lo c =
      runFB n w m ng ps G T E len (Nat.succ lo) (nIf(Nat.blt lo c,
        pointStepB n w m ng ps G T E lo c, nat_lit 0)) :=
  strictN_app _ _

theorem runFB_zero {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} :
    ∀ len lo, runFB n w m ng ps G T E len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    rw [runFB_succ]
    have hb : Nat.blt lo 0 = false := by
      cases h : Nat.blt lo 0
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt_zero lo)
    rw [hb]
    exact runFB_zero len _

private theorem runFB_mono {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} : ∀ len lo c,
    runFB n w m ng ps G T E len lo c ≠ 0 → c ≤ runFB n w m ng ps G T E len lo c
  | 0, _, _, _ => le_rfl
  | len + 1, lo, c, h => by
    rw [runFB_succ] at h ⊢
    cases hb : Nat.blt lo c
    · rw [hb] at h
      exact absurd (runFB_zero len _) h
    · rw [hb] at h
      have h1 := runFB_mono len (Nat.succ lo) _ h
      have hp : pointStepB n w m ng ps G T E lo c ≠ 0 := fun e => by
        change runFB n w m ng ps G T E len (Nat.succ lo) (pointStepB n w m ng ps G T E lo c) ≠ 0
          at h
        rw [e, runFB_zero] at h
        exact h rfl
      exact le_trans (pointStepB_mono hp) h1

private theorem loop_stB {n w ng N : Nat} {G T E : Nat → Nat} {gs : Array (Array Nat)}
    {ps : List Nat} (hs : gs.size = ng)
    (hinj : ∀ a < N, ∀ b < N, keyA n ps (unpack n w (T a)) = keyA n ps (unpack n w (T b)) → a = b)
    (hstep : ∀ i < N, ∀ k < ng,
      leftA n gs k (unpack n w (T i)) = unpack n w (pcomp n w (mask w) (G k) (T i)))
    (hkey : ∀ i < N, ∀ k < ng, ∀ j,
      keyK n w ps (T j) = keyM n w (mask w) ps (G k) (T i) →
        keyA n ps (leftA n gs k (unpack n w (T i))) = keyA n ps (unpack n w (T j))) :
    ∀ len lo c f (pts : Array (Array Nat)) (edges : Array (Array Nat)) (par lab : Array Nat)
      (idx : Std.HashMap Nat Nat), StB (keyA n ps) (fun j => unpack n w (T j)) c pts idx →
      len ≤ f → runFB n w (mask w) ng ps G T E len lo c ≠ 0 →
      runFB n w (mask w) ng ps G T E len lo c ≤ N →
      ∃ (pts' : Array (Array Nat)) (edges' : Array (Array Nat)) (par' lab' : Array Nat)
        (idx' : Std.HashMap Nat Nat),
        StB (keyA n ps) (fun j => unpack n w (T j)) (runFB n w (mask w) ng ps G T E len lo c)
          pts' idx' ∧
        gLoop (leftA n gs) gs.size (keyA n ps) f lo pts edges par lab idx =
          gLoop (leftA n gs) gs.size (keyA n ps) (f - len) (lo + len) pts' edges' par' lab' idx'
  | 0, lo, c, f, pts, edges, par, lab, idx, hst, _, _, _ =>
    ⟨pts, edges, par, lab, idx, hst, rfl⟩
  | len + 1, lo, c, f, pts, edges, par, lab, idx, hst, hf, h0, hN => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [runFB_succ] at h0 hN ⊢
    cases hb : Nat.blt lo c
    · rw [hb] at h0
      exact absurd (runFB_zero len _) h0
    · rw [hb] at h0 hN
      change runFB n w (mask w) ng ps G T E len (Nat.succ lo)
        (pointStepB n w (mask w) ng ps G T E lo c) ≠ 0 at h0
      change runFB n w (mask w) ng ps G T E len (Nat.succ lo)
        (pointStepB n w (mask w) ng ps G T E lo c) ≤ N at hN
      change ∃ (pts' : Array (Array Nat)) (edges' : Array (Array Nat)) (par' lab' : Array Nat)
        (idx' : Std.HashMap Nat Nat),
        StB (keyA n ps) (fun j => unpack n w (T j))
          (runFB n w (mask w) ng ps G T E len (Nat.succ lo)
            (pointStepB n w (mask w) ng ps G T E lo c)) pts' idx' ∧
        gLoop (leftA n gs) gs.size (keyA n ps) (f + 1) lo pts edges par lab idx =
          gLoop (leftA n gs) gs.size (keyA n ps) (f + 1 - (len + 1)) (lo + (len + 1)) pts' edges'
            par' lab' idx'
      have hlo : lo < c := Nat.blt_eq.mp hb
      have hp0 : pointStepB n w (mask w) ng ps G T E lo c ≠ 0 := fun e => by
        rw [e, runFB_zero] at h0
        exact h0 rfl
      have hpN : pointStepB n w (mask w) ng ps G T E lo c ≤ N :=
        le_trans (runFB_mono len _ _ h0) hN
      have hloN : lo < N := by
        have := pointStepB_mono hp0
        omega
      have hg : ∀ k < ng, ∀ c', genStepB n w (mask w) ps T (T lo) (E lo) (G k) k c' ≠ 0 →
          ((∃ j < c', keyA n ps (leftA n gs k (unpack n w (T lo))) =
              keyA n ps (unpack n w (T j))) ∧
            genStepB n w (mask w) ps T (T lo) (E lo) (G k) k c' = c') ∨
          (leftA n gs k (unpack n w (T lo)) = unpack n w (T c') ∧
            genStepB n w (mask w) ps T (T lo) (E lo) (G k) k c' = c' + 1) := by
        intro k hk c' h'
        rcases genStepB_cases h' with ⟨⟨j, hj, e⟩, e2⟩ | ⟨e, e2⟩
        · exact Or.inl ⟨⟨j, hj, hkey lo hloN k hk j e⟩, e2⟩
        · exact Or.inr ⟨by rw [hstep lo hloN k hk, e], e2⟩
      rw [pointStepB_foldl] at hp0 hpN h0 hN ⊢
      have hfold := fold_stB (act := leftA n gs) (key := keyA n ps)
        (U := fun j => unpack n w (T j)) hinj
        (fun k => genStepB_zero n w (mask w) ps T (T lo) (E lo) (G k) k) hg (List.range ng)
        (fun k hk => List.mem_range.1 hk) c pts par lab #[] idx hst hlo hp0 hpN
      have hst1 := hst
      rw [gLoop, ite_eq_left (by rw [hst1.1]; exact hlo)]
      have e1 : gStep (leftA n gs) gs.size (keyA n ps) lo (pts, par, lab, idx) =
          (List.range ng).foldl (gF (leftA n gs) (keyA n ps) lo) (pts, par, lab, idx, #[]) := by
        unfold gStep
        rw [hs]
      rw [e1]
      generalize (List.range ng).foldl (gF (leftA n gs) (keyA n ps) lo) (pts, par, lab, idx, #[]) =
        s at hfold
      obtain ⟨a, b, l, d, r⟩ := s
      obtain ⟨pts', edges', par', lab', idx', hst', heq⟩ :=
        loop_stB hs hinj hstep hkey len (Nat.succ lo) _ f a (edges.push r) b l d hfold (by omega)
          h0 hN
      refine ⟨pts', edges', par', lab', idx', hst', ?_⟩
      have e2 : f + 1 - (len + 1) = f - len := by omega
      have e3 : lo + (len + 1) = Nat.succ lo + len := by omega
      rw [e2, e3]
      exact heq

private theorem gLoop_doneB {act : Nat → Array Nat → Array Nat} {ngen : Nat}
    {key : Array Nat → Nat} {N : Nat} (f : Nat) (pts : Array (Array Nat))
    (edges : Array (Array Nat)) (par lab : Array Nat) (idx : Std.HashMap Nat Nat)
    (h : pts.size = N) : (gLoop act ngen key f N pts edges par lab idx).1 = pts := by
  cases f with
  | zero => rfl
  | succ f =>
    rw [gLoop, ite_eq_right (by omega)]

theorem enumBfs_pts_key {n w ng N fuel : Nat} {G T E : Nat → Nat} {SK : List Nat}
    {gs : Array (Array Nat)} {ps : List Nat} (hs : gs.size = ng)
    (hg : ∀ k < ng, gs[k]! = unpack n w (G k)) (hsz : szOK n w = true)
    (hcG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true)
    (hcT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true) (hT0 : T 0 = pidn n w)
    (hps : ∀ p ∈ ps, p < n) (hK : keysSK n w ps N T SK = true)
    (hR : runFB n w (mask w) ng ps G T E N 0 1 = N) (hf : N ≤ fuel) :
    (enumBfs n gs ps fuel).pts = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
  obtain ⟨hn, hw⟩ := szOK_facts hsz
  have hn32 : n < 2 ^ 32 := by
    have := (szOK_facts' hsz).1
    omega
  have hinj : ∀ a < N, ∀ b < N,
      keyA n ps (unpack n w (T a)) = keyA n ps (unpack n w (T b)) → a = b := by
    intro a ha b hb e
    refine keysSK_spec hK a ha b hb ?_
    rw [keyA_unpack hps, keyA_unpack hps] at e
    exact e
  have hstep : ∀ i < N, ∀ k < ng,
      leftA n gs k (unpack n w (T i)) = unpack n w (pcomp n w (mask w) (G k) (T i)) := by
    intro i hi k hk1
    unfold leftA
    rw [hg k hk1, compA_unpack (hcG k hk1) (hcT i hi)]
  have hkey : ∀ i < N, ∀ k < ng, ∀ j,
      keyK n w ps (T j) = keyM n w (mask w) ps (G k) (T i) →
        keyA n ps (leftA n gs k (unpack n w (T i))) = keyA n ps (unpack n w (T j)) := by
    intro i hi k hk j e
    rw [hstep i hi k hk, keyA_unpack hps, keyA_unpack hps]
    change keyK n w ps (pcomp n w (mask w) (G k) (T i)) = keyK n w ps (T j)
    rw [e, keyM_eq hn32 hps]
  have hN : N ≠ 0 := by
    intro e
    subst e
    have e1 : runFB n w (mask w) ng ps G T E 0 0 1 = 1 := rfl
    omega
  have hU0 : unpack n w (T 0) = idA n := by
    rw [hT0, unpack_pidn hn hw]
  have hst0 : StB (keyA n ps) (fun j => unpack n w (T j)) 1 #[idA n]
      ((∅ : Std.HashMap Nat Nat).insert (keyA n ps (idA n)) 0) := by
    refine ⟨rfl, fun j hj => ?_, fun j hj => ?_, fun m j h => ?_⟩
    · have e : j = 0 := by omega
      subst e
      dsimp only
      rw [hU0]
      simp
    · have e : j = 0 := by omega
      subst e
      dsimp only
      rw [hU0]
      simp
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · next e =>
        rw [beq_iff_eq] at e
        cases h
        exact ⟨by omega, by dsimp only; rw [hU0, e]⟩
      · rw [Std.HashMap.getElem?_empty] at h
        exact absurd h (by simp)
  obtain ⟨pts', edges', par', lab', idx', hst', heq⟩ :=
    loop_stB hs hinj hstep hkey N 0 1 fuel #[idA n] #[] #[0] #[0] _ hst0 hf
      (by rw [hR]; exact hN) (by rw [hR])
  rw [hR] at hst'
  unfold enumBfs
  rw [arrBfs_eq]
  change (gLoop (leftA n gs) gs.size (keyA n ps) fuel 0 #[idA n] #[] #[0] #[0]
    ((∅ : Std.HashMap Nat Nat).insert (keyA n ps (idA n)) 0)).1 = _
  rw [heq, Nat.zero_add, gLoop_doneB _ _ _ _ _ _ hst'.1]
  apply Array.ext
  · rw [hst'.1, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← getElem!_pos pts' i h1]
    exact hst'.2.1 i (by rw [hst'.1] at h1; exact h1)

theorem runFB_add {n w m ng : Nat} {ps : List Nat} {G T E : Nat → Nat} : ∀ (a b lo c : Nat),
    runFB n w m ng ps G T E (a + b) lo c =
      runFB n w m ng ps G T E b (lo + a) (runFB n w m ng ps G T E a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : Nat.succ lo + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm, runFB_succ, runFB_succ, runFB_add a b (Nat.succ lo), e]

theorem runFB_blocks {n w ng : Nat} {ps : List Nat} {G T E : Nat → Nat} (L : Nat)
    (C : Nat → Nat) : ∀ K, (∀ s < K, runSlB n w ng ps G T E L C s = true) →
      runFB n w (mask w) ng ps G T E (L * K) 0 (C 0) = C K
  | 0, _ => rfl
  | K + 1, h => by
    rw [Nat.mul_succ, runFB_add, runFB_blocks L C K (fun s hs => h s (by omega)), Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h K (by omega))

theorem runFB_of_slices {n w ng N L K : Nat} {ps : List Nat} {G T E C : Nat → Nat}
    (hN : N = L * K) (hL : 0 < L) (hc : ∀ s < K, canonSl n w T L s = true) (hC0 : C 0 = 1)
    (hCK : C K = N) (hr : ∀ s < K, runSlB n w ng ps G T E L C s = true) :
    runFB n w (mask w) ng ps G T E N 0 1 = N ∧
      ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := by
  refine ⟨?_, fun i hi => ?_⟩
  · have h := runFB_blocks L C K hr
    rw [hC0, hCK, ← hN] at h
    exact h
  · rw [hN] at hi
    have hs : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 (by rwa [Nat.mul_comm] at hi)
    have h1 := hc (i / L) hs
    unfold canonSl at h1
    have h2 := allN_spec h1 (i % L) (Nat.mod_lt _ hL)
    have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
    rw [e] at h2
    exact h2

end CFSG.KC.BfsPin

end
