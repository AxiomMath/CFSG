module

public import Certificates.Data.Kernel.D4LinkK
public import CFSG.Certificates.Kernel.HexaStabKGlue
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check

public section

namespace CFSG.KC.D4Link

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Fischer CFSG.Quasithin
open CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.KLie.CT (fget)

section Replay

open CFSG.KC.Bfs (gF gStep gLoop push_get_lt push_get_of_eq)

private theorem runFV_succ (actK : ℕ → ℕ → ℕ) (ng : ℕ) (V E : ℕ → ℕ) (len lo c : ℕ) :
    runFV actK ng V E (len + 1) lo c =
      runFV actK ng V E len (lo + 1) (if lo < c then pointStepV actK ng V E lo c else 0) := by
  have h : runFV actK ng V E (len + 1) lo c =
      runFV actK ng V E len (Nat.succ lo)
        (nIf(Nat.blt lo c, pointStepV actK ng V E lo c, nat_lit 0)) :=
    CFSG.KC.BfsPin.strictN_app _ _
  rw [h]
  simp only [CFSG.KC.BfsPin.nIf_ite, Nat.blt_eq]

private theorem runFV_zero (actK : ℕ → ℕ → ℕ) (ng : ℕ) (V E : ℕ → ℕ) :
    ∀ len lo, runFV actK ng V E len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    rw [runFV_succ, if_neg (Nat.not_lt_zero lo)]
    exact runFV_zero actK ng V E len _

private theorem runFV_add (actK : ℕ → ℕ → ℕ) (ng : ℕ) (V E : ℕ → ℕ) :
    ∀ (a b lo c : ℕ), runFV actK ng V E (a + b) lo c =
      runFV actK ng V E b (lo + a) (runFV actK ng V E a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : lo + 1 + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm, runFV_succ, runFV_succ, runFV_add actK ng V E a b (lo + 1), e]

private theorem runFV_blocks (actK : ℕ → ℕ → ℕ) (ng : ℕ) (V E : ℕ → ℕ) (L : ℕ) (C : ℕ → ℕ) :
    ∀ K, (∀ s < K, runSlV actK ng V E L C s = true) →
      runFV actK ng V E (L * K) 0 (C 0) = C K
  | 0, _ => rfl
  | K + 1, h => by
    rw [Nat.mul_succ, runFV_add, runFV_blocks actK ng V E L C K (fun s hs => h s (by omega)),
      Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h K (by omega))

private theorem genStepV_eq (actK : ℕ → ℕ → ℕ) (V : ℕ → ℕ) (t row k c : ℕ) :
    genStepV actK V t row k c =
      if c = 0 then 0
      else if fget row k 12 < c then
        (if V (fget row k 12) = actK k t then c else 0)
      else if fget row k 12 = c then (if V c = actK k t then c + 1 else 0) else 0 := by
  unfold genStepV
  simp only [CFSG.KC.BfsPin.strictN_app, CFSG.KC.BfsPin.nIf_ite, Nat.beq_eq, Nat.blt_eq]

private theorem genStepV_zero (actK : ℕ → ℕ → ℕ) (V : ℕ → ℕ) (t row k : ℕ) :
    genStepV actK V t row k 0 = 0 := by
  simp only [genStepV_eq, ↓reduceIte]

private theorem genStepV_cases {actK : ℕ → ℕ → ℕ} {V : ℕ → ℕ} {t row k c : ℕ}
    (h0 : genStepV actK V t row k c ≠ 0) :
    c ≠ 0 ∧ ((fget row k 12 < c ∧ V (fget row k 12) = actK k t ∧ genStepV actK V t row k c = c) ∨
      (fget row k 12 = c ∧ V c = actK k t ∧ genStepV actK V t row k c = c + 1)) := by
  have hv := genStepV_eq actK V t row k c
  generalize genStepV actK V t row k c = r at h0 hv ⊢
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hv
    exact absurd hv h0
  simp only [h1, ↓reduceIte] at hv
  refine ⟨h1, ?_⟩
  by_cases h2 : fget row k 12 < c
  · simp only [h2, ↓reduceIte] at hv
    by_cases h3 : V (fget row k 12) = actK k t
    · simp only [h3, ↓reduceIte] at hv
      exact Or.inl ⟨h2, h3, hv⟩
    · simp only [h3, ↓reduceIte] at hv
      exact absurd hv h0
  · simp only [h2, ↓reduceIte] at hv
    by_cases h4 : fget row k 12 = c
    · by_cases h5 : V c = actK k t
      · simp only [h4, h5, ↓reduceIte] at hv
        exact Or.inr ⟨h4, h5, hv⟩
      · simp only [h4, h5, ↓reduceIte] at hv
        exact absurd hv h0
    · simp only [h4, ↓reduceIte] at hv
      exact absurd hv h0

private theorem genStepV_mono {actK : ℕ → ℕ → ℕ} {V : ℕ → ℕ} {t row k c : ℕ}
    (h0 : genStepV actK V t row k c ≠ 0) : c ≤ genStepV actK V t row k c := by
  rcases (genStepV_cases h0).2 with ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> omega

private theorem recV_eq (g : ℕ → ℕ → ℕ) (ng : ℕ) : ∀ r, r ≤ ng → ∀ c,
    Nat.rec (motive := fun _ => ℕ → ℕ) (fun c => c)
      (fun r ih c => strictN (g (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) r c =
    (List.range' (ng - r) r).foldl (fun c k => g k c) c
  | 0, _, _ => rfl
  | r + 1, h, c => by
    have e1 : Nat.sub (Nat.sub ng r) (nat_lit 1) = ng - (r + 1) := by
      change ng - r - 1 = ng - (r + 1)
      omega
    have s1 : Nat.rec (motive := fun _ => ℕ → ℕ) (fun c => c)
        (fun r ih c => strictN (g (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) (r + 1) c =
        Nat.rec (motive := fun _ => ℕ → ℕ) (fun c => c)
          (fun r ih c => strictN (g (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) r
          (g (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) := CFSG.KC.BfsPin.strictN_app _ _
    have e2 : ng - r = ng - (r + 1) + 1 := by omega
    rw [s1, e1, recV_eq g ng r (by omega), e2, List.range'_succ, List.foldl_cons]

private theorem pointStepV_foldl (actK : ℕ → ℕ → ℕ) (ng : ℕ) (V E : ℕ → ℕ) (i c : ℕ) :
    pointStepV actK ng V E i c =
      (List.range ng).foldl (fun c k => genStepV actK V (V i) (E i) k c) c := by
  have h := recV_eq (fun k c => genStepV actK V (V i) (E i) k c) ng ng le_rfl c
  rw [Nat.sub_self, ← List.range_eq_range'] at h
  refine Eq.trans ?_ h
  unfold pointStepV
  rw [CFSG.KC.BfsPin.strictN_app, CFSG.KC.BfsPin.strictN_app]

private theorem foldl_zero_v {g : ℕ → ℕ → ℕ} (hz : ∀ k, g k 0 = 0) :
    ∀ L : List ℕ, L.foldl (fun c k => g k c) 0 = 0
  | [] => rfl
  | k :: L => by rw [List.foldl_cons, hz, foldl_zero_v hz L]

private theorem foldl_mono_v {g : ℕ → ℕ → ℕ} (hz : ∀ k, g k 0 = 0)
    (hg : ∀ k c, g k c ≠ 0 → c ≤ g k c) :
    ∀ (L : List ℕ) (c : ℕ), L.foldl (fun c k => g k c) c ≠ 0 → c ≤ L.foldl (fun c k => g k c) c
  | [], _, _ => le_rfl
  | k :: L, c, h => by
    rw [List.foldl_cons] at h ⊢
    have h1 : g k c ≠ 0 := fun e => h (by rw [e, foldl_zero_v hz])
    exact le_trans (hg k c h1) (foldl_mono_v hz hg L _ h)

private theorem pointStepV_mono {actK : ℕ → ℕ → ℕ} {ng : ℕ} {V E : ℕ → ℕ} {i c : ℕ}
    (h : pointStepV actK ng V E i c ≠ 0) : c ≤ pointStepV actK ng V E i c := by
  rw [pointStepV_foldl] at h ⊢
  exact foldl_mono_v (g := fun k c => genStepV actK V (V i) (E i) k c)
    (fun k => genStepV_zero actK V (V i) (E i) k) (fun k c' h' => genStepV_mono h') _ c h

private theorem runFV_mono {actK : ℕ → ℕ → ℕ} {ng : ℕ} {V E : ℕ → ℕ} :
    ∀ len lo c, runFV actK ng V E len lo c ≠ 0 → c ≤ runFV actK ng V E len lo c
  | 0, _, _, _ => le_rfl
  | len + 1, lo, c, h => by
    rw [runFV_succ] at h ⊢
    by_cases hlo : lo < c
    · rw [if_pos hlo] at h ⊢
      have h1 := runFV_mono len (lo + 1) _ h
      have hp : pointStepV actK ng V E lo c ≠ 0 := fun e => by
        rw [e, runFV_zero] at h
        exact h rfl
      exact le_trans (pointStepV_mono hp) h1
    · rw [if_neg hlo] at h
      exact absurd (runFV_zero _ _ _ _ _ _) h

private def StOK (key : Array ℕ → ℕ) (U : ℕ → Array ℕ) (c : ℕ) (pts : Array (Array ℕ))
    (idx : Std.HashMap ℕ ℕ) : Prop :=
  pts.size = c ∧ (∀ j < c, pts[j]! = U j) ∧ (∀ j < c, idx[key (U j)]? = some j) ∧
    ∀ m j, idx[m]? = some j → j < c ∧ key (U j) = m

private def TrOK (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (U : ℕ → Array ℕ) (c : ℕ)
    (par lab : Array ℕ) : Prop :=
  par.size = c ∧ lab.size = c ∧ ∀ j, 0 < j → j < c →
    par[j]! < j ∧ lab[j]! < ngen ∧ U j = act lab[j]! (U par[j]!)

private def RwOK (act : ℕ → Array ℕ → Array ℕ) (U : ℕ → Array ℕ) (E : ℕ → ℕ) (i c n : ℕ)
    (row : Array ℕ) : Prop :=
  row.size = n ∧ ∀ k < n, row[k]! = fget (E i) k 12 ∧ row[k]! < c ∧ U row[k]! = act k (U i)

private def EdOK (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (U : ℕ → Array ℕ) (E : ℕ → ℕ)
    (lo c : ℕ) (edges : Array (Array ℕ)) : Prop :=
  edges.size = lo ∧ ∀ j < lo, RwOK act U E j c ngen edges[j]!

private theorem RwOK.mono {act : ℕ → Array ℕ → Array ℕ} {U : ℕ → Array ℕ} {E : ℕ → ℕ}
    {i c c' n : ℕ} {row : Array ℕ} (h : RwOK act U E i c n row) (hc : c ≤ c') :
    RwOK act U E i c' n row :=
  ⟨h.1, fun k hk => ⟨(h.2 k hk).1, lt_of_lt_of_le (h.2 k hk).2.1 hc, (h.2 k hk).2.2⟩⟩

private theorem EdOK.push {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ} {U : ℕ → Array ℕ}
    {E : ℕ → ℕ} {lo c c' : ℕ} {edges : Array (Array ℕ)} {row : Array ℕ}
    (he : EdOK act ngen U E lo c edges) (hr : RwOK act U E lo c' ngen row) (hc : c ≤ c') :
    EdOK act ngen U E (lo + 1) c' (edges.push row) := by
  refine ⟨by rw [Array.size_push, he.1], fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
  · rw [push_get_lt _ _ (by rw [he.1]; exact hj)]
    exact (he.2 j hj).mono hc
  · rw [hj, push_get_of_eq _ _ he.1]
    exact hr

private theorem gF_st {act : ℕ → Array ℕ → Array ℕ} {key : Array ℕ → ℕ} {U : ℕ → Array ℕ}
    {E : ℕ → ℕ} {ngen N : ℕ} (hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b)
    {c i k r : ℕ} {pts : Array (Array ℕ)} {par lab row : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hs : StOK key U c pts idx) (ht : TrOK act ngen U c par lab) (hi : i < c)
    (hrow : RwOK act U E i c k row) (hk : k < ngen)
    (hr : (fget (E i) k 12 < c ∧ act k (U i) = U (fget (E i) k 12) ∧ r = c) ∨
      (fget (E i) k 12 = c ∧ act k (U i) = U c ∧ r = c + 1))
    (hrN : r ≤ N) :
    StOK key U r (gF act key i (pts, par, lab, idx, row) k).1
        (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 ∧
      TrOK act ngen U r (gF act key i (pts, par, lab, idx, row) k).2.1
        (gF act key i (pts, par, lab, idx, row) k).2.2.1 ∧
      RwOK act U E i r (k + 1) (gF act key i (pts, par, lab, idx, row) k).2.2.2.2 := by
  have hpi : pts[i]! = U i := hs.2.1 i hi
  have hsz : pts.size = c := hs.1
  simp only [gF]
  split
  · next j heq =>
    rw [Std.HashMap.get?_eq_getElem?, hpi] at heq
    obtain ⟨hj, hkj⟩ := hs.2.2.2 _ _ heq
    rcases hr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hjk : j = fget (E i) k 12 := by
        have := hs.2.2.1 (fget (E i) k 12) h1
        rw [← h2, heq] at this
        exact Option.some.inj this
      rw [h3]
      refine ⟨hs, ht, ?_, fun k' hk' => ?_⟩
      · show (row.push j).size = k + 1
        rw [Array.size_push, hrow.1]
      · show (row.push j)[k']! = fget (E i) k' 12 ∧ (row.push j)[k']! < c ∧
          U (row.push j)[k']! = act k' (U i)
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | hk'
        · rw [push_get_lt _ _ (by rw [hrow.1]; exact hk')]
          exact hrow.2 k' hk'
        · rw [hk', push_get_of_eq _ _ hrow.1, hjk]
          exact ⟨rfl, h1, h2.symm⟩
    · rw [h2] at hkj
      have := hinj j (by omega) c (by omega) hkj
      omega
  · next heq =>
    rw [Std.HashMap.get?_eq_getElem?, hpi] at heq
    rcases hr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h2, hs.2.2.1 _ h1] at heq
      exact absurd heq (by simp)
    · dsimp only
      rw [hpi, h2, h3]
      have hne : ∀ j < c, key (U c) ≠ key (U j) := fun j hj h' => by
        have := hinj c (by omega) j (by omega) h'
        omega
      refine ⟨⟨by rw [Array.size_push, hsz], fun j hj => ?_, fun j hj => ?_, fun m j h => ?_⟩,
        ⟨by rw [Array.size_push, ht.1], by rw [Array.size_push, ht.2.1], fun j h0 hj => ?_⟩,
        by rw [Array.size_push, hrow.1], fun k' hk' => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [push_get_lt _ _ (by rw [hsz]; exact hj)]
          exact hs.2.1 j hj
        · rw [hj]
          exact push_get_of_eq _ _ hsz
      · rw [Std.HashMap.getElem?_insert]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · simp only [beq_iff_eq, hne j hj, ↓reduceIte]
          exact hs.2.2.1 j hj
        · rw [hj]
          simp only [beq_self_eq_true, ↓reduceIte, hsz]
      · rw [Std.HashMap.getElem?_insert] at h
        split at h
        · next e' =>
          rw [beq_iff_eq] at e'
          cases h
          exact ⟨by omega, by rw [hsz, e']⟩
        · obtain ⟨hj, e'⟩ := hs.2.2.2 m j h
          exact ⟨by omega, e'⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · obtain ⟨hp, hl, e⟩ := ht.2.2 j h0 hj
          rw [push_get_lt par i (by rw [ht.1]; exact hj),
            push_get_lt lab k (by rw [ht.2.1]; exact hj)]
          exact ⟨hp, hl, e⟩
        · rw [hj, push_get_of_eq par i ht.1, push_get_of_eq lab k ht.2.1]
          exact ⟨hi, hk, h2.symm⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | hk'
        · rw [push_get_lt _ _ (by rw [hrow.1]; exact hk')]
          obtain ⟨a, b, d⟩ := hrow.2 k' hk'
          exact ⟨a, by omega, d⟩
        · rw [hk', push_get_of_eq _ _ hrow.1, hsz]
          exact ⟨h1.symm, by omega, h2.symm⟩

private theorem fold_st {act : ℕ → Array ℕ → Array ℕ} {key : Array ℕ → ℕ} {U : ℕ → Array ℕ}
    {E : ℕ → ℕ} {ngen N : ℕ} (hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b)
    {g : ℕ → ℕ → ℕ} {i : ℕ} (hz : ∀ k, g k 0 = 0)
    (hg : ∀ k < ngen, ∀ c, g k c ≠ 0 →
      ((fget (E i) k 12 < c ∧ act k (U i) = U (fget (E i) k 12) ∧ g k c = c) ∨
        (fget (E i) k 12 = c ∧ act k (U i) = U c ∧ g k c = c + 1))) :
    ∀ n, n ≤ ngen → ∀ (c : ℕ) (pts : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), StOK key U c pts idx → TrOK act ngen U c par lab → i < c →
      ∀ s, s = (List.range n).foldl (gF act key i) (pts, par, lab, idx, #[]) →
      ∀ cn, cn = (List.range n).foldl (fun c k => g k c) c → cn ≠ 0 → cn ≤ N →
      c ≤ cn ∧ StOK key U cn s.1 s.2.2.2.1 ∧ TrOK act ngen U cn s.2.1 s.2.2.1 ∧
        RwOK act U E i cn n s.2.2.2.2 := by
  intro n
  induction n with
  | zero =>
    intro _ c pts par lab idx hs ht _ s hs' cn hcn _ _
    subst hs' hcn
    exact ⟨le_rfl, hs, ht, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn c pts par lab idx hs ht hi s hs' cn hcn h0 hN
    subst hs' hcn
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h0 hN ⊢
    have hc0 : (List.range n).foldl (fun c k => g k c) c ≠ 0 := fun e => h0 (by rw [e, hz])
    have hg1 := hg n hn _ h0
    have hcle : (List.range n).foldl (fun c k => g k c) c ≤ N := by
      rcases hg1 with ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> omega
    obtain ⟨hmono, hs1, ht1, hr1⟩ :=
      ih (by omega) c pts par lab idx hs ht hi _ rfl _ rfl hc0 hcle
    generalize (List.range n).foldl (gF act key i) (pts, par, lab, idx, #[]) = s1 at hs1 ht1 hr1 ⊢
    generalize (List.range n).foldl (fun c k => g k c) c = c1 at hmono hs1 ht1 hr1 hg1 h0 hN ⊢
    obtain ⟨p, q, l, d, w⟩ := s1
    obtain ⟨hs2, ht2, hr2⟩ := gF_st hinj hs1 ht1 (by omega) hr1 (by omega) hg1 hN
    refine ⟨?_, hs2, ht2, hr2⟩
    rcases hg1 with ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> omega

private theorem gLoop_done' {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ} {key : Array ℕ → ℕ}
    {N : ℕ} (f : ℕ) (pts : Array (Array ℕ)) (edges : Array (Array ℕ)) (par lab : Array ℕ)
    (idx : Std.HashMap ℕ ℕ) (h : pts.size = N) :
    gLoop act ngen key f N pts edges par lab idx = (pts, edges, par, lab) := by
  cases f with
  | zero => rfl
  | succ f => rw [gLoop, if_neg (by omega)]

private theorem loop_st {act : ℕ → Array ℕ → Array ℕ} {key : Array ℕ → ℕ} {U : ℕ → Array ℕ}
    {actP : ℕ → ℕ → ℕ} {V E : ℕ → ℕ} {ngen N : ℕ}
    (hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b)
    (hstep : ∀ i < N, ∀ k < ngen, ∀ j, V j = actP k (V i) → act k (U i) = U j) :
    ∀ len lo c f (pts : Array (Array ℕ)) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), StOK key U c pts idx → TrOK act ngen U c par lab →
      EdOK act ngen U E lo c edges → len ≤ f →
      runFV actP ngen V E len lo c ≠ 0 → runFV actP ngen V E len lo c ≤ N →
      ∃ (pts' : Array (Array ℕ)) (edges' : Array (Array ℕ)) (par' lab' : Array ℕ)
        (idx' : Std.HashMap ℕ ℕ),
        StOK key U (runFV actP ngen V E len lo c) pts' idx' ∧
        TrOK act ngen U (runFV actP ngen V E len lo c) par' lab' ∧
        EdOK act ngen U E (lo + len) (runFV actP ngen V E len lo c) edges' ∧
        gLoop act ngen key f lo pts edges par lab idx =
          gLoop act ngen key (f - len) (lo + len) pts' edges' par' lab' idx'
  | 0, lo, c, f, pts, edges, par, lab, idx, hs, ht, he, _, _, _ =>
    ⟨pts, edges, par, lab, idx, hs, ht, he, rfl⟩
  | len + 1, lo, c, f, pts, edges, par, lab, idx, hs, ht, he, hf, h0, hN => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hlo : lo < c := by
      by_contra hlo
      rw [runFV_succ, if_neg hlo, runFV_zero] at h0
      exact h0 rfl
    have hrun : runFV actP ngen V E (len + 1) lo c =
        runFV actP ngen V E len (lo + 1) (pointStepV actP ngen V E lo c) := by
      rw [runFV_succ, if_pos hlo]
    rw [hrun] at h0 hN ⊢
    have hp0 : pointStepV actP ngen V E lo c ≠ 0 := fun e => by
      rw [e, runFV_zero] at h0
      exact h0 rfl
    have hpN : pointStepV actP ngen V E lo c ≤ N := le_trans (runFV_mono _ _ _ h0) hN
    have hloN : lo < N := by
      have := pointStepV_mono hp0
      omega
    have hg : ∀ k < ngen, ∀ c', genStepV actP V (V lo) (E lo) k c' ≠ 0 →
        ((fget (E lo) k 12 < c' ∧ act k (U lo) = U (fget (E lo) k 12) ∧
            genStepV actP V (V lo) (E lo) k c' = c') ∨
          (fget (E lo) k 12 = c' ∧ act k (U lo) = U c' ∧
            genStepV actP V (V lo) (E lo) k c' = c' + 1)) := by
      intro k hk c' h'
      rcases (genStepV_cases h').2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, hstep lo hloN k hk _ h2, h3⟩
      · exact Or.inr ⟨h1, hstep lo hloN k hk _ h2, h3⟩
    rw [pointStepV_foldl] at hp0 hpN h0 hN ⊢
    obtain ⟨hcc, hs1, ht1, hr1⟩ :=
      fold_st hinj (g := fun k c => genStepV actP V (V lo) (E lo) k c)
        (fun k => genStepV_zero actP V (V lo) (E lo) k) hg ngen le_rfl c pts par lab idx hs ht hlo
        _ rfl _ rfl hp0 hpN
    rw [gLoop, if_pos (by rw [hs.1]; exact hlo)]
    have e1 : gStep act ngen key lo (pts, par, lab, idx) =
        (List.range ngen).foldl (gF act key lo) (pts, par, lab, idx, #[]) := rfl
    rw [e1]
    generalize (List.range ngen).foldl (gF act key lo) (pts, par, lab, idx, #[]) = s
      at hs1 ht1 hr1 ⊢
    obtain ⟨a, b, l, d, w⟩ := s
    obtain ⟨pts', edges', par', lab', idx', hst', htt', hee', heq⟩ :=
      loop_st hinj hstep len (lo + 1) _ f a (edges.push w) b l d hs1 ht1 (he.push hr1 hcc)
        (by omega) h0 hN
    have e2 : f + 1 - (len + 1) = f - len := by omega
    have e3 : lo + (len + 1) = lo + 1 + len := by omega
    rw [e2, e3]
    exact ⟨pts', edges', par', lab', idx', hst', htt', hee', heq⟩

end Replay

theorem arrPin_sound {act : ℕ → Array ℕ → Array ℕ} {valid : Array ℕ → Bool}
    {key : Array ℕ → ℕ} {actP : ℕ → ℕ → ℕ} {keyP : ℕ → ℕ} {validP : ℕ → Bool}
    {dec : ℕ → Array ℕ} {root : Array ℕ} {ngen N L K fuel : ℕ} {V E S C : ℕ → ℕ}
    (hact : ∀ k < ngen, ∀ v, validP v = true → act k (dec v) = dec (actP k v))
    (hvalid : ∀ v, validP v = true → valid (dec v) = true)
    (hkey : ∀ v, key (dec v) = keyP v) (hroot : root = dec (V 0))
    (hN : N = L * K) (hL : 0 < L) (hfuel : N ≤ fuel) (hv : ∀ i < N, validP (V i) = true)
    (hD : CFSG.KC.BfsPin.distinctK N (fun i => keyP (V i)) S = true)
    (hC0 : C 0 = 1) (hCK : C K = N) (hr : ∀ s < K, runSlV actP ngen V E L C s = true) :
    arrCertOK act ngen valid key root (arrBfs act ngen key root fuel) = true ∧
      (arrBfs act ngen key root fuel).pts.size = N ∧
      (∀ i < N, (arrBfs act ngen key root fuel).pts[i]! = dec (V i)) ∧
      ∀ i < N, ∀ k < ngen, ((arrBfs act ngen key root fuel).edges[i]!)[k]! = fget (E i) k 12 := by
  have _ := hL
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Array ℕ, ∀ j, U j = dec (V j) := ⟨fun j => dec (V j), fun _ => rfl⟩
  have hU0 : U 0 = root := by rw [hU, hroot]
  have hkeyU : ∀ j, key (U j) = keyP (V j) := fun j => by rw [hU, hkey]
  have hinj : ∀ a < N, ∀ b < N, key (U a) = key (U b) → a = b := by
    intro a ha b hb e
    refine CFSG.KC.BfsPin.distinctK_inj hD a ha b hb ?_
    show keyP (V a) = keyP (V b)
    rw [← hkeyU, ← hkeyU]
    exact e
  have hstep : ∀ i < N, ∀ k < ngen, ∀ j, V j = actP k (V i) → act k (U i) = U j := by
    intro i hi k hk j hj
    rw [hU i, hU j, hj]
    exact hact k hk (V i) (hv i hi)
  have hR : runFV actP ngen V E N 0 1 = N := by
    have h := runFV_blocks actP ngen V E L C K hr
    rw [hC0, hCK, ← hN] at h
    exact h
  have hN0 : N ≠ 0 := by
    intro e
    have e1 : runFV actP ngen V E 0 0 1 = 1 := rfl
    rw [e] at hR
    omega
  have hst0 : StOK key U 1 #[root] ((∅ : Std.HashMap ℕ ℕ).insert (key root) 0) := by
    refine ⟨rfl, fun j hj => ?_, fun j hj => ?_, fun m j h => ?_⟩
    · have e : j = 0 := by omega
      rw [e, hU0]
      simp
    · have e : j = 0 := by omega
      rw [e, hU0]
      simp
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · next e =>
        rw [beq_iff_eq] at e
        cases h
        exact ⟨by omega, by rw [hU0, e]⟩
      · rw [Std.HashMap.getElem?_empty] at h
        exact absurd h (by simp)
  have ht0 : TrOK act ngen U 1 #[0] #[0] := ⟨rfl, rfl, fun j h0 hj => absurd hj (by omega)⟩
  have he0 : EdOK act ngen U E 0 1 #[] := ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  obtain ⟨pts', edges', par', lab', idx', hst', ht', he', heq⟩ :=
    loop_st (act := act) (key := key) (actP := actP) hinj hstep N 0 1 fuel #[root] #[] #[0] #[0] _
      hst0 ht0 he0 hfuel (by rw [hR]; exact hN0) hR.le
  rw [hR] at hst' ht'
  rw [hR, Nat.zero_add] at he'
  have hsz : pts'.size = N := hst'.1
  have hget : ∀ i < N, pts'[i]! = dec (V i) := fun i hi => (hst'.2.1 i hi).trans (hU i)
  have hgb : CFSG.KC.Bfs.gBfs act ngen key root fuel = (pts', edges', par', lab') := by
    unfold CFSG.KC.Bfs.gBfs
    rw [heq, Nat.zero_add, gLoop_done' _ _ _ _ _ _ hsz]
  have hA : arrBfs act ngen key root fuel = ⟨pts', edges', par', lab'⟩ := by
    rw [CFSG.KC.Bfs.arrBfs_eq, hgb]
  have hnd : (pts'.toList.map key).Nodup := by
    refine CFSG.KC.Bfs.nodup_map_of_inj key fun a ha b hb e => ?_
    rw [hsz] at ha hb
    rw [hst'.2.1 a ha, hst'.2.1 b hb] at e
    exact hinj a ha b hb e
  rw [hA]
  refine ⟨?_, hsz, hget, fun i hi k hk => ((he'.2 i hi).2 k hk).1⟩
  simp only [arrCertOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨by omega, ?_⟩, fun i hi => ?_⟩, CFSG.KC.Bfs.pairwise_lt_mergeSort hnd⟩
  · rw [hst'.2.1 0 (by omega), hU0]
  · have hi' : i < N := by omega
    simp only [arrPointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    obtain ⟨hrs, hre⟩ := he'.2 i hi'
    refine ⟨⟨⟨?_, hrs⟩, fun k hk => ?_⟩, ?_⟩
    · rw [hget i hi']
      exact hvalid _ (hv i hi')
    · obtain ⟨-, hlt, hUe⟩ := hre k hk
      refine ⟨by omega, ?_⟩
      rw [hst'.2.1 _ hlt, hst'.2.1 i hi']
      exact hUe
    · rcases Nat.eq_zero_or_pos i with h | h
      · exact Or.inl h
      · obtain ⟨hp, hl, e⟩ := ht'.2.2 i h hi'
        refine Or.inr ⟨⟨hp, hl⟩, ?_⟩
        rw [hst'.2.1 i hi', hst'.2.1 _ (by omega)]
        exact e

theorem mulK_eq : ∀ a < 8, ∀ b < 8, mulK a b = GF8.mulNat a b := by decide +kernel

theorem invK_eq : ∀ c < 8, invK c = ginv c := by decide +kernel

theorem pg3_lt (V j : ℕ) : pg 3 (mask 3) V j < 8 := by
  unfold pg
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide +kernel)

theorem vget_lt (V j : ℕ) : vget V j < 8 := by
  unfold vget
  exact pg3_lt V j

theorem mulK_lt (a b : ℕ) : mulK a b < 8 := by
  unfold mulK
  exact pg3_lt _ _

theorem invK_lt (c : ℕ) : invK c < 8 := by
  unfold invK
  exact pg3_lt _ _

theorem unpack_get8 (V : ℕ) {j : ℕ} (hj : j < 8) : (unpack 8 3 V)[j]! = vget V j := by
  rw [getElem!_pos _ j (by simpa [unpack] using hj)]
  simp [unpack, vget]

theorem dotK_lt (M V i : ℕ) : dotK M V i < 8 := by
  unfold dotK
  apply_rules [xor_lt8, mulK_lt]

theorem leadF_lt {f : ℕ → ℕ} (hf : ∀ j < 8, f j < 8) : leadF f < 8 := by
  unfold leadF
  split
  · exact hf _ (Fin.isLt _)
  · norm_num

theorem leadF_congr {f g : ℕ → ℕ} (h : ∀ j < 8, f j = g j) : leadF f = leadF g := by
  have h' : ∀ i : Fin 8, f i.val = g i.val := fun i => h i.val i.isLt
  unfold leadF
  simp only [h']

theorem nzF_congr {f g : ℕ → ℕ} (h : ∀ j < 8, f j = g j) : nzF f = nzF g := by
  have h' : ∀ i : Fin 8, f i.val = g i.val := fun i => h i.val i.isLt
  unfold nzF
  simp only [h']

theorem strictN_app' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem leadCode_eq (w : Array ℕ) : leadCode w = leadF (fun j => w[j]!) := rfl

theorem unpack8_size (V : ℕ) : (unpack 8 3 V).size = 8 := by simp [unpack]

theorem vget_pmk {f : ℕ → ℕ} (hf : ∀ x < 8, f x < 8) {i : ℕ} (hi : i < 8) :
    vget (pmk 8 3 f) i = f i := by
  unfold vget
  exact CFSG.KC.HexaStabK.pg_pmk (by norm_num) (fun x hx => by
    have := hf x hx
    norm_num
    exact this) hi

theorem projAct_eq {GM : ℕ → ℕ} {k : ℕ}
    (hG : ∀ t < 64, (genCodes.getD k #[])[t]! = vget (GM k) t) (V : ℕ) :
    projAct k (unpack 8 3 V) = unpack 8 3 (actK GM k V) := by
  have hm : ∀ a b, GF8.mulNat (vget (GM k) a) (vget V b) = mulK (vget (GM k) a) (vget V b) :=
    fun a b => (mulK_eq _ (vget_lt _ _) _ (vget_lt _ _)).symm
  have hd : ∀ i < 8, dotCode (genCodes.getD k #[]) (unpack 8 3 V) i = dotK (GM k) V i := by
    intro i hi
    unfold dotCode dotK
    rw [hG _ (by omega), hG _ (by omega), hG _ (by omega), hG _ (by omega), hG _ (by omega),
      hG _ (by omega), hG _ (by omega), hG _ (by omega), unpack_get8 V (by norm_num : 0 < 8),
      unpack_get8 V (by norm_num : 1 < 8), unpack_get8 V (by norm_num : 2 < 8),
      unpack_get8 V (by norm_num : 3 < 8), unpack_get8 V (by norm_num : 4 < 8),
      unpack_get8 V (by norm_num : 5 < 8), unpack_get8 V (by norm_num : 6 < 8),
      unpack_get8 V (by norm_num : 7 < 8)]
    simp only [hm]
  have hW : ∀ i < 8, vget (mvK (GM k) V) i = dotK (GM k) V i := fun i hi =>
    vget_pmk (fun x _ => dotK_lt _ _ _) hi
  have hl : leadF (vget (mvK (GM k) V)) = leadF (dotK (GM k) V) := leadF_congr hW
  have hl8 : leadF (dotK (GM k) V) < 8 := leadF_lt fun j _ => dotK_lt _ _ _
  have hX : ∀ j < 8, (Array.ofFn (n := 8) fun i => dotCode (genCodes.getD k #[])
      (unpack 8 3 V) i.val)[j]! = dotK (GM k) V j := fun j hj => by
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    exact hd j hj
  have hlc : leadCode (Array.ofFn (n := 8) fun i => dotCode (genCodes.getD k #[])
      (unpack 8 3 V) i.val) = leadF (dotK (GM k) V) := by
    rw [leadCode_eq]
    exact leadF_congr hX
  have hg : ginv (leadF (dotK (GM k) V)) < 8 := by
    rw [← invK_eq _ hl8]
    exact invK_lt _
  unfold projAct normCode mulVecCode actK normK
  rw [strictN_app', strictN_app', hl, hlc, invK_eq _ hl8]
  apply Array.ext
  · simp [unpack]
  · intro i h1 h2
    have hi : i < 8 := by simpa using h1
    rw [Array.getElem_map, Array.getElem_ofFn, hd i hi]
    simp only [unpack, Array.getElem_ofFn]
    change _ = vget (pmk 8 3 fun i => mulK (ginv (leadF (dotK (GM k) V))) (vget (mvK (GM k) V) i)) i
    rw [vget_pmk (fun x _ => mulK_lt _ _) hi, hW i hi, mulK_eq _ hg _ (dotK_lt _ _ _)]

theorem validV_eq (V : ℕ) : validV (unpack 8 3 V) = validK V := by
  have hall : (unpack 8 3 V).all (· < 8) = true := by
    rw [Array.all_eq_true]
    intro i hi
    simp only [unpack, Array.getElem_ofFn, decide_eq_true_eq]
    exact vget_lt V i
  have hany : (unpack 8 3 V).any (· != 0) = nzF (vget V) := by
    unfold nzF
    rw [Bool.eq_iff_iff, Array.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨i, hi, h⟩
      have hi8 : i < 8 := by simpa [unpack] using hi
      refine ⟨⟨i, hi8⟩, List.mem_finRange _, ?_⟩
      simpa [unpack, vget, mask] using h
    · rintro ⟨i, -, h⟩
      refine ⟨i.val, by simp [unpack], ?_⟩
      simpa [unpack, vget, mask] using h
  have hlead : leadCode (unpack 8 3 V) = leadF (vget V) := by
    rw [leadCode_eq]
    exact leadF_congr fun j hj => unpack_get8 V hj
  unfold validV validK
  rw [unpack8_size]
  simp only [unpack8_size] at hall hany
  rw [hall, hany, hlead]
  rfl

theorem keyV_eq (V : ℕ) : keyV (unpack 8 3 V) = keyK V := by
  unfold keyV keyK kstep
  rw [← Array.foldl_toList]
  simp [unpack, List.ofFn_succ, vget]

end CFSG.KC.D4Link

end
