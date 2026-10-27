module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByList
public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Perm.Native

open CFSG.Sporadic.Th.Native

@[expose] def conjApply (T : Tree) (letters : Array Table) (k j : ℕ) (q : Array ℕ) : Array ℕ :=
  walk T letters j (walk T letters k (walkInv T letters j q))

@[expose] def prodApply (T : Tree) (letters : Array Table) (k : ℕ) (wl : List ℕ) (q : Array ℕ) :
    Array ℕ :=
  walk T letters k (wl.foldr (fun j q => conjApply T letters k j q) q)

@[expose] def powApply (f : Array ℕ → Array ℕ) : ℕ → Array ℕ → Array ℕ
  | 0, q => q
  | m + 1, q => f (powApply f m q)

@[expose] def witOK (T : Tree) (letters : Array Table) (k : ℕ) (wl : List ℕ) (m : ℕ)
    (q : Array ℕ) : Bool :=
  !tupleEq (powApply (prodApply T letters k wl) m q) q

end CFSG.Perm.Native

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

section Walks

variable {T : Tree} {letters : Array Table} {lG : ℕ → G}

@[expose] def Pts (n : ℕ) (q : Array ℕ) : Prop := ∀ t < q.size, q[t]! < n

theorem Pts.walk (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size) {q : Array ℕ}
    (hq : Pts n q) :
    Pts n (walk T letters k q) ∧ ∀ t < q.size, (walk T letters k q)[t]! = idx n (treeG T lG k) q[t]! := by
  obtain ⟨hs, he⟩ := walk_spec hW hk q hq
  refine ⟨fun t ht => ?_, he⟩
  rw [hs] at ht
  rw [he t ht]
  exact idx_lt _ (hq t ht)

theorem Pts.walkInv (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size) {q : Array ℕ}
    (hq : Pts n q) :
    Pts n (walkInv T letters k q) ∧
      ∀ t < q.size, (walkInv T letters k q)[t]! = idx n (treeG T lG k)⁻¹ q[t]! := by
  obtain ⟨hs, he⟩ := walkInv_spec hW hk q hq
  refine ⟨fun t ht => ?_, he⟩
  rw [hs] at ht
  rw [he t ht]
  exact idx_lt _ (hq t ht)

theorem walk_size' (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size) {q : Array ℕ}
    (hq : Pts n q) : (walk T letters k q).size = q.size := (walk_spec hW hk q hq).1

theorem walkInv_size' (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size)
    {q : Array ℕ} (hq : Pts n q) : (walkInv T letters k q).size = q.size :=
  (walkInv_spec hW hk q hq).1

@[expose] noncomputable def conjG (T : Tree) (lG : ℕ → G) (k j : ℕ) : G :=
  treeG T lG j * treeG T lG k * (treeG T lG j)⁻¹

theorem conjApply_spec (hW : WalkFacts n T letters lG) {k j : ℕ} (hk : k < T.pts.size)
    (hj : j < T.pts.size) {q : Array ℕ} (hq : Pts n q) :
    Pts n (conjApply T letters k j q) ∧ (conjApply T letters k j q).size = q.size ∧
      ∀ t < q.size, (conjApply T letters k j q)[t]! = idx n (conjG T lG k j) q[t]! := by
  obtain ⟨h1, e1⟩ := Pts.walkInv hW hj hq
  have s1 := walkInv_size' hW hj hq
  obtain ⟨h2, e2⟩ := Pts.walk hW hk h1
  have s2 := walk_size' hW hk h1
  obtain ⟨h3, e3⟩ := Pts.walk hW hj h2
  have s3 := walk_size' hW hj h2
  refine ⟨h3, by rw [conjApply, s3, s2, s1], fun t ht => ?_⟩
  rw [conjApply, e3 t (by rw [s2, s1]; exact ht), e2 t (by rw [s1]; exact ht), e1 t ht,
    conjG, idx_mul, idx_mul]

@[expose] noncomputable def prodG (T : Tree) (lG : ℕ → G) (k : ℕ) (wl : List ℕ) : G :=
  treeG T lG k * (wl.map fun j => conjG T lG k j).prod

theorem foldr_conj_spec (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size) :
    ∀ (wl : List ℕ), (∀ j ∈ wl, j < T.pts.size) → ∀ {q : Array ℕ}, Pts n q →
      Pts n (wl.foldr (fun j q => conjApply T letters k j q) q) ∧
        (wl.foldr (fun j q => conjApply T letters k j q) q).size = q.size ∧
        ∀ t < q.size, (wl.foldr (fun j q => conjApply T letters k j q) q)[t]! =
          idx n (wl.map fun j => conjG T lG k j).prod q[t]! := by
  intro wl
  induction wl with
  | nil => intro _ q hq; exact ⟨hq, rfl, fun t _ => by simp [idx_one]⟩
  | cons j wl ih =>
    intro hwl q hq
    obtain ⟨h1, s1, e1⟩ := ih (fun j' hj' => hwl j' (List.mem_cons_of_mem _ hj')) hq
    obtain ⟨h2, s2, e2⟩ := conjApply_spec hW hk (hwl j List.mem_cons_self) h1
    refine ⟨h2, by rw [List.foldr_cons, s2, s1], fun t ht => ?_⟩
    rw [List.foldr_cons, e2 t (by rw [s1]; exact ht), e1 t ht, List.map_cons, List.prod_cons,
      idx_mul]

theorem prodApply_spec (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size)
    {wl : List ℕ} (hwl : ∀ j ∈ wl, j < T.pts.size) {q : Array ℕ} (hq : Pts n q) :
    Pts n (prodApply T letters k wl q) ∧ (prodApply T letters k wl q).size = q.size ∧
      ∀ t < q.size, (prodApply T letters k wl q)[t]! = idx n (prodG T lG k wl) q[t]! := by
  obtain ⟨h1, s1, e1⟩ := foldr_conj_spec hW hk wl hwl hq
  obtain ⟨h2, e2⟩ := Pts.walk hW hk h1
  have s2 := walk_size' hW hk h1
  refine ⟨h2, by rw [prodApply, s2, s1], fun t ht => ?_⟩
  rw [prodApply, e2 t (by rw [s1]; exact ht), e1 t ht, prodG, idx_mul]

theorem powApply_spec {f : Array ℕ → Array ℕ} {g : G}
    (hf : ∀ q, Pts n q → Pts n (f q) ∧ (f q).size = q.size ∧ ∀ t < q.size, (f q)[t]! = idx n g q[t]!) :
    ∀ (m : ℕ) {q : Array ℕ}, Pts n q →
      Pts n (powApply f m q) ∧ (powApply f m q).size = q.size ∧
        ∀ t < q.size, (powApply f m q)[t]! = idx n (g ^ m) q[t]! := by
  intro m
  induction m with
  | zero => intro q hq; exact ⟨hq, rfl, fun t _ => by rw [powApply, pow_zero, idx_one]⟩
  | succ m ih =>
    intro q hq
    obtain ⟨h1, s1, e1⟩ := ih hq
    obtain ⟨h2, s2, e2⟩ := hf _ h1
    refine ⟨h2, by rw [powApply, s2, s1], fun t ht => ?_⟩
    rw [powApply, e2 t (by rw [s1]; exact ht), e1 t ht, pow_succ', idx_mul]

theorem prodG_pow_ne_one_of_witOK (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size)
    {wl : List ℕ} (hwl : ∀ j ∈ wl, j < T.pts.size) {q : Array ℕ} (hq : Pts n q) {m : ℕ}
    (h : witOK T letters k wl m q = true) : prodG T lG k wl ^ m ≠ 1 := by
  intro h1
  obtain ⟨-, s, e⟩ := powApply_spec (fun q hq => prodApply_spec hW hk hwl hq) m hq
  unfold witOK at h
  simp only [Bool.not_eq_true'] at h
  have : tupleEq (powApply (prodApply T letters k wl) m q) q = true := by
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq]
    refine ⟨s, allIn_eq_true.2 fun t _ ht => ?_⟩
    rw [e t ht, h1, idx_one]
    simp
  rw [this] at h
  exact Bool.noConfusion h

end Walks

theorem gLAPPrimeCoreOf_eq_bot_of_tree [Finite G] {p : ℕ} (hp : p.Prime) {y : G}
    {letters : Array Table} {gs : ℕ → G}
    (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j)) (h2 : letters.size % 2 = 0)
    (hinv : ∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true)
    {lv : Array ℕ} (hlv : ∀ l ∈ lv, l < letters.size) {T : Tree} {r : ℕ}
    (htree : Perm.Native.treeOK n r T letters lv = true)
    (hcomm : ∀ l ∈ lv, pairG gs l * y = y * pairG gs l)
    (hcard : Nat.card (Subgroup.centralizer ({y} : Set G)) ≤ T.pts.size) {m a : ℕ}
    (hn : T.pts.size = p ^ a * m) (wit : ℕ → List ℕ)
    (hwit : ∀ i < T.pts.size, ∀ j ∈ wit i, j < T.pts.size) {q : Array ℕ} (hq : Pts n q)
    (hw : ∀ i < T.pts.size, 0 < i → witOK T letters i (wit i) m q = true) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) = ⊥ := by
  have hrepAll := rep_pairG hrep h2 hinv
  have hTF : TreeFacts n T lv (pairG gs) r := treeOK_facts (fun l hl => hrepAll l (hlv l hl)) htree
  have hW : WalkFacts n T letters (pairG gs) := by
    intro k hk hk0
    obtain ⟨hpar, hlab⟩ := hTF.par k hk hk0
    have hl := hlv _ hlab
    refine ⟨hpar, hrepAll _ hl, ?_⟩
    rw [← pairG_invL]
    exact hrepAll _ (invL_lt h2 hl)
  have hle : lettersGroup lv (pairG gs) ≤ Subgroup.centralizer ({y} : Set G) := by
    unfold lettersGroup
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm l hl)
  refine gLAPPrimeCoreOf_eq_bot_of_list hp hn (fun i => treeG T (pairG gs) i)
    (fun i hi => hle (hTF.treeG_mem hi)) (fun i hi j hj hij => ?_) hcard wit hwit
    (fun i hi hne => ?_)
  · apply Nat.ne_of_gt hj
    refine hTF.pts_inj hi (lt_trans hj hi) ?_
    rw [← hTF.elt i hi, ← hTF.elt j (lt_trans hj hi)]
    exact congrArg (fun g => idx n g r) hij
  · have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · exfalso; apply hne
        show treeG T (pairG gs) 0 = 1
        rw [treeG.eq_def, dif_neg (by omega)]
      · exact h
    exact prodG_pow_ne_one_of_witOK hW hi (hwit i hi) hq (hw i hi hi0)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
