module

public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Certificates.Data.CFSGNative.J3.Check
import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KS.J3Sub

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.TBfs CFSG.Perm.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.J3.Native

theorem allIn_iff' {s e : Nat} {p : Nat → Bool} :
    allIn s e p = true ↔ ∀ i, s ≤ i → i < e → p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i h1 h2
    have := h ⟨i - s, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' h1] using this
  · intro h ⟨i, hi⟩ _
    simpa using h (s + i) (by omega) (by omega)

theorem set!_get' {α : Type} [Inhabited α] {a : Array α} {i j : Nat} {v : α} (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by simp; omega), getElem!_pos a j hj]
  by_cases e : i = j
  · subst e
    simp
  · rw [Array.getElem_setIfInBounds_ne hj e]
    simp [e]

theorem fold_range'_ind {β : Type} (f : β → Nat → β) (P : Nat → β → Prop) (m : Nat) (b : β)
    (h0 : P 0 b) (h : ∀ j < m, ∀ b, P j b → P (j + 1) (f b j)) :
    P m ((List.range' 0 m).foldl f b) := by
  induction m with
  | zero => simpa using h0
  | succ m ih =>
    rw [List.range'_concat, List.foldl_append]
    simpa using h m (by omega) _ (ih fun j hj b hb => h j (by omega) b hb)

theorem labelsOf_eq (n : Nat) (S : Array Tree) :
    labelsOf n S = (List.range' 0 S.size).foldl (fun labs j =>
      (List.range' 0 S[j]!.pts.size).foldl (fun labs k => labs.set! (ap S[j]!.pts k) j) labs)
      (Array.replicate n 0) := by
  unfold labelsOf
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl]

theorem labelsOf_get {n k : Nat} {S : Array Tree} {CNT : Nat → Nat} {PT : Nat → Nat → Nat}
    {LBL : Nat → Nat} (hS : S.size = k) (hsz : ∀ j < k, S[j]!.pts.size = CNT j)
    (hpt : ∀ j < k, ∀ q < CNT j, ap S[j]!.pts q = PT j q ∧ PT j q < n)
    (hq : ∀ j < k, ∀ q < CNT j, LBL (PT j q) = j)
    (hz : ∀ z < n, LBL z < k ∧ ∃ q < CNT (LBL z), PT (LBL z) q = z) :
    (labelsOf n S).size = n ∧ ∀ p < n, (labelsOf n S)[p]! = LBL p := by
  rw [labelsOf_eq, hS]
  have := fold_range'_ind (fun labs j =>
      (List.range' 0 S[j]!.pts.size).foldl (fun labs k => labs.set! (ap S[j]!.pts k) j) labs)
    (fun J (labs : Array Nat) => labs.size = n ∧ ∀ p < n, LBL p < J → labs[p]! = LBL p) k
    (Array.replicate n 0) ⟨by simp, fun p _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun J hJ labs hP => by
      rw [hsz J hJ]
      have := fold_range'_ind (fun labs k => labs.set! (ap S[J]!.pts k) J)
        (fun K (labs : Array Nat) => labs.size = n ∧ ∀ p < n,
          (LBL p < J ∨ (LBL p = J ∧ ∃ q < K, PT J q = p)) → labs[p]! = LBL p) (CNT J) labs
        ⟨hP.1, fun p hp h => by
          rcases h with h | ⟨-, q, hq0, -⟩
          · exact hP.2 p hp h
          · exact absurd hq0 (Nat.not_lt_zero _)⟩
        (fun K hK labs hQ => by
          obtain ⟨e, hx⟩ := hpt J hJ K hK
          rw [e]
          refine ⟨by simp [hQ.1], fun p hp h => ?_⟩
          rw [set!_get' (by rw [hQ.1]; exact hp)]
          by_cases ex : PT J K = p
          · rw [ite_eq_left ex, ← ex, hq J hJ K hK]
          · rw [ite_eq_right ex]
            refine hQ.2 p hp ?_
            rcases h with h | ⟨h1, q, hq1, h2⟩
            · exact Or.inl h
            · refine Or.inr ⟨h1, q, ?_, h2⟩
              rcases Nat.lt_or_ge q K with a | a
              · exact a
              · exact absurd (by rw [show q = K by omega] at h2; exact h2) ex)
      refine ⟨this.1, fun p hp h => this.2 p hp ?_⟩
      rcases Nat.lt_or_ge (LBL p) J with a | a
      · exact Or.inl a
      · have e : LBL p = J := by omega
        obtain ⟨-, q, hq1, h2⟩ := hz p hp
        exact Or.inr ⟨e, q, by rw [← e]; exact hq1, by rw [← e]; exact h2⟩)
  exact ⟨this.1, fun p hp => this.2 p hp (hz p hp).1⟩

theorem pts_ap {n cnt : Nat} {PTS POS PAR LAB : Nat → Nat} {i : Nat} (hi : i < cnt) :
    ap (tbfsRec n cnt PTS POS PAR LAB).pts i = r32 PTS i := ap_ofFn hi

theorem pos_ap {n cnt : Nat} {PTS POS PAR LAB : Nat → Nat} {z : Nat} (hz : z < n) :
    ap (tbfsRec n cnt PTS POS PAR LAB).pos z = r32 POS z := ap_ofFn hz

theorem walkInv_one {n NL cnt : Nat} {letters : Array Table} {L : Nat → Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat}
    (hL : ∀ l < NL, ∀ x < n, ap letters[l]! x = L l x ∧ L l x < n)
    (hlab : ∀ q < cnt, 0 < q → invL (r32 LAB q) < NL) :
    ∀ f kk, kk < cnt → kk ≤ f → ∀ y < n, ∃ w < n,
      walkInv (tbfsRec n cnt PTS POS PAR LAB) letters kk #[y] = #[w] ∧
        walkInvF L PAR LAB f kk [y] = [w] := by
  intro f
  induction f with
  | zero =>
    intro kk _ hkf y hy
    have : kk = 0 := by omega
    subst this
    refine ⟨y, hy, ?_, rfl⟩
    rw [walkInv]
    simp
  | succ f ih =>
    intro kk hk hkf y hy
    have hpar : ap (tbfsRec n cnt PTS POS PAR LAB).par kk = r32 PAR kk := ap_ofFn hk
    have hlb : ap (tbfsRec n cnt PTS POS PAR LAB).lab kk = r32 LAB kk := ap_ofFn hk
    rw [walkInv, hpar, hlb, walkInvF_succ]
    by_cases hc : 0 < kk ∧ r32 PAR kk < kk
    · rw [dite_eq_left hc, ite_eq_left hc, CFSG.KS.TW.apT_map, mapK_eq, xor_one]
      obtain ⟨e1, e2⟩ := hL _ (hlab kk hk hc.1) y hy
      have e3 : #[y].map (ap letters[invL (r32 LAB kk)]!) = #[L (invL (r32 LAB kk)) y] := by
        simp [e1]
      rw [e3, List.map_singleton]
      exact ih _ (by omega) (by omega) _ e2
    · rw [dite_eq_right hc, ite_eq_right hc]
      exact ⟨y, hy, rfl, rfl⟩

section

variable {n k : Nat} {T : Tree} {letters : Array Table} {reps labs : Array Nat}
  {LBL : Nat → Nat} {F : Nat → Nat × Nat → Nat} {KK : Nat → Nat} {W : Nat → Nat → Nat}

theorem testBit_or_shift (b x j : Nat) :
    (b ||| (1 <<< x)).testBit j = (b.testBit j || decide (x = j)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem deriv_fold (hlabs : ∀ y < n, labs[y]! = LBL y ∧ LBL y < k) (hreps : reps.size = k)
    (hw : ∀ i < k, ∀ y < n, ap T.pos reps[i]! = KK i ∧ W i y < n ∧
      walkInv T letters (KK i) #[y] = #[W i y])
    (hF : ∀ b s, F b s = if s.1 < k ∧ s.2 < n ∧ b.testBit s.1 ∧ b.testBit (LBL s.2) then
      b ||| (1 <<< LBL (W s.1 s.2)) else b) :
    ∀ (steps : List (Nat × Nat)) (A : Array Bool) (b : Nat),
      (A.size = k ∧ ∀ j < k, A[j]! = b.testBit j) →
      (steps.foldl (derivStep n T letters reps labs) A).size = k ∧
        ∀ j < k, (steps.foldl (derivStep n T letters reps labs) A)[j]! =
          (steps.foldl F b).testBit j := by
  intro steps
  induction steps with
  | nil => intro A b h; exact h
  | cons s steps ih =>
    intro A b ⟨hA1, hA2⟩
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    rw [hF]
    unfold derivStep
    by_cases hc : s.1 < k ∧ s.2 < n ∧ b.testBit s.1 ∧ b.testBit (LBL s.2)
    · obtain ⟨h1, h2, h3, h4⟩ := hc
      obtain ⟨hl1, hl2⟩ := hlabs s.2 h2
      obtain ⟨e1, e2, e3⟩ := hw s.1 h1 s.2 h2
      have hcn : (decide (s.1 < reps.size) && decide (s.2 < n) && A[s.1]! && A[labs[s.2]!]!) =
          true := by
        rw [hreps, hl1, hA2 _ h1, hA2 _ hl2, h3, h4]
        simp [h1, h2]
      have hinv : invLabel T letters labs (ap T.pos reps[s.1]!) s.2 = LBL (W s.1 s.2) := by
        unfold invLabel
        rw [e1, e3]
        exact (hlabs _ e2).1
      have hlw := (hlabs _ e2).2
      rw [ite_eq_left hcn, ite_eq_left ⟨h1, h2, h3, h4⟩, hinv]
      refine ⟨by simp [hA1], fun j hj => ?_⟩
      rw [set!_get' (by rw [hA1]; exact hj), testBit_or_shift, hA2 j hj]
      by_cases e : LBL (W s.1 s.2) = j
      · simp [e]
      · simp [e]
    · have hcn : (decide (s.1 < reps.size) && decide (s.2 < n) && A[s.1]! && A[labs[s.2]!]!) =
          false := by
        rw [Bool.eq_false_iff]
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rw [hreps] at h1
        obtain ⟨hl1, hl2⟩ := hlabs s.2 h2
        rw [hA2 _ h1] at h3
        rw [hl1, hA2 _ hl2] at h4
        exact hc ⟨h1, h2, h3, h4⟩
      rw [ite_eq_right (by rw [hcn]; decide), ite_eq_right hc]
      exact ⟨hA1, hA2⟩

theorem derivOK_of (hlabs : ∀ y < n, labs[y]! = LBL y ∧ LBL y < k) (hreps : reps.size = k)
    (hw : ∀ i < k, ∀ y < n, ap T.pos reps[i]! = KK i ∧ W i y < n ∧
      walkInv T letters (KK i) #[y] = #[W i y])
    (hF : ∀ b s, F b s = if s.1 < k ∧ s.2 < n ∧ b.testBit s.1 ∧ b.testBit (LBL s.2) then
      b ||| (1 <<< LBL (W s.1 s.2)) else b)
    {c : Nat} (hc : c < k) {steps : List (Nat × Nat)}
    (hd : steps.foldl F ((1 <<< 0) ||| (1 <<< c)) = 2 ^ k - 1) :
    derivOK n k T letters reps labs c steps = true := by
  have hk : 0 < k := by omega
  obtain ⟨-, h2⟩ := deriv_fold hlabs hreps hw hF steps
    (((Array.replicate k false).set! 0 true).set! c true) ((1 <<< 0) ||| (1 <<< c))
    ⟨by simp, fun j hj => by
      rw [set!_get' (by simp; omega), set!_get' (by simp; omega), testBit_or_shift,
        Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases e1 : c = j
      · simp [e1]
      · by_cases e0 : 0 = j
        · simp [e0]
        · rw [getElem!_pos _ j (by simp; omega)]
          simp [e0, e1]⟩
  unfold derivOK
  rw [allIn_iff]
  intro j hj
  rw [h2 j hj, hd, Nat.testBit_two_pow_sub_one]
  simp [hj]

end

theorem j3sub_core {NL k cnt0 : Nat} (D : Data) {letters : Array Table} {lv : Array Nat}
    {L : Nat → Nat → Nat} {B : Nat → Nat} {PTS0 POS0 PAR0 LAB0 LBL REP SCNT : Nat → Nat}
    {SPTS SPOS SPAR SLAB STI : Nat → Nat → Nat} {F : Nat → Nat × Nat → Nat}
    (hL : letters.size = NL ∧ ∀ l < NL, ∀ x < D.n, ap letters[l]! x = L l x ∧ L l x < D.n)
    (hlv : lv = (lvK L B NL 1).toArray)
    (hb : 0 < D.base.size ∧ D.base[0]! = 0)
    (hk : D.subReps.size = k ∧ 0 < k ∧ D.derivs.size = k ∧ ∀ l < k, D.subReps[l]! = REP l)
    (hr0 : REP 0 = 0 ∧ SCNT 0 = 1)
    (hT0 : ∀ l < k, r32 POS0 (REP l) < cnt0 ∧ r32 PTS0 (r32 POS0 (REP l)) = REP l)
    (hl0 : ∀ q < cnt0, 0 < q → invL (r32 LAB0 q) < NL)
    (hs : ∀ l < k, tbfsHdK D.n (REP l) (SCNT l) (SPTS l) (SPOS l) (SPAR l) (SLAB l) = true ∧
      ∀ q < SCNT l, tbfsPtK D.n (SCNT l) (lvK L B NL 1).length L (lvAt L B NL 1) (SPTS l) (SPOS l)
        (SPAR l) (SLAB l) (STI l) q = true)
    (hz : ∀ z < D.n, LBL z < k ∧ r32 (SPOS (LBL z)) z < SCNT (LBL z) ∧
      r32 (SPTS (LBL z)) (r32 (SPOS (LBL z)) z) = z)
    (hq : ∀ l < k, ∀ q < SCNT l, LBL (r32 (SPTS l) q) = l)
    (hF : ∀ b s, F b s = if s.1 < k ∧ s.2 < D.n ∧ b.testBit s.1 ∧ b.testBit (LBL s.2) then
      b ||| (1 <<< LBL ((walkInvK L PAR0 LAB0 (r32 POS0 (REP s.1)) [s.2]).getD 0 0)) else b)
    (hd : ∀ c, 1 ≤ c → c < k → D.derivs[c]!.foldl F ((1 <<< 0) ||| (1 <<< c)) = 2 ^ k - 1) :
    subChecks D letters lv (D.subReps.map fun r => treeBFS D.n r letters lv)
        (labelsOf D.n (D.subReps.map fun r => treeBFS D.n r letters lv)) = true ∧
      derivChecks D letters (tbfsRec D.n cnt0 PTS0 POS0 PAR0 LAB0)
        (labelsOf D.n (D.subReps.map fun r => treeBFS D.n r letters lv)) = true := by
  have hlvR : lv.size = (lvK L B NL 1).length ∧ ∀ t < (lvK L B NL 1).length,
      lv[t]! = lvAt L B NL 1 t ∧ lvAt L B NL 1 t < letters.size ∧
        ∀ x < D.n, ap letters[lvAt L B NL 1 t]! x = L (lvAt L B NL 1 t) x := by
    subst hlv
    refine ⟨by simp, fun t ht => ⟨?_, ?_, fun x hx => (hL.2 _ (mem_lvK.1 (lvAt_mem ht)).1 x hx).1⟩⟩
    · rw [getElem!_pos _ t (by simpa using ht)]
      simp [lvAt, List.getElem?_eq_getElem ht]
    · rw [hL.1]
      exact (mem_lvK.1 (lvAt_mem ht)).1
  have hR : ∀ j < k, Rep D.n (REP j) (SCNT j) (lvK L B NL 1).length L (lvAt L B NL 1) (SPTS j)
      (SPOS j) (SPAR j) (SLAB j) (STI j) :=
    fun j hj => ⟨hd_spec (hs j hj).1, fun q hq => pt_spec ((hs j hj).2 q hq)⟩
  have hT : ∀ j < k, treeBFS D.n (REP j) letters lv =
      tbfsRec D.n (SCNT j) (SPTS j) (SPOS j) (SPAR j) (SLAB j) ∧
      treeOK D.n (REP j) (tbfsRec D.n (SCNT j) (SPTS j) (SPOS j) (SPAR j) (SLAB j)) letters lv =
        true := fun j hj => tbfs_of_rep hlvR (hR j hj)
  have hrep : ∀ j < k, REP j < D.n := by
    intro j hj
    have := ((hR j hj).pt 0 (hR j hj).hd.cnt_pos).lt
    rwa [(hR j hj).hd.root] at this
  have hSs : (D.subReps.map fun r => treeBFS D.n r letters lv).size = k := by simp [hk.1]
  have hSj : ∀ j < k, (D.subReps.map fun r => treeBFS D.n r letters lv)[j]! =
      tbfsRec D.n (SCNT j) (SPTS j) (SPOS j) (SPAR j) (SLAB j) := by
    intro j hj
    rw [getElem!_pos _ j (by rw [hSs]; exact hj), Array.getElem_map,
      ← getElem!_pos D.subReps j (by omega), hk.2.2.2 j hj]
    exact (hT j hj).1
  generalize (D.subReps.map fun r => treeBFS D.n r letters lv) = S at hSs hSj ⊢
  have hlab := labelsOf_get (n := D.n) (S := S) (CNT := SCNT) (PT := fun j q => r32 (SPTS j) q)
    (LBL := LBL) hSs (fun j hj => by rw [hSj j hj]; simp [tbfsRec])
    (fun j hj q hq => by
      rw [hSj j hj]
      exact ⟨ap_ofFn hq, ((hR j hj).pt q hq).lt⟩) hq
    (fun z hz' => ⟨(hz z hz').1, _, (hz z hz').2.1, (hz z hz').2.2⟩)
  generalize labelsOf D.n S = labs at hlab ⊢
  obtain ⟨-, hlab⟩ := hlab
  refine ⟨?_, ?_⟩
  · unfold subChecks
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨hb.1, hb.2⟩, by rw [hk.1]; exact hk.2.1⟩, by rw [hk.2.2.2 0 hk.2.1, hr0.1]⟩,
      by rw [hSs, hk.1]⟩, by rw [hSj 0 hk.2.1]; simp [tbfsRec, hr0.2]⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hk.1, allIn_iff]
      intro j hj
      rw [hk.2.2.2 j hj, hSj j hj]
      exact (hT j hj).2
    · rw [allIn_iff]
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hz p hp
      rw [hlab p hp, hk.1, hSj _ h1]
      simp only [Bool.and_eq_true, decide_eq_true_eq, inTreeB, beq_iff_eq]
      rw [pos_ap hp, pts_ap h2, h3]
      simp [tbfsRec, h1, h2]
    · rw [hk.1, allIn_iff]
      intro j hj
      rw [hSj j hj, allIn_iff]
      intro t ht
      have ht' : t < SCNT j := by simpa [tbfsRec] using ht
      rw [pts_ap ht', hlab _ ((hR j hj).pt t ht').lt, hq j hj t ht']
      simp
  · unfold derivChecks
    rw [allIn_iff']
    intro c h1 h2
    rw [hk.1] at h2 ⊢
    refine derivOK_of (LBL := LBL) (KK := fun i => r32 POS0 (REP i))
      (W := fun i y => (walkInvK L PAR0 LAB0 (r32 POS0 (REP i)) [y]).getD 0 0)
      (fun y hy => ⟨hlab y hy, (hz y hy).1⟩) hk.1 (fun i hi y hy => ?_) hF h2 (hd c h1 h2)
    obtain ⟨w, hw, e1, e2⟩ := walkInv_one (n := D.n) (cnt := cnt0) (PTS := PTS0) (POS := POS0)
      hL.2 hl0 _ _ (hT0 i hi).1 (Nat.le_refl _) y hy
    have e3 : (walkInvK L PAR0 LAB0 (r32 POS0 (REP i)) [y]).getD 0 0 = w := by
      unfold walkInvK
      rw [e2]
      rfl
    rw [e3, hk.2.2.2 i hi]
    exact ⟨pos_ap (hrep i hi), hw, e1⟩

end CFSG.KS.J3Sub

end
