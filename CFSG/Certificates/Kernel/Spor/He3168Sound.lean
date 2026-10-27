module

public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.HeVOrb
public import Certificates.Data.Kernel.He3168K
public import Certificates.Data.CFSGNative.He.Certificate
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.HeSub

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.TBfs CFSG.Perm.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

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

theorem labelsOf_eq (S : Array Tree) :
    labelsOf S = (List.range' 0 S.size).foldl (fun labs j =>
      (List.range' 0 S[j]!.pts.size).foldl (fun labs k => labs.set! (ap S[j]!.pts k) j) labs)
      (Array.replicate 8330 0) := by
  unfold labelsOf
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl]

theorem labelsOf_get {k : Nat} {S : Array Tree} {CNT : Nat → Nat} {PT : Nat → Nat → Nat}
    {LBL : Nat → Nat} (hS : S.size = k) (hsz : ∀ j < k, S[j]!.pts.size = CNT j)
    (hpt : ∀ j < k, ∀ q < CNT j, ap S[j]!.pts q = PT j q ∧ PT j q < 8330)
    (hq : ∀ j < k, ∀ q < CNT j, LBL (PT j q) = j)
    (hz : ∀ z < 8330, LBL z < k ∧ ∃ q < CNT (LBL z), PT (LBL z) q = z) :
    (labelsOf S).size = 8330 ∧ ∀ p < 8330, (labelsOf S)[p]! = LBL p := by
  rw [labelsOf_eq, hS]
  have := fold_range'_ind (fun labs j =>
      (List.range' 0 S[j]!.pts.size).foldl (fun labs k => labs.set! (ap S[j]!.pts k) j) labs)
    (fun J (labs : Array Nat) => labs.size = 8330 ∧ ∀ p < 8330, LBL p < J → labs[p]! = LBL p) k
    (Array.replicate 8330 0) ⟨by simp, fun p _ h => absurd h (Nat.not_lt_zero _)⟩
    (fun J hJ labs hP => by
      rw [hsz J hJ]
      have := fold_range'_ind (fun labs k => labs.set! (ap S[J]!.pts k) J)
        (fun K (labs : Array Nat) => labs.size = 8330 ∧ ∀ p < 8330,
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

theorem subRoots_size : subRoots.size = 7 := rfl

theorem heSub_sound {NL : Nat} {letters : Array Table} {lv : Array Nat}
    {L : Nat → Nat → Nat} {B : Nat → Nat} {LBL SCNT : Nat → Nat}
    {SPTS SPOS SPAR SLAB STI : Nat → Nat → Nat}
    (hL : letters.size = NL ∧ ∀ l < NL, ∀ x < 8330, ap letters[l]! x = L l x ∧ L l x < 8330)
    (hlv : lv = (lvK L B NL 1).toArray)
    (hs : ∀ l < 7, tbfsHdK 8330 subRoots[l]! (SCNT l) (SPTS l) (SPOS l) (SPAR l) (SLAB l) = true ∧
      ∀ q < SCNT l, tbfsPtK 8330 (SCNT l) (lvK L B NL 1).length L (lvAt L B NL 1) (SPTS l) (SPOS l)
        (SPAR l) (SLAB l) (STI l) q = true)
    (hsz : (List.range 7).map SCNT = subSizes)
    (hz : ∀ z < 8330, LBL z < 7 ∧ r32 (SPOS (LBL z)) z < SCNT (LBL z) ∧
      r32 (SPTS (LBL z)) (r32 (SPOS (LBL z)) z) = z)
    (hq : ∀ l < 7, ∀ q < SCNT l, LBL (r32 (SPTS l) q) = l) :
    subChecks letters lv (subTrees letters lv) (labelsOf (subTrees letters lv)) = true ∧
      ∀ z < 8330, (labelsOf (subTrees letters lv))[z]! = LBL z := by
  have hlvR : lv.size = (lvK L B NL 1).length ∧ ∀ t < (lvK L B NL 1).length,
      lv[t]! = lvAt L B NL 1 t ∧ lvAt L B NL 1 t < letters.size ∧
        ∀ x < 8330, ap letters[lvAt L B NL 1 t]! x = L (lvAt L B NL 1 t) x := by
    subst hlv
    refine ⟨by simp, fun t ht => ⟨?_, ?_, fun x hx => (hL.2 _ (mem_lvK.1 (lvAt_mem ht)).1 x hx).1⟩⟩
    · rw [getElem!_pos _ t (by simpa using ht)]
      simp [lvAt, List.getElem?_eq_getElem ht]
    · rw [hL.1]
      exact (mem_lvK.1 (lvAt_mem ht)).1
  have hR : ∀ j < 7, Rep 8330 subRoots[j]! (SCNT j) (lvK L B NL 1).length L (lvAt L B NL 1)
      (SPTS j) (SPOS j) (SPAR j) (SLAB j) (STI j) :=
    fun j hj => ⟨hd_spec (hs j hj).1, fun q hq => pt_spec ((hs j hj).2 q hq)⟩
  have hT : ∀ j < 7, treeBFS 8330 subRoots[j]! letters lv =
      tbfsRec 8330 (SCNT j) (SPTS j) (SPOS j) (SPAR j) (SLAB j) ∧
      treeOK 8330 subRoots[j]! (tbfsRec 8330 (SCNT j) (SPTS j) (SPOS j) (SPAR j) (SLAB j))
        letters lv = true := fun j hj => tbfs_of_rep hlvR (hR j hj)
  have hSs : (subTrees letters lv).size = 7 := by simp [subTrees, subRoots_size]
  have hSj : ∀ j < 7, (subTrees letters lv)[j]! =
      tbfsRec 8330 (SCNT j) (SPTS j) (SPOS j) (SPAR j) (SLAB j) := by
    intro j hj
    unfold subTrees
    rw [getElem!_pos _ j (by simp [subRoots_size]; exact hj), Array.getElem_map,
      ← getElem!_pos subRoots j (by rw [subRoots_size]; exact hj)]
    exact (hT j hj).1
  have hsizes : (subTrees letters lv).toList.map (fun T => T.pts.size) = subSizes := by
    rw [← hsz]
    apply List.ext_getElem
    · simp [hSs]
    · intro i h1 h2
      have hi : i < 7 := by simpa [hSs] using h1
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      rw [← getElem!_pos (subTrees letters lv) i (by rw [hSs]; exact hi), hSj i hi]
      simp [tbfsRec]
  generalize (subTrees letters lv) = S at hSs hSj hsizes ⊢
  have hlab := labelsOf_get (S := S) (CNT := SCNT) (PT := fun j q => r32 (SPTS j) q)
    (LBL := LBL) hSs (fun j hj => by rw [hSj j hj]; simp [tbfsRec])
    (fun j hj q hq => by
      rw [hSj j hj]
      exact ⟨ap_ofFn hq, ((hR j hj).pt q hq).lt⟩) hq
    (fun z hz' => ⟨(hz z hz').1, _, (hz z hz').2.1, (hz z hz').2.2⟩)
  generalize labelsOf S = labs at hlab ⊢
  obtain ⟨-, hlab⟩ := hlab
  refine ⟨?_, hlab⟩
  unfold subChecks
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hSs, subRoots_size⟩, rfl⟩, ?_⟩, ?_⟩, hsizes⟩
  · rw [allIn_iff]
    intro j hj
    simp only [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [hSj j hj]
      exact (hT j hj).2
    · rw [allIn_iff]
      intro t ht
      rw [hSj j hj] at ht ⊢
      have ht' : t < SCNT j := by simpa [tbfsRec] using ht
      rw [pts_ap ht', hlab _ ((hR j hj).pt t ht').lt, hq j hj t ht']
      simp
  · rw [allIn_iff]
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hz p hp
    rw [hlab p hp, hSj _ h1]
    simp only [Bool.and_eq_true, decide_eq_true_eq, inTreeB, beq_iff_eq]
    rw [pos_ap hp, pts_ap h2, h3]
    simp [tbfsRec, h1, h2]

open CFSG.KS.SporSch.LyM CFSG.KS.HeVO in
theorem colsMat_eq {Q : Nat} {vs : Array (Array Nat)} {c : Nat → Nat}
    (hv : ∀ t < 50, vs[t]! = keyOf 50 12 (c t))
    (hcol : ∀ t < 50, CFSG.KC.He3168.colK Q t (c t) = true) :
    colsMat 50 vs = unpackL 50 12 600 Q := by
  unfold colsMat unpackL
  apply congrArg Array.ofFn
  funext i
  apply congrArg Array.ofFn
  funext t
  rw [hv t t.isLt]
  unfold keyOf
  rw [ofFn_get! _ i.isLt, land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change c t / 2 ^ (12 * i.val) % 2 ^ 12 = Q >>> (600 * i.val + 12 * t.val) % 2 ^ 12
  rw [Nat.shiftRight_eq_div_pow]
  have e := Nat.eq_of_beq_eq_true (allN_spec (hcol t t.isLt) i i.isLt)
  change (Q >>> (600 * i.val + 12 * t.val)) &&& (2 ^ 12 - 1) =
    (c t >>> (12 * i.val)) &&& (2 ^ 12 - 1) at e
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at e
  exact e.symm

end CFSG.KS.HeSub

end
