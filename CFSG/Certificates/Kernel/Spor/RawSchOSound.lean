module

public import CFSG.Certificates.Kernel.Spor.RawSch4OSound
import all CFSG.Certificates.Kernel.Spor.RawSch3GSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native

theorem gens_mem_of {n w kS kO nb BP : Nat} {S SI : Nat → Nat} {D : List (List Int)}
    {M : Submonoid (Equiv.Perm (Fin n))}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO D nb BP = true)
    (hinv : ∀ g ∈ M, g⁻¹ ∈ M) (hO : ∀ j < kO, pp n w (S j) ∈ M) :
    ∀ j < kS, pp n w (S j) ∈ M := by
  unfold headK at hh
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨hsz, _, _, _, hperm, hder, _, _⟩ := hh
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjk : j < kO
    · exact hO j hjk
    · have := allN_iff.1 hder j hj
      rw [bIf_eq, ite_eq_right (by rw [blt_dec]; simpa using hjk), strictB_eq, Bool.and_eq_true,
        beq_dec, decide_eq_true_iff] at this
      obtain ⟨hl, he⟩ := this
      obtain ⟨g, hg, hgm⟩ := wordK_mem hn24 hw (j := j) (M := M)
        (fun h hh' => ⟨pp n w (S h), (prep_pp (allN_iff.1 hperm h (by omega))).1,
          (prep_pp (allN_iff.1 hperm h (by omega))).2, ih h hh' (by omega)⟩) hinv _ hl
      have hSj : PRep n w (wordK n w (mask w) (pidn n w) S SI (dword D kO j)) (pp n w (S j)) := by
        rw [← he]
        exact (prep_pp (allN_iff.1 hperm j hj)).1
      rw [prep_unique hSj hg]
      exact hgm

theorem gens_mem_wds {n w kS kO nb BP TJ TS : Nat} {S SI : Nat → Nat} {D : List (List Int)}
    {WS : List (List Nat)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO D nb BP = true)
    (hW : wdsK n w (mask w) (pidn n w) S SI kO TJ WS 0 = true) (hJ : incK TJ TS = true) :
    ∀ j < kS, pp n w (S j) ∈ Submonoid.closure (LT n w S kS TS) := by
  have hh' := hh
  unfold headK at hh'
  simp only [bAnd_eq, Bool.and_eq_true] at hh'
  obtain ⟨hsz, _, hko, _, hperm, _, _, _⟩ := hh'
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hko' : kO ≤ kS := Nat.le_of_ble_eq_true hko
  have hpO : allN kO (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true :=
    allN_iff.2 fun j hj => allN_iff.1 hperm j (by omega)
  have hsub : LJ n w S kO TJ ⊆ LT n w S kS TS := by
    rintro g ⟨a, ha, hak, rfl⟩
    have ha' : a < stCnt TJ := by
      rw [shr_eq] at ha
      exact Nat.lt_of_lt_of_le ha (Nat.div_le_self _ _)
    have e : lp n w S kO (stAt TJ a) = lp n w S kS (stAt TJ a) := by
      unfold lp
      rw [if_pos hak, if_pos (by omega)]
    rw [e]
    exact inc_sub (n := n) (w := w) (kS := kS) (S := S) hJ ⟨a, ha', rfl⟩
  have hWm := wds_facts hn24 hw hpO WS 0 hW
  exact gens_mem_of hh (fun g hg => inv_mem_closure hg)
    (fun j hj => Submonoid.closure_mono hsub (hWm j (Nat.zero_le _) hj))

theorem lv12K_facts {w kS BP l T1 T2 : Nat} {S SI : Nat → Nat}
    (h : lv12K w (mask w) S SI kS BP l T1 T2 = true) :
    invTabK kS T1 = true ∧ invTabK kS T2 = true ∧ fixK w (mask w) S SI kS T1 (pg w (mask w) BP l) = true ∧
      fixK w (mask w) S SI kS T2 (pg w (mask w) BP (l + 1)) = true ∧ incK T2 T1 = true := by
  unfold lv12K at h
  simp only [bAnd_iff, Nat.succ_eq_add_one] at h
  exact h

set_option maxHeartbeats 1000000 in
theorem schK_of_schOL {n w kS BP E i TS NSi CH : Nat} {S SI LR TR TRI : Nat → Nat}
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hl : LevelsOK n w S SI LR TR TRI kS E BP) (hE : i + 3 ≤ E)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hlv : ∀ k < E - i - 2, lv12K w (mask w) S SI kS BP (i + k) (stepsAt n w S kS BP (i + k + 1))
      (stepsAt n w S kS BP (i + k + 1 + 1)) = true)
    (hTS : ∀ a < stCnt TS, stAt TS a < kS + kS)
    (hgm : ∀ j < kS, pp n w (S j) ∈ Submonoid.closure (LT n w S kS TS))
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i TS
      (s * CH) CH = true)
    (hsl : ∀ k < E - i - 1, ∃ N, rcnt (LR (i + 1 + k)) ≤ N * CH ∧ ∀ s < N,
      schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E (i + 1 + k)
        (stepsAt n w S kS BP (i + 1 + k)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  obtain ⟨hsz, -, hR0, -, -, hp0⟩ := levelK_facts (hl i (by omega))
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hP : ∀ l < E, ∀ k < rcnt (LR l), permOK n w (mask w) (n * w)
      (TR (roff n (n * w) (LR l) + k)) (TRI (roff n (n * w) (LR l) + k)) = true :=
    fun l hl' => (levelK_facts (hl l hl')).2.2.2.2.2
  have hb : ∀ l < E, pg w (mask w) BP l < n := fun l hl' => by
    obtain ⟨-, -, hR, -, -, -⟩ := levelK_facts (hl l hl')
    rw [← hR.root]
    exact (hR.pt 0 hR.c_pos).1
  have hq : ∀ l < E, ∀ a < rcnt (LR l),
      rpos w (mask w) (n * w) (LR l) (rpt w (mask w) (LR l) a) = a := fun l hl' a ha => by
    obtain ⟨-, -, hR, -, -, -⟩ := levelK_facts (hl l hl')
    exact (hR.pt a ha).2
  have hlv' : ∀ l, i ≤ l → l + 3 ≤ E → lv12K w (mask w) S SI kS BP l
      (stepsAt n w S kS BP (l + 1)) (stepsAt n w S kS BP (l + 1 + 1)) = true := fun l h1 h2 => by
    have := hlv (l - i) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  have hinvL : ∀ l, i < l → l < E → invTabK kS (stepsAt n w S kS BP l) = true := fun l h1 h2 => by
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact (lv12K_facts (hlv' i le_rfl hE)).1
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 + 1 := ⟨l - 2, by omega⟩
      exact (lv12K_facts (hlv' m (by omega) (by omega))).2.1
  have hTl : ∀ l, i < l → l < E → ∀ j < stCnt (stepsAt n w S kS BP l),
      stAt (stepsAt n w S kS BP l) j < kS + kS := fun l h1 h2 => letter_lt (hinvL l h1 h2)
  have hfixL : ∀ l, i ≤ l → l + 1 < E →
      fixK w (mask w) S SI kS (stepsAt n w S kS BP (l + 1)) (pg w (mask w) BP l) = true := by
    intro l h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact (lv12K_facts (hlv' i le_rfl hE)).2.2.1
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      exact (lv12K_facts (hlv' m (by omega) (by omega))).2.2.2.1
  have hincL : ∀ l, i < l → l + 1 < E →
      LT n w S kS (stepsAt n w S kS BP (l + 1)) ⊆ LT n w S kS (stepsAt n w S kS BP l) := by
    intro l h1 h2
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact inc_sub (lv12K_facts (hlv' m (by omega) (by omega))).2.2.2.2
  have FL : ∀ l, i < l → l < E → ∀ k < rcnt (LR l),
      tp n w TR (LR l) k ∈ Submonoid.closure (LT n w S kS (stepsAt n w S kS BP l)) ∧
      ∀ hr : pg w (mask w) BP l < n, ((tp n w TR (LR l) k) ⟨_, hr⟩ : Nat) =
        rpt w (mask w) (LR l) k := fun l h1 h2 => tree_facts hp (hl l h2) (hTl l h1 h2)
  have hA : ∀ l d, i < l → l + 1 + d = E → ∀ σ ∈ LT n w S kS (stepsAt n w S kS BP l),
      ∀ a < rcnt (LR l), ∃ a' < rcnt (LR l), ∃ v ∈ PS n w TR LR (l + 1) d,
        σ * tp n w TR (LR l) a = tp n w TR (LR l) a' * v := by
    intro l d h1 h2
    obtain ⟨N, hcN, hsN⟩ := hsl (l - (i + 1)) (by omega)
    rw [Nat.add_sub_cancel' (by omega : i + 1 ≤ l)] at hcN hsN
    exact step_of_schK hn24 hw hp (hTl l h1 (by omega)) hP h2 hcN hsN
  have hC : ∀ m l, i < l → l + (m + 1) = E →
      (∀ g ∈ Submonoid.closure (LT n w S kS (stepsAt n w S kS BP l)),
        ∀ u ∈ PS n w TR LR l (m + 1), g * u ∈ PS n w TR LR l (m + 1)) ∧
      PS n w TR LR l (m + 1) ⊆ Submonoid.closure (LT n w S kS (stepsAt n w S kS BP l)) := by
    intro m
    induction m with
    | zero =>
      intro l h1 h2
      exact mulW one_W one_Wm (hA l 0 h1 h2) (fun a ha => (FL l h1 (by omega) a ha).1)
        (Set.empty_subset _)
    | succ m ih =>
      intro l h1 h2
      obtain ⟨C1, C2⟩ := ih (l + 1) (by omega) (by omega)
      exact mulW C1 C2 (hA l (m + 1) h1 (by omega)) (fun a ha => (FL l h1 (by omega) a ha).1)
        (hincL l h1 (by omega))
  have hone : ∀ m l, i < l → l + m = E → (1 : Equiv.Perm (Fin n)) ∈ PS n w TR LR l m := by
    intro m
    induction m with
    | zero => intro l _ _; exact Set.mem_singleton 1
    | succ m ih =>
      intro l h1 h2
      have hRc := (levelK_facts (hl l (by omega))).2.2.1.c_pos
      exact mem_TW.2 ⟨0, hRc, 1, ih (l + 1) (by omega) (by omega),
        by rw [tp_zero (hl l (by omega)), one_mul]⟩
  obtain ⟨D, rfl⟩ : ∃ D, E = i + 1 + (D + 1 + 1) := ⟨E - i - 3, by omega⟩
  obtain ⟨C1a, C1b⟩ := hC (D + 1) (i + 1) (by omega) rfl
  have hUU : ∀ u ∈ PS n w TR LR (i + 1) (D + 1 + 1), ∀ v ∈ PS n w TR LR (i + 1) (D + 1 + 1),
      u * v ∈ PS n w TR LR (i + 1) (D + 1 + 1) := fun u hu v hv => C1a u (C1b hu) v hv
  have hTSb := hTS
  have hD := step_of_schK (d := D + 1 + 1) hn24 hw hp hTSb hP rfl hc hs
  have hT0 := letter_lt hinv
  have F0 := tree_facts hp (hl i (by omega)) hT0
  have hmem : ∀ j < stCnt (stepsAt n w S kS BP i),
      lp n w S kS (stAt (stepsAt n w S kS BP i) j) ∈ Submonoid.closure (LT n w S kS TS) := by
    intro j hj
    have hj' := hT0 j hj
    unfold lp
    split_ifs with hl'
    · exact hgm _ hl'
    · exact inv_mem_closure (hgm _ (by omega))
  have hfix : ∀ l d, i + 1 ≤ l → l + (d + 1) = i + 1 + (D + 1 + 1) →
      ∀ v ∈ PS n w TR LR (l + 1) d, ∀ x : Fin n, (x : Nat) = pg w (mask w) BP l → v x = x := by
    intro l d hlo hld v hv x hx
    obtain ⟨xv, hxv⟩ := x
    simp only at hx
    subst hx
    rcases d with _ | m
    · rw [PS_zero, Set.mem_singleton_iff] at hv
      rw [hv]
      rfl
    · exact fix_of_closure (fix_LT hp (hTl (l + 1) (by omega) (by omega))
        (hfixL l (by omega) (by omega)) hxv) ((hC m (l + 1) (by omega) (by omega)).2 hv)
  have ht : ∀ l, i + 1 ≤ l → l < i + 1 + (D + 1 + 1) → ∀ a < rcnt (LR l),
      ∀ hr : pg w (mask w) BP l < n,
      ((tp n w TR (LR l) a) ⟨_, hr⟩ : Nat) = rpt w (mask w) (LR l) a :=
    fun l hlo hl' a ha hr => (FL l (by omega) hl' a ha).2 hr
  have hb0 := hb i (by omega)
  have fx1 := fix_LT hp (hTl (i + 1) (by omega) (by omega)) (hfixL i le_rfl (by omega)) hb0
  have e2 : Nat.sub (i + 1 + (D + 1 + 1)) (Nat.succ i) = D + 1 + 1 := by
    simp only [Nat.sub_eq, Nat.succ_eq_add_one]
    omega
  unfold schK
  rw [e2]
  simp only [strictB_eq, allN_iff, bIf_eq, Nat.blt_eq, Nat.add_eq, Nat.succ_eq_add_one]
  intro dh _
  split
  case isFalse => rfl
  rename_i hc'
  rw [allN_iff]
  intro j hj
  have hσ := prep_lp hp (hT0 j hj)
  obtain ⟨k', hk', u, hu, e⟩ := mulCS hUU hD (hone (D + 1 + 1) (i + 1) (by omega) rfl)
    (hmem j hj) (h₀ + dh) hc'
  have fu : u ⟨_, hb0⟩ = ⟨_, hb0⟩ := fix_of_closure fx1 (C1b hu)
  have ept : pg w (mask w) (letterK S SI kS (stAt (stepsAt n w S kS BP i) j))
      (rpt w (mask w) (LR i) (h₀ + dh)) = rpt w (mask w) (LR i) k' := by
    rw [← (F0 _ hc').2 hb0, hσ, ← Equiv.Perm.mul_apply, e, Equiv.Perm.mul_apply, fu,
      (F0 k' hk').2 hb0]
  have ek : rpos w (mask w) (n * w) (LR i) (pg w (mask w)
      (letterK S SI kS (stAt (stepsAt n w S kS BP i) j)) (rpt w (mask w) (LR i) (h₀ + dh))) = k' := by
    rw [ept]
    exact (hR0.pt k' hk').2
  rw [ek, if_pos hk']
  have hPG : PRep n w _ ((tp n w TR (LR i) k')⁻¹ *
      (lp n w S kS (stAt (stepsAt n w S kS BP i) j) * tp n w TR (LR i) (h₀ + dh))) :=
    prep_pcomp hn (prep_pp (hp0 _ hk')).2 (prep_pcomp hn hσ (prep_pp (hp0 _ hc')).1)
  rw [e, inv_mul_cancel_left] at hPG
  exact sift_of_mem_PS hsz hP hb ht hq hfix (D + 1 + 1) (i + 1) le_rfl (by omega) _ u hPG
    (PF.pcomp_shr _ _ hn (PF.w_pos hw)) hu

theorem schK_of_schOL_orig {n w kS kO BP E i TS NSi CH : Nat} {S SI LR TR TRI : Nat → Nat}
    {W : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W E BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS E BP) (hE : i + 3 ≤ E)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hlv : ∀ k < E - i - 2, lv12K w (mask w) S SI kS BP (i + k) (stepsAt n w S kS BP (i + k + 1))
      (stepsAt n w S kS BP (i + k + 1 + 1)) = true)
    (hTS : allN (stCnt TS) (fun a => Nat.blt (stAt TS a) kS) = true)
    (hTO : allN kO (fun j => anyLt (stCnt TS) (fun a => Nat.beq (stAt TS a) j)) = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i TS
      (s * CH) CH = true)
    (hsl : ∀ k < E - i - 1, ∃ N, rcnt (LR (i + 1 + k)) ≤ N * CH ∧ ∀ s < N,
      schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E (i + 1 + k)
        (stepsAt n w S kS BP (i + 1 + k)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i
      (stepsAt n w S kS BP i) h₀ cnt = true :=
  schK_of_schOL (head_facts hh).1 hl hE hinv hlv
    (fun a ha => by have := Nat.blt_eq.mp (allN_iff.1 hTS a ha); omega)
    (gens_mem hh hTO) hc hs hsl h₀ cnt

theorem schK_of_schOL_wds {n w kS kO BP E i TS TJ NSi CH : Nat} {S SI LR TR TRI : Nat → Nat}
    {W : List (List Int)} {WS : List (List Nat)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W E BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS E BP) (hE : i + 3 ≤ E)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (hlv : ∀ k < E - i - 2, lv12K w (mask w) S SI kS BP (i + k) (stepsAt n w S kS BP (i + k + 1))
      (stepsAt n w S kS BP (i + k + 1 + 1)) = true)
    (hTS : allN (stCnt TS) (fun a => Nat.blt (stAt TS a) kS) = true)
    (hW : wdsK n w (mask w) (pidn n w) S SI kO TJ WS 0 = true) (hJ : incK TJ TS = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i TS
      (s * CH) CH = true)
    (hsl : ∀ k < E - i - 1, ∃ N, rcnt (LR (i + 1 + k)) ≤ N * CH ∧ ∀ s < N,
      schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E (i + 1 + k)
        (stepsAt n w S kS BP (i + 1 + k)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP E i
      (stepsAt n w S kS BP i) h₀ cnt = true :=
  schK_of_schOL (head_facts hh).1 hl hE hinv hlv
    (fun a ha => by have := Nat.blt_eq.mp (allN_iff.1 hTS a ha); omega)
    (gens_mem_wds hh hW hJ) hc hs hsl h₀ cnt

theorem schK_of_sch4OL {n w kS kO BP i TS NSi N1 N2 N3 CH : Nat} {S SI LR TR TRI : Nat → Nat}
    {W : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 4) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 4) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (h12 : lv12K w (mask w) S SI kS BP i (stepsAt n w S kS BP (i + 1))
      (stepsAt n w S kS BP (i + 1 + 1)) = true)
    (h23 : lv12K w (mask w) S SI kS BP (i + 1) (stepsAt n w S kS BP (i + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1)) = true)
    (hTS : allN (stCnt TS) (fun a => Nat.blt (stAt TS a) kS) = true)
    (hTO : allN kO (fun j => anyLt (stCnt TS) (fun a => Nat.beq (stAt TS a) j)) = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) i TS
      (s * CH) CH = true)
    (hc1 : rcnt (LR (i + 1)) ≤ N1 * CH)
    (hs1 : ∀ s < N1, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) (i + 1)
      (stepsAt n w S kS BP (i + 1)) (s * CH) CH = true)
    (hc2 : rcnt (LR (i + 1 + 1)) ≤ N2 * CH)
    (hs2 : ∀ s < N2, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4)
      (i + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1)) (s * CH) CH = true)
    (hc3 : rcnt (LR (i + 1 + 1 + 1)) ≤ N3 * CH)
    (hs3 : ∀ s < N3, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4)
      (i + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 4) i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  refine schK_of_schOL_orig hh hl (by omega) hinv (fun k hk => ?_) hTS hTO hc hs
    (fun k hk => ?_) h₀ cnt
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact h12
    · exact h23
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact ⟨N1, hc1, hs1⟩
    · exact ⟨N2, hc2, hs2⟩
    · exact ⟨N3, hc3, hs3⟩

end CFSG.KS.Raw.Orb

end
