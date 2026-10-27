module

public import CFSG.Certificates.Kernel.He7222.StackSound
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.He7222.ChainSound

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KS.Raw.Orb CFSG.KS.PF

variable {n w : ℕ}

theorem stkIK_rep : ∀ {TIs : List (List ℕ)} {ix : List ℕ} (rec : ℕ → ℕ → Equiv.Perm (Fin n))
    {acc : List ℕ} {accg : List (Equiv.Perm (Fin n))}, ix.length = TIs.length →
    (∀ t < TIs.length, PRep n w ((TIs.getD t []).getD (ix.getD t 0) 0) (rec t (ix.getD t 0))) →
    StkRep n w acc accg →
    StkRep n w (stkIK TIs ix acc) ((tupL rec TIs.length ix).reverse ++ accg)
  | [], [], _, _, _, _, _, ha => by
    change StkRep n w _ _
    simpa [tupL, stkIK] using ha
  | [], _ :: _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, _, hl, _, _ => absurd hl (by simp)
  | TI :: TIs, j :: ix, rec, acc, accg, hl, hr, ha => by
    have e : stkIK (TI :: TIs) (j :: ix) acc = stkIK TIs ix (getS TI j :: acc) := rfl
    have ha' : StkRep n w (getS TI j :: acc) (rec 0 j :: accg) := by
      rw [StkRep, List.forall₂_cons]
      refine ⟨?_, ha⟩
      rw [getS_eq]
      exact hr 0 (by simp)
    rw [e, List.length_cons, tupL_succ, List.reverse_cons, List.append_assoc]
    exact stkIK_rep (fun t => rec (t + 1)) (by simpa using hl)
      (fun t ht => hr (t + 1) (by simpa using ht)) ha'

theorem clsW_sound {w m : ℕ} {Ts TIs : List (List ℕ)} {rs : List ℕ} {KC : List (List ℕ)}
    {keys : List ℕ} : ∀ (L : List (List ℕ)) (pos : ℕ), L = KC.drop pos → pos ≤ KC.length →
    List.rec (motive := fun _ => Nat → Bool) (fun pos => Nat.beq pos (lenS keys))
      (fun ix _ ih pos => bAnd(tupOK Ts ix,
        bAnd(Nat.beq (keyF w (cjEv w m (stkK Ts ix) rs (stkIK TIs ix List.nil)) (nat_lit 5))
          (getS keys pos), strictB (Nat.succ pos) ih))) L pos = true →
    KC.length = keys.length ∧ ∀ i, pos ≤ i → i < KC.length →
      tupOK Ts (KC.getD i []) = true ∧
      keyF w (cjEv w m (stkK Ts (KC.getD i [])) rs (stkIK TIs (KC.getD i []) [])) 5 =
        keys.getD i 0 := by
  intro L
  induction L with
  | nil =>
    intro pos hL hp h
    have hK : KC.length ≤ pos := List.drop_eq_nil_iff.mp hL.symm
    have h' : Nat.beq pos (lenS keys) = true := h
    rw [lenS_eq] at h'
    have := Nat.eq_of_beq_eq_true h'
    exact ⟨by omega, fun i hi hi' => absurd hi' (by omega)⟩
  | cons ix L ih =>
    intro pos hL hp h
    have hpK : pos < KC.length := by
      rcases Nat.lt_or_ge pos KC.length with h1 | h1
      · exact h1
      · have : KC.drop pos = [] := List.drop_eq_nil_iff.mpr h1
        rw [this] at hL
        exact absurd hL (List.cons_ne_nil _ _)
    have hix : KC.getD pos [] = ix := by
      rw [List.getD_eq_getElem _ _ hpK]
      have := congrArg List.head? hL
      rw [List.head?_cons, List.head?_drop, List.getElem?_eq_getElem hpK] at this
      exact (Option.some.inj this).symm
    have hL' : L = KC.drop (pos + 1) := by
      have := congrArg List.tail hL
      rw [List.tail_cons, List.tail_drop] at this
      exact this
    have h' : bAnd(tupOK Ts ix,
        bAnd(Nat.beq (keyF w (cjEv w m (stkK Ts ix) rs (stkIK TIs ix List.nil)) (nat_lit 5))
          (getS keys pos), strictB (Nat.succ pos) (List.rec (motive := fun _ => Nat → Bool)
            (fun pos => Nat.beq pos (lenS keys))
            (fun ix _ ih pos => bAnd(tupOK Ts ix,
              bAnd(Nat.beq (keyF w (cjEv w m (stkK Ts ix) rs (stkIK TIs ix List.nil)) (nat_lit 5))
                (getS keys pos), strictB (Nat.succ pos) ih))) L))) = true := h
    rw [bAnd_iff, bAnd_iff, strictB_eqP] at h'
    obtain ⟨ht, hk, hrest⟩ := h'
    obtain ⟨hlen, hall⟩ := ih (pos + 1) hL' hpK hrest
    refine ⟨hlen, fun i hi hiK => ?_⟩
    rcases Nat.lt_or_ge pos i with hpi | hpi
    · exact hall i hpi hiK
    have : i = pos := by omega
    subst this
    rw [hix]
    refine ⟨ht, ?_⟩
    rw [Nat.eq_of_beq_eq_true hk, getS_eq]

theorem clsK_sound {w m : ℕ} {Ts TIs : List (List ℕ)} {rs : List ℕ} {KC : List (List ℕ)}
    {keys : List ℕ} (h : clsK w m Ts TIs rs KC keys = true) :
    KC.length = keys.length ∧ ∀ i < KC.length,
      tupOK Ts (KC.getD i []) = true ∧
      keyF w (cjEv w m (stkK Ts (KC.getD i [])) rs (stkIK TIs (KC.getD i []) [])) 5 =
        keys.getD i 0 := by
  obtain ⟨h1, h2⟩ := clsW_sound KC 0 rfl (Nat.zero_le _) h
  exact ⟨h1, fun i hi => h2 i (Nat.zero_le _) hi⟩

theorem svW_sound {w m : ℕ} {Ts TIs : List (List ℕ)} {rs : List ℕ} {h hI tau : ℕ}
    {KC : List (List ℕ)} {Sv : List ℕ} : ∀ (L : List (List ℕ)) (pos : ℕ) (sv : List ℕ),
    L = KC.drop pos → (∀ x ∈ sv, x ∈ Sv) →
    List.rec (motive := fun _ => Nat → List Nat → Bool)
      (fun _ sv => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) sv)
      (fun ix _ ih pos sv => strictB (Nat.succ pos) (fun pos' =>
        List.rec (motive := fun _ => Bool)
          (bIf(cmK w m (stkK Ts ix) rs (stkIK TIs ix List.nil) h hI tau, false, ih pos' sv))
          (fun q rest _ => bIf(Nat.beq q pos, ih pos' rest,
            bIf(cmK w m (stkK Ts ix) rs (stkIK TIs ix List.nil) h hI tau, false, ih pos' sv)))
          sv)) L pos sv = true →
    ∀ i, pos ≤ i → i < KC.length →
      cmK w m (stkK Ts (KC.getD i [])) rs (stkIK TIs (KC.getD i []) []) h hI tau = true →
      i ∈ Sv := by
  intro L
  induction L with
  | nil =>
    intro pos sv hL _ _ i hi hiK
    have hK : KC.length ≤ pos := List.drop_eq_nil_iff.mp hL.symm
    exact absurd hiK (by omega)
  | cons ix L ih =>
    intro pos sv hL hsv hw i hi hiK hcm
    have hpK : pos < KC.length := by
      rcases Nat.lt_or_ge pos KC.length with h1 | h1
      · exact h1
      · have : KC.drop pos = [] := List.drop_eq_nil_iff.mpr h1
        rw [this] at hL
        exact absurd hL (List.cons_ne_nil _ _)
    have hix : KC.getD pos [] = ix := by
      rw [List.getD_eq_getElem _ _ hpK]
      have := congrArg List.head? hL
      rw [List.head?_cons, List.head?_drop, List.getElem?_eq_getElem hpK] at this
      exact (Option.some.inj this).symm
    have hL' : L = KC.drop (pos + 1) := by
      have := congrArg List.tail hL
      rw [List.tail_cons, List.tail_drop] at this
      exact this
    dsimp only at hw
    rw [strictB_eqP (Nat.succ pos)] at hw
    cases sv with
    | nil =>
      rw [bIf_iff] at hw
      rcases hw with ⟨hc, hf⟩ | ⟨hc, hrest⟩
      · exact absurd hf (by simp)
      · rcases Nat.lt_or_ge pos i with hpi | hpi
        · exact ih (pos + 1) [] hL' hsv hrest i hpi hiK hcm
        · have : i = pos := by omega
          subst this
          rw [hix, hc] at hcm
          exact absurd hcm (by simp)
    | cons q rest =>
      rw [bIf_iff] at hw
      rcases hw with ⟨hq, hrest⟩ | ⟨hq, hw'⟩
      · rcases Nat.lt_or_ge pos i with hpi | hpi
        · exact ih (pos + 1) rest hL' (fun x hx => hsv x (List.mem_cons_of_mem _ hx)) hrest i hpi
            hiK hcm
        · have : i = pos := by omega
          subst this
          rw [← Nat.eq_of_beq_eq_true hq]
          exact hsv q List.mem_cons_self
      · rw [bIf_iff] at hw'
        rcases hw' with ⟨hc, hf⟩ | ⟨hc, hrest⟩
        · exact absurd hf (by simp)
        · rcases Nat.lt_or_ge pos i with hpi | hpi
          · exact ih (pos + 1) (q :: rest) hL' hsv hrest i hpi hiK hcm
          · have : i = pos := by omega
            subst this
            rw [hix, hc] at hcm
            exact absurd hcm (by simp)

theorem svK_sound {w m : ℕ} {Ts TIs : List (List ℕ)} {rs : List ℕ} {h hI tau : ℕ}
    {KC : List (List ℕ)} {Sv : List ℕ} (hs : svK w m Ts TIs rs h hI tau KC Sv = true) :
    ∀ i < KC.length,
      cmK w m (stkK Ts (KC.getD i [])) rs (stkIK TIs (KC.getD i []) []) h hI tau = true →
      i ∈ Sv := fun i hi =>
  svW_sound KC 0 Sv rfl (fun _ hx => hx) hs i (Nat.zero_le _) hi

end CFSG.KC.HeChain

end
