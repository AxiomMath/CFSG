module

public import Certificates.Data.Kernel.T75M23.P7K
public import CFSG.Certificates.Kernel.T75M23.N7KSound

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable
open CFSG.CGT.T75JM (V3 glAct FinCheck evalWord3 affPerm8 translate8 vecIdx idxVec)

theorem iteN (f : Nat → Nat) (c i : Nat) (r : Nat) :
    (if i = c then f c else r) = if i = c then f i else r := by
  by_cases h : i = c
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h]

theorem with8_eq (f : Nat → Nat) (k : (Nat → Nat) → Bool) : with8 f k = k f := by
  unfold with8
  simp only [sB_eq]
  refine congrArg k (funext fun i => ?_)
  simp only [iteN f, ite_self]

variable {L : Int → Nat}

theorem ap_pw (hL : LetterRd L) (w : List (Fin 6 × Bool)) {x : Nat} (hx : x < 23) :
    ap (n7Tab w) x = fd 5 (pw L w) x :=
  (fd_wordK_lt hL (lw w) hx).1

theorem fd_pw_lt (hL : LetterRd L) (w : List (Fin 6 × Bool)) {x : Nat} (hx : x < 23) :
    fd 5 (pw L w) x < 23 :=
  (fd_wordK_lt hL (lw w) hx).2

theorem size_n7Tab (hL : LetterRd L) (w : List (Fin 6 × Bool)) : (n7Tab w).size = 23 :=
  (wordT_fd (by norm_num) hid hL (lw w)).1

theorem fd_pc (A B : Nat) {x : Nat} (hx : x < 23) : fd 5 (pc A B) x = fd 5 A (fd 5 B x) :=
  fd_pcomp (by norm_num) 5 A B hx

theorem lw_append (u v : List (Fin 6 × Bool)) : lw (u ++ v) = lw u ++ lw v := by
  simp [lw, liftWord7]

theorem fd_pw_append (hL : LetterRd L) (u v : List (Fin 6 × Bool)) {x : Nat} (hx : x < 23) :
    fd 5 (pw L (u ++ v)) x = fd 5 (pw L u) (fd 5 (pw L v) x) := by
  have hy := fd_pw_lt hL v hx
  unfold pw at hy ⊢
  rw [fd_wordK (by norm_num) hid L (lw (u ++ v)) hx, lw_append, List.foldr_append,
    ← fd_wordK (by norm_num) hid L (lw v) hx, ← fd_wordK (by norm_num) hid L (lw u) hy]

theorem tabEq_of_fd (hL : LetterRd L) {w w' : List (Fin 6 × Bool)}
    (h : ∀ x < 23, fd 5 (pw L w) x = fd 5 (pw L w') x) : tabEq7 w w' = true := by
  unfold tabEq7
  refine beq_of_ap (size_n7Tab hL w) (size_n7Tab hL w') fun x hx => ?_
  rw [ap_pw hL w hx, ap_pw hL w' hx]
  exact h x hx

theorem fd_of_tabEq (hL : LetterRd L) {w w' : List (Fin 6 × Bool)} (h : tabEq7 w w' = true)
    {x : Nat} (hx : x < 23) : fd 5 (pw L w) x = fd 5 (pw L w') x := by
  unfold tabEq7 at h
  rw [← ap_pw hL w hx, ← ap_pw hL w' hx, beq_iff_eq.1 h]

theorem tabEq_of_beq (hL : LetterRd L) {w w' : List (Fin 6 × Bool)}
    (h : Nat.beq (pw L w) (pw L w') = true) : tabEq7 w w' = true :=
  tabEq_of_fd hL fun _ _ => by rw [Nat.eq_of_beq_eq_true h]

theorem tabEq_mul (hL : LetterRd L) {u v r : List (Fin 6 × Bool)}
    (h : Nat.beq (pc (pw L u) (pw L v)) (pw L r) = true) : tabEq7 (u ++ v) r = true :=
  tabEq_of_fd hL fun x hx => by
    rw [← Nat.eq_of_beq_eq_true h, fd_pc _ _ hx, fd_pw_append hL _ _ hx]

theorem tabEq_conj (hL : LetterRd L) {u e r : List (Fin 6 × Bool)}
    (h : Nat.beq (pc (pc (pw L u) (pw L e)) (pw L (invWord7 u))) (pw L r) = true) :
    tabEq7 (u ++ e ++ invWord7 u) r = true :=
  tabEq_of_fd hL fun x hx => by
    have hy := fd_pw_lt hL (invWord7 u) hx
    rw [← Nat.eq_of_beq_eq_true h, fd_pc _ _ hx, fd_pc _ _ hy, fd_pw_append hL _ _ hx,
      fd_pw_append hL _ _ hy]

theorem idx37_lt : ∀ c : V3, idx37 c < 8 := by decide

theorem idx37_inj : ∀ c d : V3, idx37 c = idx37 d → c = d := by decide

theorem idx37_single2 : idx37 (Pi.single (2 : Fin 3) (1 : ZMod 2)) = 4 := by decide

theorem pChecks_of (hL : LetterRd L) (h : pOkK L = true) :
    eMulCheck7 = true ∧ eInjCheck7 = true ∧ eTorsCheck7 = true ∧ actVCheck7 = true ∧
      actGCheck7 = true ∧ thetaCheck7 = true ∧ d0Check7 = true ∧ d8Check7 = true := by
  unfold pOkK at h
  rw [withL_eq, with8_eq] at h
  unfold pOkE at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h8'⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  unfold eMulK at h1
  unfold conjK at h4 h5 h12 h13
  unfold actGK at h6
  have hE4 : eW7 (Pi.single (2 : Fin 3) (1 : ZMod 2)) = eWtab7.getD 4 [] := by
    unfold eW7
    rw [idx37_single2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold eMulCheck7
    exact decide_eq_true fun c d => tabEq_mul hL (of_decide_eq_true h1 c d)
  · unfold eInjCheck7
    refine decide_eq_true fun c d hcd => idx37_inj c d ?_
    have e : keyL (List.range 23) (ePk L (idx37 c)) = keyL (List.range 23) (ePk L (idx37 d)) :=
      keyP_congr _ fun p hp => fd_of_tabEq hL hcd (List.mem_range.1 hp)
    exact eq_of_nodupN (f := fun i => keyL (List.range 23) (ePk L i)) h2 (idx37_lt c)
      (idx37_lt d) e
  · unfold eTorsCheck7
    rw [Bool.and_eq_true, hE4]
    exact ⟨tabEq_of_beq hL h3, by decide⟩
  · unfold actVCheck7
    exact decide_eq_true fun c =>
      ⟨tabEq_conj hL (of_decide_eq_true h4 c), tabEq_conj hL (of_decide_eq_true h5 c)⟩
  · unfold actGCheck7
    exact decide_eq_true fun k c =>
      ⟨tabEq_of_beq hL (of_decide_eq_true h6 k c).1, tabEq_of_beq hL (of_decide_eq_true h6 k c).2⟩
  · unfold thetaCheck7
    rw [Bool.and_eq_true]
    exact ⟨tabEq_of_beq hL h7, tabEq_of_beq hL h8⟩
  · exact tabEq_of_beq hL h8'
  · unfold d8Check7
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨tabEq_of_beq hL h9, tabEq_of_beq hL h10⟩, tabEq_of_beq hL h11⟩,
      decide_eq_true fun c =>
        ⟨tabEq_conj hL (of_decide_eq_true h12 c), tabEq_conj hL (of_decide_eq_true h13 c)⟩⟩

theorem eq_of_idx {g h : NativeSporadic.M23} (e : ∀ x < 23, idx 23 g x = idx 23 h x) : g = h := by
  refine Subtype.ext (Equiv.ext fun i => Fin.ext ?_)
  have := e i.val i.isLt
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at this

theorem phiK_injective (hL : LetterRd L)
    (h1 : n7InvCheck = true) (h2 : n7RelCheck = true) (hok : n7kOk L = true) :
    Function.Injective (phiK h1 h2) := by
  intro g g' e
  obtain ⟨a, ha, k, hk, rfl⟩ := n7K_surj hL h1 h2 hok g
  obtain ⟨b, hb, l, hl, rfl⟩ := n7K_surj hL h1 h2 hok g'
  rw [phiK_n7, phiK_n7] at e
  have := img_injective hL h1 Certificates.certificate271010.2.1 hok
    (a₁ := (⟨a, ha⟩, ⟨k, hk⟩)) (a₂ := (⟨b, hb⟩, ⟨l, hl⟩)) e
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  rw [this.1, this.2]

theorem allAT_spec {g : Nat → Nat → Nat → Nat → Bool} (h : allAT L g = true) {a k : Nat}
    (ha : a < 2520) (hk : k < 16) : g a k (ak L a) (tk L k) = true := by
  unfold allAT at h
  have := allW_spec h a (by rw [a7Words_length]; exact ha)
  rw [Nat.zero_add, sB_eq, ← a7Words_getD ha] at this
  have := List.all_eq_true.1 this k (List.mem_range.2 hk)
  rwa [sB_eq] at this

theorem idx37_single : ∀ j : Fin 3, idx37 (Pi.single j (1 : ZMod 2)) = 2 ^ j.val := by decide

theorem idx37_idxVec : ∀ i : Fin 8, idx37 (idxVec i) = i.val := by decide

theorem e_cent_of (hL : LetterRd L) (h1 : n7InvCheck = true)
    (h2 : n7RelCheck = true) (hok : n7kOk L = true) (h : eCentK L = true) :
    ∀ n : N7, (∀ j : Fin 3, n * n7 (vExp7 (eW7 (Pi.single j 1))) =
      n7 (vExp7 (eW7 (Pi.single j 1))) * n) → ∃ c : V3, n = n7 (vExp7 (eW7 c)) := by
  unfold eCentK at h
  rw [withL_eq, with8_eq] at h
  unfold eCentE at h
  refine n7K_forall hL h1 h2 hok _ fun a ha k hk => ?_
  intro hcomm
  have hg := allAT_spec h ha hk
  have hpt : ∀ x < 23, idx 23 (phiK h1 h2 (n7 (a7W a ++ tw7 k))) x =
      fd 5 (ak L a) (fd 5 (tk L k) x) := fun x hx => by
    rw [phiK_n7, idx_elem h1 hL a hk hx, fd_pcomp (by norm_num) 5 _ _ hx]
  have hpw : ∀ (w : List (Fin 6 × Bool)) {x : Nat}, x < 23 →
      idx 23 (phiK h1 h2 (n7 w)) x = fd 5 (pw L w) x := fun w x hx => by
    rw [phiK_n7]
    exact idx_img h1 hL w hx
  have hc : ∀ j : Fin 3, ∀ x < 23, comAt (ak L a) (tk L k) (ePk L (2 ^ j.val)) x = true := by
    intro j x hx
    have hj : n7 (a7W a ++ tw7 k) * n7 (vExp7 (eW7 (Pi.single j 1))) =
        n7 (vExp7 (eW7 (Pi.single j 1))) * n7 (a7W a ++ tw7 k) := hcomm j
    have e1 := congrArg (fun g => idx 23 (phiK h1 h2 g) x) hj
    simp only [map_mul, idx_mul] at e1
    have hy : fd 5 (pw L (vExp7 (eW7 (Pi.single j 1)))) x < 23 := fd_pw_lt hL _ hx
    have hz : fd 5 (ak L a) (fd 5 (tk L k) x) < 23 := by
      rw [← hpt x hx]
      exact idx_lt _ hx
    rw [hpt x hx, hpw _ hx, hpt _ hy, hpw _ hz] at e1
    unfold comAt
    have hE : ePk L (2 ^ j.val) = pw L (vExp7 (eW7 (Pi.single j 1))) := by
      unfold ePk eW7
      rw [idx37_single]
    rw [hE]
    exact Nat.beq_eq_true_eq _ _ ▸ e1
  have hall : ((List.range 23).all fun x => comAt (ak L a) (tk L k) (ePk L 1) x &&
      comAt (ak L a) (tk L k) (ePk L 2) x && comAt (ak L a) (tk L k) (ePk L 4) x) = true :=
    List.all_eq_true.2 fun x hx => by
      have hx' := List.mem_range.1 hx
      simp only [Bool.and_eq_true]
      exact ⟨⟨hc 0 x hx', hc 1 x hx'⟩, hc 2 x hx'⟩
  rw [hall, Bool.not_true, Bool.false_or, List.any_eq_true] at hg
  obtain ⟨i, hi, hiq⟩ := hg
  have hi8 := List.mem_range.1 hi
  refine ⟨idxVec ⟨i, hi8⟩, phiK_injective hL h1 h2 hok (eq_of_idx fun x hx => ?_)⟩
  have hx' := List.all_eq_true.1 hiq x (List.mem_range.2 hx)
  have hval : n7 (vExp7 (eW7 (idxVec ⟨i, hi8⟩))) = n7 (vExp7 (eWtab7.getD i [])) := by
    unfold eW7
    rw [idx37_idxVec]
  rw [hval, hpt x hx, hpw _ hx]
  exact Nat.eq_of_beq_eq_true hx'

theorem evalWord3_cons {H : Type*} [Group H] (x : Fin 3 → H) (p : Fin 3 × Bool)
    (w : List (Fin 3 × Bool)) :
    evalWord3 x (p :: w) = (if p.2 then x p.1 else (x p.1)⁻¹) * evalWord3 x w := by
  simp [evalWord3]

theorem evW_eval (haff : AffOk) (t : Fin 3 → V3) : ∀ (w : List (Fin 3 × Bool)) (i : Fin 8),
    (evalWord3 (fun k => affPerm8 (mv7 k) (t k)) w i).val =
      evW (vecIdx (t 0)).val (vecIdx (t 1)).val (vecIdx (t 2)).val w i.val
  | [], i => by simp [evalWord3, evW]
  | (k, b) :: w, i => by
    rw [evalWord3_cons, Equiv.Perm.mul_apply, haff k b (t k), evW_eval haff t w]
    fin_cases k <;> rfl

theorem finCheck_of (haff : AffOk) (htr : TrOk)
    {rs : List (List (Fin 3 × Bool) × List (Fin 3 × Bool))} {ws : List (List (Fin 3 × Bool))}
    (h : finKW rs ws = true) : FinCheck mv7 rs pEw7 ws := by
  intro t hR hE w hw
  unfold finKW at h
  have h' := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h _
    (List.mem_range.2 (vecIdx (t 0)).isLt)) _ (List.mem_range.2 (vecIdx (t 1)).isLt)) _
    (List.mem_range.2 (vecIdx (t 2)).isLt)
  have hrel : (rs.all fun r => eqW (vecIdx (t 0)).val (vecIdx (t 1)).val (vecIdx (t 2)).val
      r.1 r.2) = true :=
    List.all_eq_true.2 fun r hr => List.all_eq_true.2 fun i hi => by
      have := congrArg (fun σ : Equiv.Perm (Fin 8) => (σ ⟨i, List.mem_range.1 hi⟩).val) (hR r hr)
      simp only [evW_eval haff t] at this
      exact beq_iff_eq.2 this
  have hew : (([0, 1, 2] : List (Fin 3)).all fun j => (List.range 8).all fun i =>
      evW (vecIdx (t 0)).val (vecIdx (t 1)).val (vecIdx (t 2)).val (pEw7 j) i == i ^^^ 2 ^ j.val) =
      true :=
    List.all_eq_true.2 fun j _ => List.all_eq_true.2 fun i hi => by
      have := congrArg (fun σ : Equiv.Perm (Fin 8) => (σ ⟨i, List.mem_range.1 hi⟩).val) (hE j)
      simp only [evW_eval haff t, htr] at this
      exact beq_iff_eq.2 this
  rw [hrel, hew, Bool.and_self, Bool.not_true, Bool.false_or] at h'
  have hw' := List.all_eq_true.1 h' w hw
  refine Equiv.ext fun i => Fin.ext ?_
  rw [evW_eval haff t, Equiv.Perm.one_apply]
  exact beq_iff_eq.1 (List.all_eq_true.1 hw' i.val (List.mem_range.2 i.isLt))

end CFSG.KC.N7K

end
