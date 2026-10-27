
module

public import Certificates.Data.Kernel.T75JM.PCheckK
public import CFSG.Certificates.Kernel.T75JM.N0KSound

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable

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

theorem ap_pw (hL : LetterRd L) (w : List (Fin 6 × Bool)) {x : Nat} (hx : x < 22) :
    ap (n0Tab w) x = fd 5 (pw L w) x :=
  (fd_wordK_lt hL (lw w) hx).1

theorem fd_pw_lt (hL : LetterRd L) (w : List (Fin 6 × Bool)) {x : Nat} (hx : x < 22) :
    fd 5 (pw L w) x < 22 :=
  (fd_wordK_lt hL (lw w) hx).2

theorem size_n0Tab (hL : LetterRd L) (w : List (Fin 6 × Bool)) : (n0Tab w).size = 22 :=
  (wordT_fd (by norm_num) hid hL (lw w)).1

theorem fd_pc (A B : Nat) {x : Nat} (hx : x < 22) : fd 5 (pc A B) x = fd 5 A (fd 5 B x) :=
  fd_pcomp (by norm_num) 5 A B hx

theorem lw_append (u v : List (Fin 6 × Bool)) : lw (u ++ v) = lw u ++ lw v := by
  simp [lw, liftWord]

theorem fd_pw_append (hL : LetterRd L) (u v : List (Fin 6 × Bool)) {x : Nat} (hx : x < 22) :
    fd 5 (pw L (u ++ v)) x = fd 5 (pw L u) (fd 5 (pw L v) x) := by
  have hy := fd_pw_lt hL v hx
  unfold pw at hy ⊢
  rw [fd_wordK (by norm_num) hid L (lw (u ++ v)) hx, lw_append, List.foldr_append,
    ← fd_wordK (by norm_num) hid L (lw v) hx, ← fd_wordK (by norm_num) hid L (lw u) hy]

theorem tabEq_of_fd (hL : LetterRd L) {w w' : List (Fin 6 × Bool)}
    (h : ∀ x < 22, fd 5 (pw L w) x = fd 5 (pw L w') x) : tabEq w w' = true := by
  unfold tabEq
  refine beq_of_ap (size_n0Tab hL w) (size_n0Tab hL w') fun x hx => ?_
  rw [ap_pw hL w hx, ap_pw hL w' hx]
  exact h x hx

theorem fd_of_tabEq (hL : LetterRd L) {w w' : List (Fin 6 × Bool)} (h : tabEq w w' = true)
    {x : Nat} (hx : x < 22) : fd 5 (pw L w) x = fd 5 (pw L w') x := by
  unfold tabEq at h
  rw [← ap_pw hL w hx, ← ap_pw hL w' hx, beq_iff_eq.1 h]

theorem tabEq_of_beq (hL : LetterRd L) {w w' : List (Fin 6 × Bool)}
    (h : Nat.beq (pw L w) (pw L w') = true) : tabEq w w' = true :=
  tabEq_of_fd hL fun _ _ => by rw [Nat.eq_of_beq_eq_true h]

theorem tabEq_mul (hL : LetterRd L) {u v r : List (Fin 6 × Bool)}
    (h : Nat.beq (pc (pw L u) (pw L v)) (pw L r) = true) : tabEq (u ++ v) r = true :=
  tabEq_of_fd hL fun x hx => by
    rw [← Nat.eq_of_beq_eq_true h, fd_pc _ _ hx, fd_pw_append hL _ _ hx]

theorem tabEq_conj (hL : LetterRd L) {u e r : List (Fin 6 × Bool)}
    (h : Nat.beq (pc (pc (pw L u) (pw L e)) (pw L (invWord u))) (pw L r) = true) :
    tabEq (u ++ e ++ invWord u) r = true :=
  tabEq_of_fd hL fun x hx => by
    have hy := fd_pw_lt hL (invWord u) hx
    rw [← Nat.eq_of_beq_eq_true h, fd_pc _ _ hx, fd_pc _ _ hy, fd_pw_append hL _ _ hx,
      fd_pw_append hL _ _ hy]

theorem idx3_lt : ∀ c : V3, idx3 c < 8 := by decide

theorem idx3_inj : ∀ c d : V3, idx3 c = idx3 d → c = d := by decide

theorem idx3_single0 : idx3 (Pi.single (0 : Fin 3) (1 : ZMod 2)) = 1 := by decide

theorem pChecks_of (hL : LetterRd L) (h : pOkK L = true) :
    eMulCheck = true ∧ eInjCheck = true ∧ eTorsCheck = true ∧ actVCheck = true ∧
      actGCheck = true ∧ thetaCheck = true ∧ d8Check = true := by
  unfold pOkK at h
  rw [withL_eq, with8_eq] at h
  unfold pOkE at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  unfold eMulK at h1
  unfold conjK at h4 h5 h12 h13
  unfold actGK at h6
  have hE1 : eW (Pi.single (0 : Fin 3) (1 : ZMod 2)) = eWtab.getD 1 [] := by
    unfold eW
    rw [idx3_single0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold eMulCheck
    exact decide_eq_true fun c d => tabEq_mul hL (of_decide_eq_true h1 c d)
  · unfold eInjCheck
    refine decide_eq_true fun c d hcd => idx3_inj c d ?_
    have e : keyL (List.range 22) (ePk L (idx3 c)) = keyL (List.range 22) (ePk L (idx3 d)) :=
      keyP_congr _ fun p hp => fd_of_tabEq hL hcd (List.mem_range.1 hp)
    exact eq_of_nodupN (f := fun i => keyL (List.range 22) (ePk L i)) h2 (idx3_lt c) (idx3_lt d) e
  · unfold eTorsCheck
    rw [Bool.and_eq_true, hE1]
    exact ⟨tabEq_of_beq hL h3, by decide⟩
  · unfold actVCheck
    exact decide_eq_true fun c =>
      ⟨tabEq_conj hL (of_decide_eq_true h4 c), tabEq_conj hL (of_decide_eq_true h5 c)⟩
  · unfold actGCheck
    exact decide_eq_true fun c =>
      ⟨tabEq_of_beq hL (of_decide_eq_true h6 c).1, tabEq_of_beq hL (of_decide_eq_true h6 c).2⟩
  · unfold thetaCheck
    rw [Bool.and_eq_true]
    exact ⟨tabEq_of_beq hL h7, tabEq_of_beq hL h8⟩
  · unfold d8Check
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨tabEq_of_beq hL h9, tabEq_of_beq hL h10⟩, tabEq_of_beq hL h11⟩,
      decide_eq_true fun c =>
        ⟨tabEq_conj hL (of_decide_eq_true h12 c), tabEq_conj hL (of_decide_eq_true h13 c)⟩⟩

theorem phiK_injective (hL : LetterRd L)
    (h1 : n0InvCheck = true) {h2 : n0RelCheck = true} (hok : n0kOk L = true) :
    Function.Injective (phiK h1 h2) := by
  obtain ⟨-, hfix, ha, ht⟩ := n0kOk_parts hok
  intro g g' e
  obtain ⟨a, ha', k, hk, rfl⟩ := n0K_surj hL h1 hok g
  obtain ⟨b, hb', l, hl, rfl⟩ := n0K_surj hL h1 hok g'
  simp only [n0_append, map_mul] at e ⊢
  have hH : ∀ p ∈ hexad, fd 5 (ak L a) p = fd 5 (ak L b) p := by
    intro p hp
    have hp22 : p < 22 := by simp [hexad] at hp; omega
    have := congrArg (fun g => idx 22 g p) e
    simp only [idx_mul] at this
    rw [idx_tk hL hk hp22, hfix k hk p hp, idx_tk hL hl hp22, hfix l hl p hp,
      idx_ak hL a hp22, idx_ak hL b hp22] at this
    exact this
  have hab : a = b := by
    refine eq_of_nodupA (f := fun u => keyP hexad (ptW L (u.map a6Z))) ha ha' hb'
      (keyP_congr hexad fun p hp => ?_)
    have hp22 : p < 22 := by simp [hexad] at hp; omega
    rw [ptW_eq L _ hp22, ptW_eq L _ hp22]
    exact hH p hp
  subst hab
  have e' := mul_left_cancel e
  have hT : ∀ p ∈ List.range 22, fd 5 (tk L k) p = fd 5 (tk L l) p := by
    intro p hp
    have hp22 := List.mem_range.1 hp
    rw [← idx_tk (h1 := h1) (h2 := h2) hL hk hp22, ← idx_tk (h1 := h1) (h2 := h2) hL hl hp22, e']
  have hkey : keyL (List.range 22) (tk L k) = keyL (List.range 22) (tk L l) := keyP_congr _ hT
  have hkl : k = l := eq_of_nodupN ht hk hl hkey
  subst hkl
  rfl

theorem allAT_spec {g : Nat → Nat → Nat → Nat → Bool} (h : allAT L g = true) {a k : Nat}
    (ha : a < 360) (hk : k < 16) : g a k (ak L a) (tk L k) = true := by
  unfold allAT at h
  have := allW_spec h a (by rw [a6Words_length]; exact ha)
  rw [Nat.zero_add, sB_eq, ← a6Words_getD ha] at this
  have := List.all_eq_true.1 this k (List.mem_range.2 hk)
  rwa [sB_eq] at this

theorem idx3_single : ∀ j : Fin 3, idx3 (Pi.single j (1 : ZMod 2)) = 2 ^ j.val := by decide

theorem idx3_idxVec : ∀ i : Fin 8, idx3 (idxVec i) = i.val := by decide

theorem e_cent_of (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) (h : eCentK L = true) :
    ∀ n : PG 6 rels6, (∀ j : Fin 3, n * val6 (vExp (eW (Pi.single j 1))) =
      val6 (vExp (eW (Pi.single j 1))) * n) → ∃ c : V3, n = val6 (vExp (eW c)) := by
  have h2 := n0RelCheck_of hL (n0kOk_parts hok).1
  unfold eCentK at h
  rw [withL_eq, with8_eq] at h
  unfold eCentE at h
  refine n0K_forall hL h1 hok _ fun a ha k hk => ?_
  intro hcomm
  have hg := allAT_spec h ha hk
  have hpt : ∀ x < 22, idx 22 (phiK h1 h2 (n0 (a6W a ++ tw k))) x =
      fd 5 (ak L a) (fd 5 (tk L k) x) := fun x hx => by
    rw [idx_phiK_elem hL a hk hx, fd_pcomp (by norm_num) 5 _ _ hx]
  have hpw : ∀ (w : List (Fin 6 × Bool)) {x : Nat}, x < 22 →
      idx 22 (phiK h1 h2 (n0 w)) x = fd 5 (pw L w) x := fun w x hx => idx_phiK hL w hx
  have hc : ∀ j : Fin 3, ∀ x < 22, comAt (ak L a) (tk L k) (ePk L (2 ^ j.val)) x = true := by
    intro j x hx
    have hj : n0 (a6W a ++ tw k) * n0 (vExp (eW (Pi.single j 1))) =
        n0 (vExp (eW (Pi.single j 1))) * n0 (a6W a ++ tw k) := hcomm j
    have e1 := congrArg (fun g => idx 22 (phiK h1 h2 g) x) hj
    simp only [map_mul, idx_mul] at e1
    have hy : fd 5 (pw L (vExp (eW (Pi.single j 1)))) x < 22 := fd_pw_lt hL _ hx
    have hz : fd 5 (ak L a) (fd 5 (tk L k) x) < 22 := by
      rw [← hpt x hx]
      exact idx_lt _ hx
    rw [hpt x hx, hpw _ hx, hpt _ hy, hpw _ hz] at e1
    unfold comAt
    have hE : ePk L (2 ^ j.val) = pw L (vExp (eW (Pi.single j 1))) := by
      unfold ePk eW
      rw [idx3_single]
    rw [hE]
    exact Nat.beq_eq_true_eq _ _ ▸ e1
  have hall : ((List.range 22).all fun x => comAt (ak L a) (tk L k) (ePk L 1) x &&
      comAt (ak L a) (tk L k) (ePk L 2) x && comAt (ak L a) (tk L k) (ePk L 4) x) = true :=
    List.all_eq_true.2 fun x hx => by
      have hx' := List.mem_range.1 hx
      simp only [Bool.and_eq_true]
      exact ⟨⟨hc 0 x hx', hc 1 x hx'⟩, hc 2 x hx'⟩
  rw [hall, Bool.not_true, Bool.false_or, List.any_eq_true] at hg
  obtain ⟨i, hi, hiq⟩ := hg
  have hi8 := List.mem_range.1 hi
  refine ⟨idxVec ⟨i, hi8⟩, phiK_injective (h2 := h2) hL h1 hok (eq_of_idx fun x hx => ?_)⟩
  have hx' := List.all_eq_true.1 hiq x (List.mem_range.2 hx)
  have hval : val6 (vExp (eW (idxVec ⟨i, hi8⟩))) = n0 (vExp (eWtab.getD i [])) := by
    unfold eW
    rw [idx3_idxVec]
    rfl
  rw [hval, hpt x hx, hpw _ hx]
  exact Nat.eq_of_beq_eq_true hx'

theorem evalWord3_cons {H : Type*} [Group H] (x : Fin 3 → H) (p : Fin 3 × Bool)
    (w : List (Fin 3 × Bool)) :
    evalWord3 x (p :: w) = (if p.2 then x p.1 else (x p.1)⁻¹) * evalWord3 x w := by
  simp [evalWord3]

theorem evW_eval (haff : AffOk) (t : Fin 3 → V3) : ∀ (w : List (Fin 3 × Bool)) (i : Fin 8),
    (evalWord3 (fun k => affPerm8 (mv k) (t k)) w i).val =
      evW (vecIdx (t 0)).val (vecIdx (t 1)).val (vecIdx (t 2)).val w i.val
  | [], i => by simp [evalWord3, evW]
  | (k, b) :: w, i => by
    rw [evalWord3_cons, Equiv.Perm.mul_apply, haff k b (t k), evW_eval haff t w]
    fin_cases k <;> rfl

theorem finCheck_of (haff : AffOk) (htr : TrOk) (h : finK = true) :
    FinCheck mv pRs pEw pWords := by
  intro t hR hE w hw
  unfold finK finKW at h
  have h' := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h _
    (List.mem_range.2 (vecIdx (t 0)).isLt)) _ (List.mem_range.2 (vecIdx (t 1)).isLt)) _
    (List.mem_range.2 (vecIdx (t 2)).isLt)
  have hrel : (pRs.all fun r => eqW (vecIdx (t 0)).val (vecIdx (t 1)).val (vecIdx (t 2)).val
      r.1 r.2) = true :=
    List.all_eq_true.2 fun r hr => List.all_eq_true.2 fun i hi => by
      have := congrArg (fun σ : Equiv.Perm (Fin 8) => (σ ⟨i, List.mem_range.1 hi⟩).val) (hR r hr)
      simp only [evW_eval haff t] at this
      exact beq_iff_eq.2 this
  have hew : (([0, 1, 2] : List (Fin 3)).all fun j => (List.range 8).all fun i =>
      evW (vecIdx (t 0)).val (vecIdx (t 1)).val (vecIdx (t 2)).val (pEw j) i == i ^^^ 2 ^ j.val) =
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

end CFSG.KC.N0K

end
