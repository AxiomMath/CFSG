module

public import Certificates.Data.Kernel.LocalQT.TcP
public import CFSG.Certificates.Kernel.LocalQTTcKSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Multi

public section

namespace CFSG.KC.LQT.TCP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.LQT.TC CFSG.KC.LQT.TCK
  CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.J2Excl CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

variable {n w : ℕ}

@[expose] def RS (n w P : ℕ) (g : Equiv.Perm (Fin n)) : Prop :=
  RP n w P g ∧ P >>> (n * w) = 0

theorem rp_unique {P : ℕ} {g h : Equiv.Perm (Fin n)} (hg : RP n w P g) (hh : RP n w P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem eq_of_rs {P Q : ℕ} {g : Equiv.Perm (Fin n)} (hP : RS n w P g) (hQ : RS n w Q g) :
    P = Q := by
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · subst h0
    have h1 := hP.2
    have h2 := hQ.2
    simp only [Nat.mul_zero, Nat.shiftRight_zero] at h1 h2
    omega
  · exact CFSG.KS.PF.eq_of_fields h0 hP.2 hQ.2 fun i hi => by
      rw [hP.1 ⟨i, hi⟩, hQ.1 ⟨i, hi⟩]

theorem clogR_le (n : ℕ) : ∀ k, CFSG.KS.PF.clogR n k ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have e : CFSG.KS.PF.clogR n (k + 1) = nIf(Nat.blt (Nat.shiftLeft (nat_lit 1)
        (CFSG.KS.PF.clogR n k)) n, Nat.succ (CFSG.KS.PF.clogR n k),
        CFSG.KS.PF.clogR n k) := rfl
    have ih := clogR_le n k
    rw [e]
    generalize CFSG.KS.PF.clogR n k = c at ih ⊢
    cases Nat.blt (Nat.shiftLeft 1 c) n
    · exact Nat.le_succ_of_le ih
    · exact Nat.succ_le_succ ih

theorem pmkT_zero (n w : ℕ) (hn : n ≤ 1) : ∀ d lo, pmkT n w (fun i => i) d lo = 0
  | 0, lo => by
    change Bool.rec (motive := fun _ => ℕ) (nat_lit 0) lo (Nat.blt lo n) = 0
    cases h : Nat.blt lo n
    · rfl
    · have := Nat.blt_eq.mp h
      show lo = 0
      omega
  | d + 1, lo => by
    have e : pmkT n w (fun i => i) (d + 1) lo = Nat.lor (pmkT n w (fun i => i) d lo)
        (Nat.shiftLeft (pmkT n w (fun i => i) d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d)))
          (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))) := rfl
    rw [e, pmkT_zero n w hn d, pmkT_zero n w hn d]
    simp

theorem idK_facts (h : idK n w (mask w) = true) :
    n < 2 ^ 32 ∧ n ≤ 2 ^ w ∧ pidn n w >>> (n * w) = 0 := by
  have hid : ∀ i < n, pg w (mask w) (pidn n w) i = i := fun i hi =>
    Nat.eq_of_beq_eq_true (allN_spec h i hi)
  have hnw : n ≤ 2 ^ w := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    · have h1 := hid (n - 1) (by omega)
      have h2 := CFSG.KS.PF.pg_lt w (pidn n w) (n - 1)
      omega
  have e : pidn n w = pmkT n w (fun i => i) (clog n) 0 := by
    unfold pidn pmk
    rw [CFSG.KS.PF.strictN_eqP]
  have hfld : CFSG.KS.PF.Fld w (pidn n w)
      (fun i => if i < 2 ^ clog n then (if 0 + i < n then i else 0) else 0) := by
    rw [e]
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_pmkT n w (fun i => i)
      (fun x hx => Nat.lt_of_lt_of_le hx hnw) (clog n) 0) ?_
    intro i
    simp
  have hclog : clog n ≤ 24 := clogR_le n 24
  have h24 : n ≤ 2 ^ 24 := by
    by_contra hc
    have hi : 2 ^ 24 < n := by omega
    have h1 := hid _ hi
    have hnot : ¬ (2 ^ 24 < 2 ^ clog n) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hclog
      omega
    have h2 := CFSG.KS.PF.pg_of_fld (i := 2 ^ 24) hfld (by
      simp only [hnot, ↓reduceIte]
      exact Nat.two_pow_pos w)
    simp only [hnot, ↓reduceIte] at h2
    omega
  refine ⟨?_, hnw, ?_⟩
  · have : (2 : ℕ) ^ 24 < 2 ^ 32 := by norm_num
    omega
  · rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0
      have h1 : n ≤ 1 := by simpa using hnw
      rw [e, pmkT_zero n 0 h1]
      simp
    · exact CFSG.KS.PF.shr_zero_of_fld h0 hfld (fun i hi => by
        have : ¬ i < n := by omega
        simp [this])

theorem pcomp_zero_w (hn : n ≤ 1) (m p q : ℕ) (hm : m = mask 0) : pcomp n 0 m p q = 0 := by
  subst hm
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · rfl
  · have e : pcomp 1 0 (mask 0) p q = Nat.lor (Nat.shiftLeft (pmkH 0 (mask 0) p q 0 0)
        (Nat.mul 0 0)) 0 := rfl
    have h := CFSG.KS.PF.pg_lt 0 p (pg 0 (mask 0) q 0)
    have h' : pmkH 0 (mask 0) p q 0 0 = 0 := by
      change pg 0 (mask 0) p (pg 0 (mask 0) q 0) = 0
      simpa using h
    rw [e, h']
    simp

theorem shr_pcomp (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) (p q : ℕ) :
    pcomp n w (mask w) p q >>> (n * w) = 0 := by
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · subst h0
    have h1 : n ≤ 1 := by simpa using hnw
    rw [pcomp_zero_w h1 _ p q rfl]
    simp
  · exact CFSG.KS.PF.pcomp_shr p q hn h0

theorem rs_pcomp (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {P Q : ℕ} {g h : Equiv.Perm (Fin n)}
    (hP : RS n w P g) (hQ : RS n w Q h) : RS n w (pcomp n w (mask w) P Q) (g * h) :=
  ⟨rp_pcomp hn hP.1 hQ.1, shr_pcomp hn hnw P Q⟩

theorem rs_idn (h : idK n w (mask w) = true) : RS n w (pidn n w) 1 :=
  ⟨rp_idn h, (idK_facts h).2.2⟩

theorem rs_of_permOK {P Q : ℕ} (h : permOK n w (mask w) (n * w) P Q = true) :
    ∃ g : Equiv.Perm (Fin n), PRep n (unpack n w P, unpack n w Q) g ∧ RS n w P g ∧
      RS n w Q g⁻¹ := by
  obtain ⟨g, h1, h2, h3⟩ := of_permOK h
  obtain ⟨s1, s2, -⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  exact ⟨g, h1, ⟨h2, s1⟩, ⟨h3, s2⟩⟩

@[expose] def PrP (n w : ℕ) (r : PArr) (A AI : ℕ) : Prop :=
  ∃ g : Equiv.Perm (Fin n), PRep n r g ∧ RS n w A g ∧ RS n w AI g⁻¹

theorem PrP.mul (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {r r' : PArr} {A AI B BI : ℕ}
    (h : PrP n w r A AI) (h' : PrP n w r' B BI) :
    PrP n w (pMul n r r') (pcomp n w (mask w) A B) (pcomp n w (mask w) BI AI) := by
  obtain ⟨g, h1, h2, h3⟩ := h
  obtain ⟨g', h1', h2', h3'⟩ := h'
  refine ⟨g * g', h1.mul h1', rs_pcomp hn hnw h2 h2', ?_⟩
  rw [mul_inv_rev]
  exact rs_pcomp hn hnw h3' h3

theorem PrP.inv {r : PArr} {A AI : ℕ} (h : PrP n w r A AI) : PrP n w (pInv r) AI A := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨g⁻¹, h1.inv, h3, ?_⟩
  rw [inv_inv]
  exact h2

theorem PrP.id {idn : ℕ} (hid : RS n w idn 1) : PrP n w (pId n) idn idn :=
  ⟨1, pRep_id, hid, by rw [inv_one]; exact hid⟩

theorem prp_of_permOK {P Q : ℕ} (h : permOK n w (mask w) (n * w) P Q = true) :
    PrP n w (unpack n w P, unpack n w Q) P Q := by
  obtain ⟨g, h1, h2, h3⟩ := rs_of_permOK h
  exact ⟨g, h1, h2, h3⟩

theorem prp_conj (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {g t : PArr} {G GI T TI : ℕ}
    (hg : PrP n w g G GI) (ht : PrP n w t T TI) :
    PrP n w (pConj n g t) (pcomp n w (mask w) (pcomp n w (mask w) G T) GI)
      (pcomp n w (mask w) G (pcomp n w (mask w) TI GI)) :=
  (hg.mul hn hnw ht |>.mul hn hnw hg.inv)

section Gens

variable {idn : ℕ} {G GI : List ℕ} (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) (hid : RS n w idn 1)
  (hl : G.length = GI.length) (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true)

include hid hl hz in
theorem gen_prp (k : ℕ) :
    PrP n w ((((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2))).getD k (pId n))
      (G.getD k idn) (GI.getD k idn) := by
  by_cases hk : k < G.length
  · have hk' : k < GI.length := hl ▸ hk
    have hkz : k < (G.zip GI).length := by simp [hk, hk']
    have := prp_of_permOK (hz _ (List.getElem_mem hkz))
    rw [List.getD_eq_getElem _ _ (by simpa using hkz), List.getElem_map,
      List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk']
    simpa using this
  · have hk' : ¬ k < GI.length := hl ▸ hk
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]
    exact PrP.id hid

theorem letGP_eq_pos (idn : ℕ) (G GI : List ℕ) (j : ℕ) (k : ℕ → ℕ → Bool) :
    letGP idn G GI (Int.ofNat (j + 1)) k = k (getTc idn G j) (getTc idn GI j) := rfl

theorem letGP_eq_neg (idn : ℕ) (G GI : List ℕ) (j : ℕ) (k : ℕ → ℕ → Bool) :
    letGP idn G GI (Int.negSucc j) k = k (getTc idn GI j) (getTc idn G j) := rfl

theorem letGP_eq_zero (idn : ℕ) (G GI : List ℕ) (k : ℕ → ℕ → Bool) :
    letGP idn G GI 0 k = k idn idn := rfl

include hid hl hz in
theorem letGP_sound (z : ℤ) (k : ℕ → ℕ → Bool) (h : letGP idn G GI z k = true) :
    ∃ A AI, k A AI = true ∧
      PrP n w (pLetter n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2)) z) A AI := by
  rcases z with (_ | j) | j
  · refine ⟨idn, idn, h, ?_⟩
    simpa [pLetter] using PrP.id hid
  · rw [letGP_eq_pos] at h
    refine ⟨_, _, h, ?_⟩
    rw [pLetter_pos, getTc_eq, getTc_eq]
    exact gen_prp hid hl hz j
  · rw [letGP_eq_neg] at h
    refine ⟨_, _, h, ?_⟩
    rw [pLetter_neg, getTc_eq, getTc_eq]
    exact (gen_prp hid hl hz j).inv

theorem wordP_nil (n w idn : ℕ) (G GI : List ℕ) (k : ℕ → ℕ → Bool) :
    wordP n w idn G GI [] k = k idn idn := rfl

theorem wordP_cons (n w idn : ℕ) (G GI : List ℕ) (z : ℤ) (wd : List ℤ) (k : ℕ → ℕ → Bool) :
    wordP n w idn G GI (z :: wd) k = wordP n w idn G GI wd (fun A AI =>
      letGP idn G GI z fun L LI =>
      strictB (pcomp n w (mask w) L A) fun B => strictB (pcomp n w (mask w) AI LI) fun BI =>
        k B BI) := rfl

include hn hnw hid hl hz in
theorem wordP_sound (wd : List ℤ) : ∀ (k : ℕ → ℕ → Bool), wordP n w idn G GI wd k = true →
    ∃ A AI, k A AI = true ∧
      PrP n w (pWord n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2)) wd) A AI := by
  induction wd with
  | nil =>
    intro k h
    rw [wordP_nil] at h
    exact ⟨idn, idn, h, PrP.id hid⟩
  | cons z wd ih =>
    intro k h
    rw [wordP_cons] at h
    obtain ⟨A, AI, h1, hA⟩ := ih _ h
    obtain ⟨L, LI, h2, hL⟩ := letGP_sound hid hl hz z _ h1
    rw [sB, sB] at h2
    exact ⟨_, _, h2, hL.mul hn hnw hA⟩

end Gens

@[expose] def R1 (Ps : List (ℕ × ℕ)) : List ℕ := (Ps.map Prod.fst).reverse

@[expose] def R2 (Ps : List (ℕ × ℕ)) : List ℕ := (Ps.map Prod.snd).reverse

@[expose] def RelP (n w : ℕ) (regs : List PArr) (Ps : List (ℕ × ℕ)) : Prop :=
  List.Forall₂ (fun r pq => PrP n w r pq.1 pq.2) regs Ps

theorem relP_append {regs : List PArr} {Ps : List (ℕ × ℕ)} (h : RelP n w regs Ps) {r : PArr}
    {A AI : ℕ} (hr : PrP n w r A AI) : RelP n w (regs ++ [r]) (Ps ++ [(A, AI)]) :=
  List.rel_append h (List.Forall₂.cons hr List.Forall₂.nil)

theorem regTc_eq (idn : ℕ) (L : List ℕ) (k : ℕ) : regTc idn L.reverse L.length k = L.getD k idn := by
  by_cases hk : k < L.length
  · unfold regTc
    have hb : Nat.blt k L.length = true := Nat.blt_eq.mpr hk
    rw [hb]
    change getTc idn L.reverse (Nat.sub (Nat.sub L.length k) 1) = _
    rw [getTc_eq, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse,
      List.getD_eq_getElem _ _ hk]
    congr 1
    change L.length - 1 - (L.length - k - 1) = k
    omega
  · unfold regTc
    have : Nat.blt k L.length = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact hk (Nat.blt_eq.mp e)
    rw [this, List.getD_eq_default _ _ (by omega)]

theorem forall₂_getD {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {d₁ : α} {d₂ : β} (hd : R d₁ d₂) (k : ℕ) :
    R (l₁.getD k d₁) (l₂.getD k d₂) := by
  induction h generalizing k with
  | nil => simpa using hd
  | cons h1 h2 ih =>
    cases k with
    | zero => simpa using h1
    | succ k => simpa using ih k

theorem relP_getD {regs : List PArr} {Ps : List (ℕ × ℕ)} (h : RelP n w regs Ps) {idn : ℕ}
    (hid : RS n w idn 1) (k : ℕ) :
    PrP n w (regs.getD k (pId n)) (regTc idn (R1 Ps) Ps.length k) (regTc idn (R2 Ps) Ps.length k) := by
  have h1 := regTc_eq idn (Ps.map Prod.fst) k
  have h2 := regTc_eq idn (Ps.map Prod.snd) k
  rw [List.length_map] at h1 h2
  have := forall₂_getD (d₂ := (idn, idn)) h (PrP.id hid : PrP n w (pId n) idn idn) k
  unfold R1 R2
  rw [h1, h2]
  have e1 : (Ps.map Prod.fst).getD k idn = (Ps.getD k (idn, idn)).1 := by
    exact List.getD_map Ps (idn, idn) Prod.fst
  have e2 : (Ps.map Prod.snd).getD k idn = (Ps.getD k (idn, idn)).2 := by
    exact List.getD_map Ps (idn, idn) Prod.snd
  rw [e1, e2]
  exact this

theorem letRP_eq_pos (idn : ℕ) (r1 r2 : List ℕ) (len j : ℕ) (k : ℕ → ℕ → Bool) :
    letRP idn r1 r2 len (Int.ofNat (j + 1)) k = k (regTc idn r1 len j) (regTc idn r2 len j) := rfl

theorem letRP_eq_neg (idn : ℕ) (r1 r2 : List ℕ) (len j : ℕ) (k : ℕ → ℕ → Bool) :
    letRP idn r1 r2 len (Int.negSucc j) k = k (regTc idn r2 len j) (regTc idn r1 len j) := rfl

theorem letRP_eq_zero (idn : ℕ) (r1 r2 : List ℕ) (len : ℕ) (k : ℕ → ℕ → Bool) :
    letRP idn r1 r2 len 0 k = k idn idn := rfl

theorem letRP_sound {regs : List PArr} {Ps : List (ℕ × ℕ)} (hR : RelP n w regs Ps) {idn : ℕ}
    (hid : RS n w idn 1) (z : ℤ) (k : ℕ → ℕ → Bool)
    (h : letRP idn (R1 Ps) (R2 Ps) Ps.length z k = true) :
    ∃ A AI, k A AI = true ∧ PrP n w (pLetter n regs z) A AI := by
  rcases z with (_ | j) | j
  · refine ⟨idn, idn, h, ?_⟩
    simpa [pLetter] using PrP.id hid
  · rw [letRP_eq_pos] at h
    refine ⟨_, _, h, ?_⟩
    rw [pLetter_pos]
    exact relP_getD hR hid j
  · rw [letRP_eq_neg] at h
    refine ⟨_, _, h, ?_⟩
    rw [pLetter_neg]
    exact (relP_getD hR hid j).inv

theorem runP_nil (n w idn : ℕ) (k : List ℕ → List ℕ → ℕ → Bool) (r1 r2 : List ℕ) (len : ℕ) :
    runP n w idn [] k r1 r2 len = k r1 r2 len := rfl

theorem runP_cons (n w idn : ℕ) (pq : ℤ × ℤ) (prog : List (ℤ × ℤ))
    (k : List ℕ → List ℕ → ℕ → Bool) (r1 r2 : List ℕ) (len : ℕ) :
    runP n w idn (pq :: prog) k r1 r2 len =
      letRP idn r1 r2 len pq.1 fun A AI => letRP idn r1 r2 len pq.2 fun B BI =>
        strictB (pcomp n w (mask w) A B) fun C => strictB (pcomp n w (mask w) BI AI) fun CI =>
          runP n w idn prog k (C :: r1) (CI :: r2) (len + 1) := rfl

theorem R1_append (Ps : List (ℕ × ℕ)) (A AI : ℕ) : R1 (Ps ++ [(A, AI)]) = A :: R1 Ps := by
  simp [R1]

theorem R2_append (Ps : List (ℕ × ℕ)) (A AI : ℕ) : R2 (Ps ++ [(A, AI)]) = AI :: R2 Ps := by
  simp [R2]

theorem runP_sound (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hid : RS n w idn 1)
    (k : List ℕ → List ℕ → ℕ → Bool) : ∀ (prog : List (ℤ × ℤ)) (regs : List PArr)
    (Ps : List (ℕ × ℕ)), RelP n w regs Ps →
    runP n w idn prog k (R1 Ps) (R2 Ps) Ps.length = true →
      ∃ Ps', RelP n w (pRun n regs prog) Ps' ∧ k (R1 Ps') (R2 Ps') Ps'.length = true
  | [], regs, Ps, hR, hk => ⟨Ps, hR, hk⟩
  | pq :: prog, regs, Ps, hR, hk => by
    rw [runP_cons] at hk
    obtain ⟨A, AI, h1, hA⟩ := letRP_sound hR hid pq.1 _ hk
    obtain ⟨B, BI, h2, hB⟩ := letRP_sound hR hid pq.2 _ h1
    rw [sB, sB] at h2
    have hr := relP_append hR (hA.mul hn hnw hB)
    rw [pRun_cons]
    refine runP_sound hn hnw hid k prog _ _ hr ?_
    rw [R1_append, R2_append, List.length_append, List.length_singleton]
    exact h2

theorem conjOneP_cons (n w g gi : ℕ) (t : ℕ) (T : List ℕ) (ti : ℕ) (TI : List ℕ)
    (k : List ℕ → List ℕ → ℕ → Bool) (r1 r2 : List ℕ) (len : ℕ) :
    conjOneP n w g gi (t :: T) (ti :: TI) k r1 r2 len =
      strictB (pcomp n w (mask w) (pcomp n w (mask w) g t) gi) fun C =>
        strictB (pcomp n w (mask w) g (pcomp n w (mask w) ti gi)) fun CI =>
          conjOneP n w g gi T TI k (C :: r1) (CI :: r2) (len + 1) := rfl

theorem conjOneP_nil (n w g gi : ℕ) (k : List ℕ → List ℕ → ℕ → Bool) (r1 r2 : List ℕ)
    (len : ℕ) :
    conjOneP n w g gi [] [] k r1 r2 len = k r1 r2 len := rfl

theorem conjOneP_sound (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {gp : PArr} {g gi : ℕ}
    (hg : PrP n w gp g gi) (k : List ℕ → List ℕ → ℕ → Bool) :
    ∀ (T TI : List ℕ), T.length = TI.length →
    (∀ p ∈ T.zip TI, permOK n w (mask w) (n * w) p.1 p.2 = true) →
    ∀ (regs : List PArr) (Ps : List (ℕ × ℕ)), RelP n w regs Ps →
    conjOneP n w g gi T TI k (R1 Ps) (R2 Ps) Ps.length = true →
      ∃ Ps', RelP n w (regs ++ ((T.zip TI).map fun p => (unpack n w p.1, unpack n w p.2)).map
          fun t => pConj n gp t) Ps' ∧ k (R1 Ps') (R2 Ps') Ps'.length = true
  | [], TI, hl, _, regs, Ps, hR, hk => by
    cases TI with
    | nil => exact ⟨Ps, by simpa using hR, hk⟩
    | cons _ _ => simp at hl
  | t :: T, TI, hl, hz, regs, Ps, hR, hk => by
    cases TI with
    | nil => simp at hl
    | cons ti TI =>
      rw [conjOneP_cons, sB, sB] at hk
      have hp := prp_of_permOK (hz (t, ti) List.mem_cons_self)
      have hc := prp_conj hn hnw hg hp
      have hr := relP_append hR hc
      have hz' : ∀ p ∈ T.zip TI, permOK n w (mask w) (n * w) p.1 p.2 = true :=
        fun p hp => hz p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
      obtain ⟨Ps', h1, h2⟩ := conjOneP_sound hn hnw hg k T TI (by simpa using hl) hz' _ _ hr
        (by rw [R1_append, R2_append, List.length_append, List.length_singleton]; exact hk)
      refine ⟨Ps', ?_, h2⟩
      simpa [List.append_assoc] using h1

theorem conjsP_nil (n w idn : ℕ) (G GI TS TIS : List ℕ) (k : List ℕ → List ℕ → ℕ → Bool)
    (r1 r2 : List ℕ) (len : ℕ) :
    conjsP n w idn G GI TS TIS [] k r1 r2 len = k r1 r2 len := rfl

theorem conjsP_cons (n w idn : ℕ) (G GI TS TIS : List ℕ) (wd : List ℤ) (ws : List (List ℤ))
    (k : List ℕ → List ℕ → ℕ → Bool) (r1 r2 : List ℕ) (len : ℕ) :
    conjsP n w idn G GI TS TIS (wd :: ws) k r1 r2 len =
      wordP n w idn G GI wd fun g gi =>
        conjOneP n w g gi TS TIS (conjsP n w idn G GI TS TIS ws k) r1 r2 len := rfl

theorem conjsP_sound (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hid : RS n w idn 1)
    {G GI TS TIS : List ℕ} (hl : G.length = GI.length)
    (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true)
    (hlT : TS.length = TIS.length)
    (hzT : ∀ p ∈ TS.zip TIS, permOK n w (mask w) (n * w) p.1 p.2 = true)
    (k : List ℕ → List ℕ → ℕ → Bool) : ∀ (ws : List (List ℤ)) (regs : List PArr)
    (Ps : List (ℕ × ℕ)), RelP n w regs Ps →
    conjsP n w idn G GI TS TIS ws k (R1 Ps) (R2 Ps) Ps.length = true →
      ∃ Ps', RelP n w (regs ++ ws.flatMap fun wd =>
        ((TS.zip TIS).map fun p => (unpack n w p.1, unpack n w p.2)).map fun t =>
          pConj n (pWord n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2)) wd) t) Ps' ∧
        k (R1 Ps') (R2 Ps') Ps'.length = true
  | [], regs, Ps, hR, hk => ⟨Ps, by simpa using hR, hk⟩
  | wd :: ws, regs, Ps, hR, hk => by
    rw [conjsP_cons] at hk
    obtain ⟨g, gi, h1, hg⟩ := wordP_sound hn hnw hid hl hz wd _ hk
    obtain ⟨Ps', h2, h3⟩ := conjOneP_sound hn hnw hg _ TS TIS hlT hzT regs Ps hR h1
    obtain ⟨Ps'', h4, h5⟩ := conjsP_sound hn hnw hid hl hz hlT hzT k ws _ _ h2 h3
    refine ⟨Ps'', ?_, h5⟩
    rw [List.flatMap_cons]
    simpa [List.append_assoc] using h4

theorem exists_of_mem_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons h1 h2 ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h1⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem mcP_core {G GI TS TIS : List ℕ} {ws : List (List ℤ)} {prog : List (ℤ × ℤ)}
    {targets : List ℕ} (h : mcP n w G GI TS TIS ws prog targets = true) :
    multiConjCheck n ((G.zip GI).map fun p => (unpack n w p.1, unpack n w p.2))
      ((TS.zip TIS).map fun p => (unpack n w p.1, unpack n w p.2)) ws prog
      (targets.map (unpack n w)) = true := by
  unfold mcP at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨hp, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨hlT, hzT⟩ := gensTc_sound TS TIS hp
  obtain ⟨Ps, hR, hk⟩ := conjsP_sound hn hnw hidn hl hz hlT hzT _ ws [] [] List.Forall₂.nil h
  obtain ⟨Ps', hR', hk'⟩ := runP_sound hn hnw hidn _ prog _ Ps hR hk
  have htarg := targTc_sound targets (R1 Ps') hk'
  unfold multiConjCheck
  rw [List.all_eq_true]
  intro A' hA'
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
  have hAP := htarg A hA
  unfold R1 at hAP
  obtain ⟨pq, hpq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hAP)
  obtain ⟨r, hr, g, h1, h2, -⟩ := exists_of_mem_right hR' hpq
  rw [List.any_eq_true]
  refine ⟨r, ?_, (eqA_iff h1.1 (CFSG.KS.Raw.Orb.rep_unpack h2.1)).2 rfl⟩
  simpa using hr

end CFSG.KC.LQT.TCP

end
