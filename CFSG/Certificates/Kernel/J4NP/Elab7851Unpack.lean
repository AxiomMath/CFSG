module

public import CFSG.Certificates.Kernel.J4NP.Elab7851Lanes
public import CFSG.Certificates.Kernel.J4Loc.SubsSound

public section

namespace CFSG.KC.J4NP

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KS.J4Loc CFSG.Sporadic.J4.QT

theorem beq_true {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ble_true {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem notB_true {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem boolRec_eq (b x y : Bool) : Bool.rec (motive := fun _ => Bool) x y b = if b then y else x := by
  cases b <;> rfl

theorem lenB_eq : ∀ B : List (List (List ℕ)), lenB B = B.length
  | [] => rfl
  | _ :: B => by
    change Nat.succ (lenB B) = _
    rw [lenB_eq B, List.length_cons]

theorem tabOK_spec {t : List ℕ} (h : tabOK t = true) : t.length = 11 ∧ ∀ x ∈ t, x < 2 ^ 11 := by
  obtain ⟨h1, h2⟩ := andB_true h
  exact ⟨by rw [← lenK_len]; exact beq_true h1, fun x hx => lt_of_blt (allL_spec h2 x hx)⟩

theorem pinGo_cons (KK : ℕ) (t : List ℕ) (TL : List (List ℕ)) (i : ℕ) :
    pinGo KK (t :: TL) i = andB (tabOK t) (Bool.rec (motive := fun _ => Bool) (pinGo KK TL i)
      (andB (Nat.beq (lnS 121 KK i) (keyT t)) (pinGo KK TL (Nat.succ i)))
      (andB (notB (eqLK t idL)) (invK t))) := by
  rw [show pinGo KK (t :: TL) i = strictB i (fun i => andB (tabOK t)
      (Bool.rec (motive := fun _ => Bool) (pinGo KK TL i)
        (andB (Nat.beq (lnS 121 KK i) (keyT t)) (pinGo KK TL (Nat.succ i)))
        (andB (notB (eqLK t idL)) (invK t)))) from rfl, strictB_eq]

theorem pinGo_spec (KK : ℕ) : ∀ (TL : List (List ℕ)) (i : ℕ), pinGo KK TL i = true →
    i ≤ 191 ∧ (∀ t ∈ TL, tabOK t = true) ∧
      ∀ t ∈ TL, andB (notB (eqLK t idL)) (invK t) = true → ∃ j, j < 191 ∧ lnS 121 KK j = keyT t
  | [], i, h => by
    refine ⟨(beq_true h).le, by simp, by simp⟩
  | t :: TL, i, h => by
    rw [pinGo_cons] at h
    obtain ⟨ht, hr⟩ := andB_true h
    rw [boolRec_eq] at hr
    split_ifs at hr with hc
    · obtain ⟨hk, hr⟩ := andB_true hr
      obtain ⟨hi, hall, hinv⟩ := pinGo_spec KK TL _ hr
      refine ⟨by omega, ?_, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ht
        · exact hall s hs
      · intro s hs hcs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨i, by omega, beq_true hk⟩
        · exact hinv s hs hcs
    · obtain ⟨hi, hall, hinv⟩ := pinGo_spec KK TL _ hr
      refine ⟨hi, ?_, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ht
        · exact hall s hs
      · intro s hs hcs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact absurd hcs (by simpa using hc)
        · exact hinv s hs hcs

theorem idL_eq : idL = idT := by decide

theorem pin_inv {KK : ℕ} {TL : List (List ℕ)} (hTL : tabL = TL) (h : pinOK KK TL = true) :
    ∀ t ∈ tabL, t ≠ idT → compT t t = idT → ∃ i < 191, ivt KK i = t := by
  intro t ht hne hinv
  rw [hTL] at ht
  obtain ⟨-, hall, hk⟩ := pinGo_spec KK TL 0 h
  obtain ⟨hl, hlt⟩ := tabOK_spec (hall t ht)
  have hc : andB (notB (eqLK t idL)) (invK t) = true := by
    rw [andB_eq, (invK_iff hl).mpr hinv, Bool.and_true, notB_eq]
    cases he : eqLK t idL
    · rfl
    · exact absurd (by rw [eqLK_spec he, idL_eq]) hne
  obtain ⟨j, hj, hjk⟩ := hk t ht hc
  exact ⟨j, hj, by rw [ivt_eq, hjk, dec_keyT hl hlt]⟩

theorem pairOK_spec {KK Ka Ca Pa x : ℕ} (h : pairOK KK Ka Ca Pa x = true) :
    Ka ≠ lnS 121 KK x ∧ (Ca.testBit x = true →
      prodK Ka (lnS 121 KK x) = prodK (lnS 121 KK x) Ka ∧ fld 8 Pa x < 191 ∧
        lnS 121 KK (fld 8 Pa x) = prodK Ka (lnS 121 KK x)) ∧
      (Ca.testBit x = false → prodK Ka (lnS 121 KK x) ≠ prodK (lnS 121 KK x) Ka) := by
  unfold pairOK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  rw [boolRec_eq, bitB_eq] at h2
  refine ⟨fun e => by rw [e, notB_eq] at h1; simp at h1, fun hb => ?_, fun hb => ?_⟩
  · rw [if_pos hb] at h2
    obtain ⟨h3, h4⟩ := andB_true h2
    obtain ⟨h5, h6⟩ := andB_true h4
    exact ⟨beq_true h3, lt_of_blt h5, beq_true h6⟩
  · rw [hb, if_neg (by decide)] at h2
    intro e
    rw [e, notB_eq] at h2
    simp at h2

theorem rowOK_spec {KK CMK PRK FMK XP : ℕ} {FL : List (List ℕ)} {a : ℕ}
    (h : rowOK KK CMK PRK FMK XP FL a = true) :
    (lnS 191 CMK a).testBit a = false ∧ lnS 2048 FMK a = fixK XP (lnS 121 KK a) ∧
      subK (lnS 2048 FMK a) (keyK (rowL FL a)) = true ∧ (rowL FL a).length ≤ 128 ∧
      ∀ x < 191, x ≠ a → pairOK KK (lnS 121 KK a) (lnS 191 CMK a) (lnS 1528 PRK a) x = true := by
  unfold rowOK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h4
  obtain ⟨h7, h8⟩ := andB_true h6
  refine ⟨by rw [← bitB_eq]; exact notB_true h1, beq_true h3, h5,
    by rw [← lenK_len]; exact ble_true h7, fun x hx hxa => ?_⟩
  rcases orB_true (allR_spec h8 x hx) with e | e
  · exact absurd (beq_true e) hxa
  · exact e

theorem descK_spec : ∀ (L : List ℕ) (ub : ℕ), descK L ub = true →
    L.Pairwise (· > ·) ∧ ∀ p ∈ L, p < ub
  | [], _, _ => by simp
  | x :: L, ub, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨hp, hlt⟩ := descK_spec L x h2
    have hx := lt_of_blt h1
    refine ⟨List.pairwise_cons.mpr ⟨fun p hp => hlt p hp, hp⟩, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hx
    · exact (hlt p hp).trans hx

theorem testBit_caK (CMK x : ℕ) : ∀ L : List ℕ, (caK CMK L).testBit x = true ↔
    x < 191 ∧ ∀ a ∈ L, (lnS 191 CMK a).testBit x = true
  | [] => by
    change (onesK 191).testBit x = true ↔ _
    rw [testBit_onesK]
    simp
  | a :: L => by
    change (caK CMK L &&& lnS 191 CMK a).testBit x = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, testBit_caK CMK x L]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem testBit_chMask (x : ℕ) : ∀ Ch : List ℕ, (chMask Ch).testBit x = true ↔
    ∃ c ∈ Ch, c &&& 255 = x
  | [] => by simp [chMask]
  | c :: Ch => by
    change (chMask Ch ||| 1 <<< (c &&& 255)).testBit x = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_chMask x Ch, decide_eq_true_iff]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

theorem testBit_imgK (Px p : ℕ) : ∀ L : List ℕ, (imgK Px L).testBit p = true ↔
    ∃ a ∈ L, fld 8 Px a = p
  | [] => by simp [imgK]
  | a :: L => by
    change (imgK Px L ||| 1 <<< fld 8 Px a).testBit p = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_imgK Px p L, decide_eq_true_iff]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

theorem testBit_andG (FMK c : ℕ) : ∀ G : List ℕ, (andG FMK G).testBit c = true ↔
    c < 2048 ∧ ∀ g ∈ G, (lnS 2048 FMK g).testBit c = true
  | [] => by
    change (onesK 2048).testBit c = true ↔ _
    rw [testBit_onesK]
    simp
  | g :: G => by
    change (andG FMK G &&& lnS 2048 FMK g).testBit c = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, testBit_andG FMK c G]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem testBit_above (C x : ℕ) (L : List ℕ) (hx : ∀ a ∈ L, a < x) (hC : C.testBit x = true) :
    (C - (C &&& lowK L)).testBit x = true := by
  cases L with
  | nil =>
    change (C - (C &&& 0)).testBit x = true
    simpa using hC
  | cons h L =>
    have hh := hx h (by simp)
    change (C - (C &&& onesK (h + 1))).testBit x = true
    have e1 : C &&& onesK (h + 1) = C % 2 ^ (h + 1) := by
      change C &&& (1 <<< (h + 1) - 1) = _
      rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
    have e2 : C - C % 2 ^ (h + 1) = (C >>> (h + 1)) <<< (h + 1) := by
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      have := Nat.div_add_mod C (2 ^ (h + 1))
      rw [Nat.mul_comm]
      omega
    rw [e1, e2, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, show h + 1 + (x - (h + 1)) = x by omega]
    simp [hC, show x ≥ h + 1 by omega]

theorem entOK_spec {MK CMK PRK FMK N i : ℕ} {R : List (List ℕ)}
    (h : entOK MK CMK PRK FMK N i R = true) :
    (∀ p, (lnS 191 MK i).testBit p = true ↔ p ∈ rowL R 0) ∧ (rowL R 0).Pairwise (· > ·) ∧
      (∀ p ∈ rowL R 0, p < 191) ∧
      (∀ x < 191, (∀ a ∈ rowL R 0, a < x ∧ (lnS 191 CMK a).testBit x = true) →
        ∃ j < N, ∀ p, (lnS 191 MK j).testBit p = true ↔
          (p ∈ rowL R 0 ∨ p = x ∨ ∃ a ∈ rowL R 0, fld 8 (lnS 1528 PRK x) a = p)) ∧
      bndOK FMK (lnS 191 MK i) (rowL R 0) (rowL R 2) (rowL R 3) = true := by
  unfold entOK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h4
  have hm := beq_true h1
  have hbits : ∀ p, (lnS 191 MK i).testBit p = true ↔ p ∈ rowL R 0 := fun p => by
    rw [hm, mem_keyK]
  obtain ⟨hpw, hlt⟩ := descK_spec _ _ h3
  refine ⟨hbits, hpw, hlt, fun x hx hxL => ?_, h6⟩
  unfold chOK at h5
  simp only [strictB_eq] at h5
  obtain ⟨h7, h8⟩ := andB_true h5
  have hC : (caK CMK (rowL R 0)).testBit x = true :=
    (testBit_caK CMK x _).mpr ⟨hx, fun a ha => (hxL a ha).2⟩
  have hab := testBit_above _ x (rowL R 0) (fun a ha => (hxL a ha).1) hC
  have h7' : chMask (rowL R 1) = caK CMK (rowL R 0) - (caK CMK (rowL R 0) &&& lowK (rowL R 0)) :=
    beq_true h7
  rw [← h7', testBit_chMask] at hab
  obtain ⟨c, hc, hcx⟩ := hab
  have hch := allL_spec h8 c hc
  unfold childOK at hch
  simp only [strictB_eq] at hch
  obtain ⟨h9, h10⟩ := andB_true hch
  refine ⟨c >>> 8, lt_of_blt h9, fun p => ?_⟩
  have h10' : lnS 191 MK (c >>> 8) =
      (lnS 191 MK i ||| 1 <<< (c &&& 255)) ||| imgK (lnS 1528 PRK (c &&& 255)) (rowL R 0) :=
    beq_true h10
  rw [h10', hcx, Nat.testBit_or, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    Bool.or_eq_true, hbits, testBit_imgK, decide_eq_true_iff]
  constructor
  · rintro ((h | rfl) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h)
  · rintro (h | rfl | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr h

theorem entGo_spec {MK CMK PRK FMK N : ℕ} : ∀ (B : List (List (List ℕ))) (s : ℕ),
    entGo MK CMK PRK FMK N B s = true → ∀ r < B.length, s + r < N →
      entOK MK CMK PRK FMK N (s + r) (B.getD r []) = true
  | [], _, _ => by simp
  | R :: B, s, h => by
    have e : entGo MK CMK PRK FMK N (R :: B) s =
        andB (orB (notB (Nat.blt s N)) (entOK MK CMK PRK FMK N s R))
          (entGo MK CMK PRK FMK N B (Nat.succ s)) := by
      rw [show entGo MK CMK PRK FMK N (R :: B) s = strictB s (fun i =>
        andB (orB (notB (Nat.blt i N)) (entOK MK CMK PRK FMK N i R))
          (entGo MK CMK PRK FMK N B (Nat.succ i))) from rfl, strictB_eq]
    rw [e] at h
    obtain ⟨h1, h2⟩ := andB_true h
    intro r hr hrN
    cases r with
    | zero =>
      rcases orB_true h1 with h3 | h3
      · have := notB_true h3
        rw [Nat.blt_eq.mpr (by omega)] at this
        exact absurd this (by decide)
      · simpa using h3
    | succ r =>
      have := entGo_spec B (Nat.succ s) h2 r (by simpa using hr) (by omega)
      rw [show s + (r + 1) = Nat.succ s + r by omega]
      simpa using this

theorem ent_ok {MK CMK PRK FMK : ℕ} {ENT : List (List (List (List ℕ)))}
    (hents : ∀ k < 235, entBlk MK CMK PRK FMK 7507 ENT k = true) {i : ℕ} (hi : i < 7507) :
    entOK MK CMK PRK FMK 7507 i (blkL (blk4 ENT (i / 32)) (i % 32)) = true := by
  have hk : i / 32 < 235 := by omega
  have h := hents _ hk
  unfold entBlk at h
  obtain ⟨h1, h2⟩ := andB_true h
  rw [lenB_eq] at h1
  have hr : i % 32 < (blk4 ENT (i / 32)).length := by
    rcases orB_true h1 with h3 | h3
    · rw [beq_true h3]
      exact Nat.mod_lt _ (by norm_num)
    · have := ble_true h3
      change 7507 ≤ 32 * (i / 32) + _ at this
      omega
  have := entGo_spec _ _ h2 (i % 32) hr (by change 32 * (i / 32) + i % 32 < 7507; omega)
  rw [blkL_eq]
  change entOK MK CMK PRK FMK 7507 (32 * (i / 32) + i % 32) _ = true at this
  rwa [Nat.div_add_mod] at this

theorem facts_of_checks {TL : List (List ℕ)} {KK CMK PRK FMK XP MK : ℕ}
    {FL : List (List ℕ)} {ENT : List (List (List (List ℕ)))} (hTL : tabL = TL)
    (hpin : pinOK KK TL = true) (hxp : xpOK XP = true) (hroot : Nat.beq (lnS 191 MK 0) 0 = true)
    (hrows : ∀ a < 191, rowOK KK CMK PRK FMK XP FL a = true)
    (hents : ∀ k < 235, entBlk MK CMK PRK FMK 7507 ENT k = true) :
    Facts7851 KK CMK PRK FMK MK ENT := by
  have hXP : ∀ j < 11, lnS 2048 XP j = planeK j := fun j hj => beq_true (allR_spec hxp j hj)
  have hK : ∀ i, lnS 121 KK i < 2 ^ 121 := fun i => lnS_lt _ _ _
  refine ⟨fun i _ => lenOK_dec _, ?_, pin_inv hTL hpin, ?_, ?_, ?_, ?_, beq_true hroot, ?_, ?_, ?_⟩
  · intro i hi j hj h
    by_contra hne
    obtain ⟨-, -, -, -, hpair⟩ := rowOK_spec (hrows i hi)
    exact (pairOK_spec (hpair j hj (Ne.symm hne))).1 (dec_inj (hK i) (hK j) h)
  · intro a ha x hx hax hcomm
    obtain ⟨-, -, -, -, hpair⟩ := rowOK_spec (hrows a ha)
    obtain ⟨-, -, h0⟩ := pairOK_spec (hpair x hx (Ne.symm hax))
    cases hb : (lnS 191 CMK a).testBit x
    · refine absurd ?_ (h0 hb)
      apply dec_inj (prodK_lt _ _) (prodK_lt _ _)
      rw [dec_prodK, dec_prodK]
      exact hcomm
    · rfl
  · intro a ha x hx hax hb
    obtain ⟨-, -, -, -, hpair⟩ := rowOK_spec (hrows a ha)
    obtain ⟨-, h1, -⟩ := pairOK_spec (hpair x hx (Ne.symm hax))
    obtain ⟨-, hp, hkey⟩ := h1 hb
    refine ⟨hp, ?_⟩
    simp only [ivt_eq]
    rw [hkey, dec_prodK]
  · intro a ha c hc
    obtain ⟨-, hfm, -⟩ := rowOK_spec (hrows a ha)
    rw [hfm, fixK_spec hXP _ hc]
    rfl
  · intro a ha
    obtain ⟨-, hfm, hsub, hlen, -⟩ := rowOK_spec (hrows a ha)
    refine ⟨rowL FL a, hlen, fun c hc hfix => ?_⟩
    have hbit : (lnS 2048 FMK a).testBit c = true := by
      rw [hfm, fixK_spec hXP _ hc]
      exact hfix
    exact (mem_keyK c _).mp (subK_spec hsub c hbit)
  · intro i hi
    obtain ⟨hbits, hpw, -, -, -⟩ := entOK_spec (ent_ok hents hi)
    exact ⟨hbits, hpw.imp fun h => Nat.ne_of_gt h⟩
  · intro i hi x hx hxL
    obtain ⟨-, -, -, hch, -⟩ := entOK_spec (ent_ok hents hi)
    exact hch x hx hxL
  · intro i hi hne
    obtain ⟨hbits, -, hlt, -, hb⟩ := entOK_spec (ent_ok hents hi)
    unfold bndOK at hb
    rcases orB_true hb with h | h
    · left
      rw [← lenK_len]
      exact ble_true h
    · right
      obtain ⟨h1, h2⟩ := andB_true h
      obtain ⟨h3, h4⟩ := andB_true h2
      refine ⟨rowL (blkL (blk4 ENT (i / 32)) (i % 32)) 2, rowL (blkL (blk4 ENT (i / 32)) (i % 32)) 3,
        fun g hg => ?_, fun c hc hall => ?_, ?_⟩
      · have hgL := (hbits g).mp (by rw [← bitB_eq]; exact allL_spec h1 g hg)
        exact ⟨hgL, hlt g hgL⟩
      · exact (mem_keyK c _).mp (subK_spec h3 c ((testBit_andG FMK c _).mpr ⟨hc, hall⟩))
      · have := ble_true h4
        rw [lenK_len, lenK_len] at this
        exact this

end CFSG.KC.J4NP

end
