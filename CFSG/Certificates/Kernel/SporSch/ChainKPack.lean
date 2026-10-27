module

public import CFSG.Certificates.Kernel.SporSch.ChainKCount
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.Mathieu
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

variable {n w : Nat}

theorem imageList_of_prep {P : Nat} {g : Equiv.Perm (Fin n)} (h : PRep n w P g) :
    imageList g = (unpack n w P).toList := by
  rw [imageList, unpack, Array.toList_ofFn]
  exact congrArg List.ofFn (funext fun i => (h i).symm)

theorem prep_inv_of_permOK {P Pi : Nat} {g : Equiv.Perm (Fin n)} (hg : PRep n w P g)
    (h : permOK n w (mask w) (n * w) P Pi = true) : PRep n w Pi g⁻¹ := by
  intro x
  have e := ((permOK_facts h).2.2 (g⁻¹ x) (g⁻¹ x).2).2
  rw [hg (g⁻¹ x)] at e
  simpa using e

theorem szOK_lt {n w : Nat} (h : szOK n w = true) : n < 2 ^ 32 := by
  have := (szOK_facts h).1
  omega

theorem mulK_rep' {g h : Equiv.Perm (Fin n)} {G H : Nat} (hsz : szOK n w = true)
    (hg : imageList g = (unpack n w G).toList) (hh : imageList h = (unpack n w H).toList) :
    imageList (g * h) = (unpack n w (pcomp n w (mask w) G H)).toList :=
  imageList_of_prep (prep_pcomp (szOK_lt hsz) (prep_of_imageList hg) (prep_of_imageList hh))

theorem invK_rep' {g : Equiv.Perm (Fin n)} {G Gi : Nat}
    (hg : imageList g = (unpack n w G).toList) (h : permOK n w (mask w) (n * w) G Gi = true) :
    imageList g⁻¹ = (unpack n w Gi).toList :=
  imageList_of_prep (prep_inv_of_permOK (prep_of_imageList hg) h)

theorem abWordK_cons (n w m idn A Ai B Bi : Nat) (z : Int) (wd : List Int) :
    abWordK n w m idn A Ai B Bi (z :: wd) = pcomp n w m
      (if icode z = 2 then A else if icode z = 3 then Ai else if icode z = 4 then B else Bi)
      (abWordK n w m idn A Ai B Bi wd) := by
  have e : abWordK n w m idn A Ai B Bi (z :: wd) = strictN (abWordK n w m idn A Ai B Bi wd)
      (fun T => strictN (icode z) (fun c => pcomp n w m (nIf(Nat.beq c (nat_lit 2), A,
        nIf(Nat.beq c (nat_lit 3), Ai, nIf(Nat.beq c (nat_lit 4), B, Bi)))) T)) := rfl
  rw [e, Orb.strictN_eq, Orb.strictN_eq]
  simp only [Orb.nIf_eq, beq_dec, decide_eq_true_eq]

theorem abOK_cons (z : Int) (wd : List Int) :
    abOK (z :: wd) = (decide (2 ≤ icode z) && decide (icode z ≤ 5) && abOK wd) := by
  have e : abOK (z :: wd) = strictB (icode z) (fun c =>
      bAnd(Nat.ble (nat_lit 2) c, bAnd(Nat.ble c (nat_lit 5), abOK wd))) := rfl
  rw [e, Orb.strictB_eq, bAnd_eq, bAnd_eq, ble_dec, ble_dec, Bool.and_assoc]

theorem abWordK_rep' {gA gB : Equiv.Perm (Fin n)} {A Ai B Bi : Nat}
    (hsz : szOK n w = true) (hA : imageList gA = (unpack n w A).toList)
    (hB : imageList gB = (unpack n w B).toList)
    (hAi : permOK n w (mask w) (n * w) A Ai = true) (hBi : permOK n w (mask w) (n * w) B Bi = true)
    {wd : List Int} (hw : abOK wd = true) :
    imageList (evalCodes [gA, gB] wd) =
      (unpack n w (abWordK n w (mask w) (pidn n w) A Ai B Bi wd)).toList := by
  have hn := szOK_lt hsz
  have pA := prep_of_imageList hA
  have pB := prep_of_imageList hB
  have pAi := prep_inv_of_permOK pA hAi
  have pBi := prep_inv_of_permOK pB hBi
  refine imageList_of_prep ?_
  induction wd with
  | nil =>
    have := szOK_facts hsz
    exact prep_pidn this.1 this.2
  | cons z wd ih =>
    rw [abOK_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨h2, h5⟩, hw⟩ := hw
    rw [abWordK_cons, evalCodes]
    refine prep_pcomp hn ?_ (ih hw)
    rcases z with k | k
    · have ec : icode (Int.ofNat k) = k + k := rfl
      rw [ec] at h2 h5 ⊢
      have hk : k = 1 ∨ k = 2 := by omega
      rcases hk with rfl | rfl
      · simpa using pA
      · simpa using pB
    · have ec : icode (Int.negSucc k) = k + 1 + (k + 1) + 1 := rfl
      rw [ec] at h2 h5 ⊢
      have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl
      · simpa using pAi
      · simpa using pBi

theorem beq_prep {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hw : 0 < w)
    (hP : PRep n w P g) (hQ : PRep n w Q h) (sP : P >>> (n * w) = 0) (sQ : Q >>> (n * w) = 0) :
    Nat.beq P Q = decide (g = h) := by
  by_cases e : g = h
  · rw [decide_eq_true e]
    have : P = Q := PF.eq_of_fields hw sP sQ fun i hi => by
      rw [hP ⟨i, hi⟩, hQ ⟨i, hi⟩, e]
    rw [this]
    exact Nat.beq_refl _
  · rw [decide_eq_false e]
    cases hb : Nat.beq P Q
    · rfl
    · rw [Nat.eq_of_beq_eq_true hb] at hP
      exact absurd (prep_unique hP hQ) e

theorem ordR_succ (n w m idn g k p : Nat) :
    ordR n w m idn g (k + 1) p = (!Nat.beq p idn && ordR n w m idn g k (pcomp n w m g p)) := by
  have e : ordR n w m idn g (k + 1) p =
      bIf(Nat.beq p idn, false, strictB (pcomp n w m g p) (ordR n w m idn g k)) := rfl
  rw [e, Orb.strictB_eq, Orb.bIf_eq]
  cases Nat.beq p idn <;> rfl

theorem ordR_spec {P : Nat} {g : Equiv.Perm (Fin n)} (hsz : szOK n w = true) (hP : PRep n w P g) :
    ∀ (k j p : Nat), PRep n w p (g ^ j) → p >>> (n * w) = 0 →
      ordR n w (mask w) (pidn n w) P k p = true →
        (∀ i < k, g ^ (j + i) ≠ 1) ∧ g ^ (j + k) = 1 := by
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have pid := prep_pidn hf.1 hf.2
  have sid := PF.pidn_shr hf.1 hf.2
  intro k
  induction k with
  | zero =>
    intro j p hp sp h
    change Nat.beq p (pidn n w) = true at h
    rw [beq_prep hw hp pid sp sid, decide_eq_true_eq] at h
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), h⟩
  | succ k ih =>
    intro j p hp sp h
    rw [ordR_succ, Bool.and_eq_true, Bool.not_eq_true', beq_prep hw hp pid sp sid,
      decide_eq_false_iff_not] at h
    have hq : PRep n w (pcomp n w (mask w) P p) (g ^ (j + 1)) := by
      rw [pow_succ']
      exact prep_pcomp hn hP hp
    obtain ⟨h1, h2⟩ := ih (j + 1) _ hq (PF.pcomp_shr _ _ hn hw) h.2
    refine ⟨fun i hi => ?_, by rwa [Nat.add_assoc, Nat.add_comm 1 k] at h2⟩
    rcases i with _ | i
    · simpa using h.1
    · have := h1 i (by omega)
      rwa [Nat.add_assoc, Nat.add_comm 1 i] at this

theorem ordIs_orderOf {g : Equiv.Perm (Fin n)} {P e : Nat} (hsz : szOK n w = true)
    (hP : PRep n w P g) (sP : P >>> (n * w) = 0) (he : 0 < e)
    (h : ordIs n w (mask w) (pidn n w) P (e - 1) = true) : orderOf g = e := by
  obtain ⟨h1, h2⟩ := ordR_spec hsz hP (e - 1) 1 P (by simpa using hP) sP h
  rw [orderOf_eq_iff he]
  refine ⟨by rwa [Nat.add_sub_cancel' he] at h2, fun m hm hm0 => ?_⟩
  have := h1 (m - 1) (by omega)
  rwa [Nat.add_sub_cancel' hm0] at this

theorem ordR_of {P : Nat} {g : Equiv.Perm (Fin n)} (hsz : szOK n w = true) (hP : PRep n w P g) :
    ∀ (k j p : Nat), PRep n w p (g ^ j) → p >>> (n * w) = 0 →
      (∀ i < k, g ^ (j + i) ≠ 1) → g ^ (j + k) = 1 →
      ordR n w (mask w) (pidn n w) P k p = true := by
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have pid := prep_pidn hf.1 hf.2
  have sid := PF.pidn_shr hf.1 hf.2
  intro k
  induction k with
  | zero =>
    intro j p hp sp _ h
    change Nat.beq p (pidn n w) = true
    rw [beq_prep hw hp pid sp sid, decide_eq_true_eq]
    simpa using h
  | succ k ih =>
    intro j p hp sp h1 h2
    rw [ordR_succ, Bool.and_eq_true, Bool.not_eq_true', beq_prep hw hp pid sp sid,
      decide_eq_false_iff_not]
    have hq : PRep n w (pcomp n w (mask w) P p) (g ^ (j + 1)) := by
      rw [pow_succ']
      exact prep_pcomp hn hP hp
    refine ⟨by simpa using h1 0 (by omega), ih (j + 1) _ hq (PF.pcomp_shr _ _ hn hw)
      (fun i hi => ?_) (by rwa [Nat.add_assoc, Nat.add_comm 1 k])⟩
    have := h1 (i + 1) (by omega)
    rwa [← Nat.add_assoc, Nat.add_right_comm] at this

theorem ordIs_eq {g : Equiv.Perm (Fin n)} {P e : Nat} (hsz : szOK n w = true)
    (hP : PRep n w P g) (sP : P >>> (n * w) = 0) (he : 0 < e) :
    ordIs n w (mask w) (pidn n w) P (e - 1) = decide (orderOf g = e) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  refine ⟨ordIs_orderOf hsz hP sP he, fun ho => ?_⟩
  refine ordR_of hsz hP (e - 1) 1 P (by simpa using hP) sP (fun i hi => ?_)
    (by rw [Nat.add_sub_cancel' he, ← ho]; exact pow_orderOf_eq_one g)
  exact pow_ne_one_of_lt_orderOf (by omega) (by omega)

theorem ordTest_of_ordIs' {g : Equiv.Perm (Fin n)} {P e : Nat} (hsz : szOK n w = true)
    (hg : imageList g = (unpack n w P).toList) (hP : canonK n w (mask w) (n * w) P = true)
    (he : 0 < e)
    (h : ordIs n w (mask w) (pidn n w) P (e - 1) = true) :
    ordTest n e (toTable g) = true :=
  (ordTest_iff perm_faithful (rep_toTable (szOK_lt hsz) g) he).2
    (ordIs_orderOf hsz (prep_of_imageList hg) (PF.canon_facts hP).2.2.1 he h)

theorem commT_of_commK' {g h : Equiv.Perm (Fin n)} {P Q : Nat}
    (hg : imageList g = (unpack n w P).toList) (hh : imageList h = (unpack n w Q).toList)
    (hc : commK n w (mask w) (n * w) P Q = true) :
    commT n (toTable g) (toTable h) = true := by
  unfold commK at hc
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨hcP, -, he⟩ := hc
  have hf := PF.canon_facts hcP
  have hn : n < 2 ^ 32 := by omega
  rw [commT_eq (rep_toTable hn g) (rep_toTable hn h), decide_eq_true_eq]
  have h1 := prep_pcomp hn (prep_of_imageList hg) (prep_of_imageList hh)
  rw [Nat.eq_of_beq_eq_true he] at h1
  exact prep_unique h1 (prep_pcomp hn (prep_of_imageList hh) (prep_of_imageList hg))

theorem powK_succ (n w m idn p e : Nat) :
    powK n w m idn p (e + 1) = pcomp n w m p (powK n w m idn p e) := by
  have h : powK n w m idn p (e + 1) = strictN (powK n w m idn p e) (fun q => pcomp n w m p q) :=
    rfl
  rw [h, Orb.strictN_eq]

theorem prep_powK {P : Nat} {g : Equiv.Perm (Fin n)} (hsz : szOK n w = true) (hP : PRep n w P g) :
    ∀ e, PRep n w (powK n w (mask w) (pidn n w) P e) (g ^ e) ∧
      powK n w (mask w) (pidn n w) P e >>> (n * w) = 0
  | 0 => by
    have hf := szOK_facts hsz
    rw [pow_zero]
    exact ⟨prep_pidn hf.1 hf.2, PF.pidn_shr hf.1 hf.2⟩
  | e + 1 => by
    have hf := szOK_facts hsz
    rw [powK_succ, pow_succ']
    exact ⟨prep_pcomp (szOK_lt hsz) hP (prep_powK hsz hP e).1,
      PF.pcomp_shr _ _ (szOK_lt hsz) (PF.w_pos hf.2)⟩

theorem xyWordK_cons (n w m idn x y xi yi l : Nat) (wd : List Nat) :
    xyWordK n w m idn x y xi yi (l :: wd) = pcomp n w m
      (if l = 0 then x else if l = 1 then y else if l = 2 then xi else yi)
      (xyWordK n w m idn x y xi yi wd) := by
  have e : xyWordK n w m idn x y xi yi (l :: wd) = strictN (xyWordK n w m idn x y xi yi wd)
      (fun T => pcomp n w m (nIf(Nat.beq l (nat_lit 0), x, nIf(Nat.beq l (nat_lit 1), y,
        nIf(Nat.beq l (nat_lit 2), xi, yi)))) T) := rfl
  rw [e, Orb.strictN_eq]
  simp only [Orb.nIf_eq, beq_dec, decide_eq_true_eq]

theorem prep_xyWordK {gA gB : Equiv.Perm (Fin n)} {A B : Nat} (hsz : szOK n w = true)
    (pA : PRep n w A gA) (pB : PRep n w B gB) (mx my : Nat) :
    ∀ wd : List Nat, PRep n w (xyWordK n w (mask w) (pidn n w) A B
        (powK n w (mask w) (pidn n w) A (mx - 1)) (powK n w (mask w) (pidn n w) B (my - 1)) wd)
        (wordElts gA gB mx my wd).prod ∧
      xyWordK n w (mask w) (pidn n w) A B
        (powK n w (mask w) (pidn n w) A (mx - 1)) (powK n w (mask w) (pidn n w) B (my - 1)) wd
        >>> (n * w) = 0
  | [] => by
    have hf := szOK_facts hsz
    have e : (wordElts gA gB mx my []).prod = 1 := by simp [wordElts]
    rw [e]
    exact ⟨prep_pidn hf.1 hf.2, PF.pidn_shr hf.1 hf.2⟩
  | l :: wd => by
    have hf := szOK_facts hsz
    have hn := szOK_lt hsz
    rw [xyWordK_cons]
    refine ⟨?_, PF.pcomp_shr _ _ hn (PF.w_pos hf.2)⟩
    have ih := (prep_xyWordK hsz pA pB mx my wd).1
    have e : (wordElts gA gB mx my (l :: wd)).prod =
        (if l = 0 then gA else if l = 1 then gB else if l = 2 then gA ^ (mx - 1)
          else gB ^ (my - 1)) * (wordElts gA gB mx my wd).prod := by
      simp only [wordElts, List.flatMap_cons, List.prod_append]
      congr 1
      split_ifs <;> simp [List.prod_replicate]
    rw [e]
    refine prep_pcomp hn ?_ ih
    split_ifs
    · exact pA
    · exact pB
    · exact (prep_powK hsz pA _).1
    · exact (prep_powK hsz pB _).1

theorem ordW_zero (n : Nat) (ts : List Table) : ordW n ts 0 = true := by
  have h1 : powFixW n ts 0 = true := by
    rw [powFixW, allIn_eq_true]
    intro i _ _
    simp [apPowW]
  have h2 : divParts 0 = [] := by decide
  rw [ordW, h1, h2]
  rfl

theorem ordE_eq {X : Nat} {x : Equiv.Perm (Fin n)} (hsz : szOK n w = true) (hX : PRep n w X x)
    (sX : X >>> (n * w) = 0) (e : Nat) :
    ordE n w (mask w) (pidn n w) X e = (decide (e = 0) || decide (orderOf x = e)) := by
  unfold ordE
  rw [Orb.bIf_eq, beq_dec]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  · simp only [he.ne', decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    exact ordIs_eq hsz hX sX he

theorem ordW_eq {ts : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) ts gs) (e : Nat) :
    ordW n ts e = (decide (e = 0) || decide (orderOf gs.prod = e)) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [ordW_zero]
  · simp only [he.ne', decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact ordW_iff perm_faithful h he

theorem wordOrdK_eq {gA gB : Equiv.Perm (Fin n)} {A B mx my : Nat}
    (ws : List (List Nat × Nat)) (hsz : szOK n w = true)
    (pA : PRep n w A gA) (pB : PRep n w B gB) :
    wordOrdK n w (mask w) (pidn n w) mx my ws A B =
      wordsTest n mx my ws (toTable gA) (toTable gB) := by
  have hn := szOK_lt hsz
  unfold wordOrdK
  rw [Orb.strictB_eq, Orb.strictB_eq, wordsTest]
  induction ws with
  | nil => rfl
  | cons q ws ih =>
    obtain ⟨wd, e⟩ := q
    have hw := prep_xyWordK hsz pA pB mx my wd
    refine (bAnd_eq _ _).trans ?_
    rw [List.all_cons]
    refine congrArg₂ (· && ·) ?_ ih
    refine (ordE_eq hsz hw.1 hw.2 e).trans ?_
    rw [ordW_eq (forall₂_wordTbls (rep_toTable hn gA) (rep_toTable hn gB) mx my wd)]

theorem wordsTest_of_wordOrdK' {gA gB : Equiv.Perm (Fin n)} {A B mx my : Nat}
    {ws : List (List Nat × Nat)} (hsz : szOK n w = true)
    (hA : imageList gA = (unpack n w A).toList) (hB : imageList gB = (unpack n w B).toList)
    (h : wordOrdK n w (mask w) (pidn n w) mx my ws A B = true) :
    wordsTest n mx my ws (toTable gA) (toTable gB) = true := by
  rwa [← wordOrdK_eq ws hsz (prep_of_imageList hA) (prep_of_imageList hB)]

end CFSG.KS.SporSch.MOC

end
