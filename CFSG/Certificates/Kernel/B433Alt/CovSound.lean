module

public import Certificates.Data.Kernel.B433Alt.Om
public import Certificates.Data.Kernel.B433Alt.Trace
public import CFSG.YGroups.Defs

public section

namespace CFSG.KC.B433Alt

open CFSG.YGroups CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

private theorem covS_sN (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

private theorem covS_sB (v : ℕ) (k : ℕ → Bool) : B4A.sB v k = k v := by cases v <;> rfl

private theorem covS_andB {a b : Bool} (h : B4A.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [B4A.andB]

private theorem covS_brec {F T b : Bool} (h : Bool.rec (motive := fun _ => Bool) F T b = true) :
    (b = true → T = true) ∧ (b = false → F = true) := by
  cases b
  · exact ⟨fun h' => (Bool.false_ne_true h').elim, fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => (Bool.false_ne_true h'.symm).elim⟩

private theorem covS_recAll {P : ℕ → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun s acc => B4A.andB acc (P s)) m = true →
      ∀ s < m, P s = true
  | 0, _, s, hs => absurd hs (Nat.not_lt_zero s)
  | m + 1, h, s, hs => by
    obtain ⟨h1, h2⟩ := covS_andB h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hlt | rfl
    · exact covS_recAll m h1 s hlt
    · exact h2

private theorem covS_wAt_lt {w : ℕ} (hw : wInH w = true) : ∀ i < wLen w, wAt w i < 10 := by
  intro i hi
  have h := covS_recAll (P := fun i => Nat.blt (wAt w i) 10) (wLen w)
    (covS_andB (show B4A.andB (wOK w) (wAllLt w 10) = true from hw)).2 i hi
  exact Nat.blt_eq.mp h

private theorem covS_fld_zero (L m : ℕ) : fld L (20 * 0) m = L &&& m := by
  show (L >>> (20 * 0)) &&& m = L &&& m
  rw [Nat.mul_zero, Nat.shiftRight_zero]

private theorem covS_fld_succ (L i m : ℕ) : fld L (20 * (i + 1)) m = fld (L >>> 20) (20 * i) m := by
  show (L >>> (20 * (i + 1))) &&& m = ((L >>> 20) >>> (20 * i)) &&& m
  rw [← Nat.shiftRight_add, show 20 * (i + 1) = 20 + 20 * i by ring]

private noncomputable def covS_suf (w p : ℕ) : YGroup 4 3 2 :=
  evalWord (yGen 4 3 2) ((List.range' p (wLen w - p)).map (wAt w))

private theorem covS_suf_len (w : ℕ) : covS_suf w (wLen w) = 1 := by
  unfold covS_suf
  rw [Nat.sub_self]
  rfl

private theorem covS_suf_succ (w p : ℕ) (hp : p < wLen w) :
    covS_suf w p = yGen 4 3 2 (wAt w p) * covS_suf w (p + 1) := by
  unfold covS_suf
  rw [show wLen w - p = wLen w - (p + 1) + 1 by omega, List.range'_succ, List.map_cons,
    evalWord_cons]

private theorem covS_suf_zero (w : ℕ) : covS_suf w 0 = evalWord (yGen 4 3 2) (wList w) := by
  unfold covS_suf wList
  rw [Nat.sub_zero, List.range_eq_range']

private theorem covS_image_mul (σ τ : Equiv.Perm (Fin 412896)) (S : Set (Fin 412896)) :
    (σ * τ) '' S = σ '' (τ '' S) := by
  rw [Equiv.Perm.coe_mul, Set.image_comp]

private theorem covS_walkId (ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896)) {CB : ℕ → ℕ}
    (hcol : ∀ c < 10, ∀ x : Fin 412896, (ρΩ (yGen 4 3 2 c) x : ℕ) = colAt CB c x)
    {w : ℕ} (hl : ∀ i < wLen w, wAt w i < 10) :
    walkId CB w = (ρΩ (evalWord (yGen 4 3 2) (wList w)) 0 : ℕ) := by
  have key : ∀ m, m ≤ wLen w →
      Nat.rec (motive := fun _ => ℕ) 0
        (fun i acc => sN acc (fun x => colAt CB (wAt w (wLen w - 1 - i)) x)) m =
      (ρΩ (covS_suf w (wLen w - m)) 0 : ℕ) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, covS_suf_len, map_one, Equiv.Perm.one_apply]
      rfl
    | succ m ih =>
      intro hm
      rw [show Nat.rec (motive := fun _ => ℕ) 0
          (fun i acc => sN acc (fun x => colAt CB (wAt w (wLen w - 1 - i)) x)) (m + 1) =
          colAt CB (wAt w (wLen w - 1 - m)) (Nat.rec (motive := fun _ => ℕ) 0
            (fun i acc => sN acc (fun x => colAt CB (wAt w (wLen w - 1 - i)) x)) m) from
          covS_sN _ _,
        ih (by omega), ← hcol (wAt w (wLen w - 1 - m)) (hl _ (by omega)),
        covS_suf_succ w (wLen w - (m + 1)) (by omega),
        show wLen w - (m + 1) + 1 = wLen w - m by omega,
        show wLen w - (m + 1) = wLen w - 1 - m by omega, map_mul, Equiv.Perm.mul_apply]
  have h := key (wLen w) le_rfl
  rw [Nat.sub_self, covS_suf_zero] at h
  rw [← h]
  exact covS_sN _ _

private noncomputable def covS_rs (RD PW CB : ℕ → ℕ) (LIVE j : ℕ) (n : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc => sN (Nat.land L (ones (nat_lit 20))) (fun e =>
      Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (sN (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (walkId CB (PW (dPt (RD e)))))) (fun a =>
          ih (Nat.shiftRight L (nat_lit 20)) a))
        (entryOK RD LIVE j e)))
    n

private theorem covS_rs_succ (RD PW CB : ℕ → ℕ) (LIVE j n L acc : ℕ) :
    covS_rs RD PW CB LIVE j (n + 1) L acc =
      Bool.rec (motive := fun _ => ℕ) 0
        (covS_rs RD PW CB LIVE j n (L >>> 20)
          (acc ||| 1 <<< walkId CB (PW (dPt (RD (L &&& ones 20))))))
        (entryOK RD LIVE j (L &&& ones 20)) := by
  have e1 : covS_rs RD PW CB LIVE j (n + 1) L acc = sN (L &&& ones 20) (fun e =>
      Bool.rec (motive := fun _ => ℕ) 0
        (sN (acc ||| 1 <<< walkId CB (PW (dPt (RD e)))) (fun a =>
          covS_rs RD PW CB LIVE j n (L >>> 20) a))
        (entryOK RD LIVE j e)) := rfl
  rw [e1, covS_sN, covS_sN]

private theorem covS_rs_spec (RD PW CB : ℕ → ℕ) (LIVE j : ℕ) : ∀ n L acc x,
    (covS_rs RD PW CB LIVE j n L acc).testBit x = true →
      acc.testBit x = true ∨ ∃ i < n, entryOK RD LIVE j (fld L (20 * i) (ones 20)) = true ∧
        x = walkId CB (PW (dPt (RD (fld L (20 * i) (ones 20)))))
  | 0, _, _, _, h => Or.inl h
  | n + 1, L, acc, x, h => by
    rw [covS_rs_succ] at h
    cases hok : entryOK RD LIVE j (L &&& ones 20)
    · rw [hok] at h
      have h0 : (0 : ℕ).testBit x = true := h
      rw [Nat.zero_testBit] at h0
      exact absurd h0 Bool.false_ne_true
    · rw [hok] at h
      rcases covS_rs_spec RD PW CB LIVE j n (L >>> 20) _ x h with h1 | ⟨i, hi, hoki, hx⟩
      · rw [Nat.testBit_or, Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h1
          refine Or.inr ⟨0, Nat.zero_lt_succ n, ?_, ?_⟩
          · rw [covS_fld_zero]; exact hok
          · rw [covS_fld_zero]; exact h1.symm
      · refine Or.inr ⟨i + 1, Nat.succ_lt_succ hi, ?_, ?_⟩
        · rw [covS_fld_succ]; exact hoki
        · rw [covS_fld_succ]; exact hx

private theorem covS_appSeg_zero (MS : ℕ → ℕ) (w a X : ℕ) : appSeg19 MS w a 0 X = X := by
  unfold appSeg19
  exact covS_sN _ _

private theorem covS_appSeg_succ (MS : ℕ → ℕ) (w a n X : ℕ) :
    appSeg19 MS w a (n + 1) X =
      netApp19 MS (wAt w (wLen w - 1 - (a + n))) (appSeg19 MS w a n X) := by
  unfold appSeg19
  rw [covS_sN, covS_sN]
  exact covS_sN _ _

private theorem covS_appSeg (ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896)) {MS : ℕ → ℕ}
    (hnet : ∀ c < 10, ∀ E < 2 ^ 412896, netApp19 MS c E < 2 ^ 412896 ∧
      {x : Fin 412896 | (netApp19 MS c E).testBit x = true} =
        ρΩ (yGen 4 3 2 c) '' {x : Fin 412896 | E.testBit x = true})
    {w a : ℕ} (hl : ∀ i < wLen w, wAt w i < 10) (S : Set (Fin 412896)) {X : ℕ}
    (hX : X < 2 ^ 412896)
    (hXS : {x : Fin 412896 | X.testBit x = true} = ρΩ (covS_suf w (wLen w - a)) '' S) :
    ∀ n, a + n ≤ wLen w → appSeg19 MS w a n X < 2 ^ 412896 ∧
      {x : Fin 412896 | (appSeg19 MS w a n X).testBit x = true} =
        ρΩ (covS_suf w (wLen w - (a + n))) '' S
  | 0, _ => by rw [covS_appSeg_zero, Nat.add_zero]; exact ⟨hX, hXS⟩
  | n + 1, h => by
    obtain ⟨hb, hs⟩ := covS_appSeg ρΩ hnet hl S hX hXS n (by omega)
    obtain ⟨hb', hs'⟩ := hnet _ (hl (wLen w - 1 - (a + n)) (by omega)) _ hb
    rw [covS_appSeg_succ]
    refine ⟨hb', ?_⟩
    rw [hs', hs, ← covS_image_mul, ← map_mul ρΩ,
      covS_suf_succ w (wLen w - (a + (n + 1))) (by omega),
      show wLen w - (a + (n + 1)) + 1 = wLen w - (a + n) by omega,
      show wLen w - (a + (n + 1)) = wLen w - 1 - (a + n) by omega]

private theorem covS_genOK {RD : ℕ → ℕ} {j g : ℕ} (h : genOK RD j g = true) :
    isStab (dKind (RD g)) = true := by
  unfold genOK at h
  rw [covS_sB] at h
  exact (covS_andB h).1

private theorem covS_segChk {MS RD RW PW CB RN RL GS XO SJ ST SA SN STL : ℕ → ℕ} {LIVE NS k : ℕ}
    (h : segChk MS RD RW PW CB LIVE RN RL GS XO SJ ST SA SN STL NS k = true) :
    genOK RD (SJ k) (genOf GS (SJ k) (ST k)) = true ∧
    SA k + SN k ≤ wLen (RW (genOf GS (SJ k) (ST k))) ∧
    (SA k = 0 → appSeg19 MS (RW (genOf GS (SJ k) (ST k))) 0 (SN k)
        (eOf RD PW CB LIVE RN RL XO STL (SJ k) (ST k)) = XO k) ∧
    (SA k ≠ 0 → SJ (k - 1) = SJ k ∧ ST (k - 1) = ST k ∧ SA (k - 1) + SN (k - 1) = SA k ∧
      appSeg19 MS (RW (genOf GS (SJ k) (ST k))) (SA k) (SN k) (XO (k - 1)) = XO k) := by
  unfold segChk at h
  simp only [covS_sB] at h
  obtain ⟨-, h⟩ := covS_andB h
  obtain ⟨hg, h⟩ := covS_andB h
  obtain ⟨hle, h⟩ := covS_andB h
  have hb := covS_brec h
  refine ⟨hg, Nat.le_of_ble_eq_true hle, fun ha => Nat.eq_of_beq_eq_true (hb.1 ?_), fun ha => ?_⟩
  · rw [ha]; rfl
  · have hf : Nat.beq (SA k) 0 = false := by
      cases hc : Nat.beq (SA k) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc) ha
    obtain ⟨c1, h⟩ := covS_andB (hb.2 hf)
    obtain ⟨c2, h⟩ := covS_andB h
    obtain ⟨c3, c4⟩ := covS_andB h
    exact ⟨Nat.eq_of_beq_eq_true c1, Nat.eq_of_beq_eq_true c2, Nat.eq_of_beq_eq_true c3,
      Nat.eq_of_beq_eq_true c4⟩

private theorem covS_finChk {RD RW PW CB RN RL GS GN XO SJ ST SA SN STL : ℕ → ℕ} {LIVE NS j : ℕ}
    (h : finChk RD RW PW CB LIVE RN RL GS GN XO SJ ST SA SN STL NS j = true)
    (hlive : 0 < LIVE &&& (1 <<< j)) :
    eOf RD PW CB LIVE RN RL XO STL j (GN j) = omAll ∧
    ∀ s < GN j, STL (128 * j + s) < NS ∧ SJ (STL (128 * j + s)) = j ∧ ST (STL (128 * j + s)) = s ∧
      SA (STL (128 * j + s)) + SN (STL (128 * j + s)) = wLen (RW (genOf GS j s)) := by
  unfold finChk at h
  obtain ⟨h1, h2⟩ := covS_andB ((covS_brec h).1 (Nat.blt_eq.mpr hlive))
  refine ⟨Nat.eq_of_beq_eq_true h1, fun s hs => ?_⟩
  have h3 := covS_recAll _ h2 s hs
  rw [covS_sB] at h3
  obtain ⟨a1, a2⟩ := covS_andB h3
  obtain ⟨b1, b2⟩ := covS_andB a2
  obtain ⟨c1, c2⟩ := covS_andB b2
  exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true b1, Nat.eq_of_beq_eq_true c1,
    Nat.eq_of_beq_eq_true c2⟩

private theorem covS_eOf_succ (RD PW CB : ℕ → ℕ) (LIVE : ℕ) (RN RL XO STL : ℕ → ℕ) (j s : ℕ) :
    eOf RD PW CB LIVE RN RL XO STL j (s + 1) =
      eOf RD PW CB LIVE RN RL XO STL j s ||| XO (STL (128 * j + s)) := rfl

private theorem covS_eOf_mono (RD PW CB : ℕ → ℕ) (LIVE : ℕ) (RN RL XO STL : ℕ → ℕ) (j s : ℕ) :
    ∀ m, s ≤ m → eOf RD PW CB LIVE RN RL XO STL j s ≤ eOf RD PW CB LIVE RN RL XO STL j m
  | 0, h => by rw [Nat.le_zero.1 h]
  | m + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact (covS_eOf_mono RD PW CB LIVE RN RL XO STL j s m (by omega)).trans
        (by rw [covS_eOf_succ]; exact Nat.left_le_or)
    · rw [h]

private theorem covS_ones_eq (n : ℕ) : ones n = 2 ^ n - 1 := by
  show (1 <<< n) - 1 = 2 ^ n - 1
  rw [Nat.one_shiftLeft]

private theorem covS_ones_lt (n : ℕ) : ones n < 2 ^ n := by
  rw [covS_ones_eq]
  exact Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos

private theorem covS_ones_testBit {n i : ℕ} (h : i < n) : (ones n).testBit i = true := by
  rw [covS_ones_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true h

private theorem covS_seg (ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896))
    {MS RD RW PW CB RN RL GS XO SJ ST SA SN STL : ℕ → ℕ} {LIVE NS : ℕ}
    (hrw : ∀ g, isStab (dKind (RD g)) = true → wInH (RW g) = true)
    (hnet : ∀ c < 10, ∀ E < 2 ^ 412896, netApp19 MS c E < 2 ^ 412896 ∧
      {x : Fin 412896 | (netApp19 MS c E).testBit x = true} =
        ρΩ (yGen 4 3 2 c) '' {x : Fin 412896 | E.testBit x = true})
    (hsa0 : SA 0 = 0)
    (hseg : ∀ k < NS, segChk MS RD RW PW CB LIVE RN RL GS XO SJ ST SA SN STL NS k = true)
    {j s : ℕ} (hE : eOf RD PW CB LIVE RN RL XO STL j s < 2 ^ 412896) (k : ℕ) :
    k < NS → SJ k = j → ST k = s →
      XO k < 2 ^ 412896 ∧
      {x : Fin 412896 | (XO k).testBit x = true} =
        ρΩ (covS_suf (RW (genOf GS j s)) (wLen (RW (genOf GS j s)) - (SA k + SN k))) ''
          {x : Fin 412896 | (eOf RD PW CB LIVE RN RL XO STL j s).testBit x = true} := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hj hs
    obtain ⟨hgen, hle, h0, h1⟩ := covS_segChk (hseg k hk)
    rw [hj, hs] at hgen hle h0 h1
    have hl := covS_wAt_lt (hrw _ (covS_genOK hgen))
    by_cases ha : SA k = 0
    · have hS : {x : Fin 412896 | (eOf RD PW CB LIVE RN RL XO STL j s).testBit x = true} =
          ρΩ (covS_suf (RW (genOf GS j s)) (wLen (RW (genOf GS j s)) - 0)) ''
            {x : Fin 412896 | (eOf RD PW CB LIVE RN RL XO STL j s).testBit x = true} := by
        rw [Nat.sub_zero, covS_suf_len, map_one, Equiv.Perm.coe_one, Set.image_id]
      have := covS_appSeg ρΩ hnet hl _ hE hS (SN k) (by omega)
      rw [h0 ha] at this
      rw [ha]
      exact this
    · have hk0 : k ≠ 0 := by rintro rfl; exact ha hsa0
      obtain ⟨hj', hs', hlen', happ⟩ := h1 ha
      obtain ⟨hb, hset⟩ := ih (k - 1) (by omega) (by omega) hj' hs'
      rw [hlen'] at hset
      have := covS_appSeg ρΩ hnet hl _ hb hset (SN k) hle
      rw [happ] at this
      exact this

theorem cover_sound_aux {MS RD RW PW CB RN RL GS GN XO SJ ST SA SN STL : ℕ → ℕ} {LIVE NS j : ℕ}
    (ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896))
    (hrw : ∀ g, isStab (dKind (RD g)) = true → wInH (RW g) = true)
    (hpw : ∀ p, wInH (PW p) = true)
    (hcol : ∀ c < 10, ∀ x : Fin 412896, (ρΩ (yGen 4 3 2 c) x : ℕ) = colAt CB c x)
    (hnet : ∀ c < 10, ∀ E < 2 ^ 412896, netApp19 MS c E < 2 ^ 412896 ∧
      {x : Fin 412896 | (netApp19 MS c E).testBit x = true} =
        ρΩ (yGen 4 3 2 c) '' {x : Fin 412896 | E.testBit x = true})
    (hsa0 : SA 0 = 0)
    (hseg : ∀ k < NS, segChk MS RD RW PW CB LIVE RN RL GS XO SJ ST SA SN STL NS k = true)
    (hfin : finChk RD RW PW CB LIVE RN RL GS GN XO SJ ST SA SN STL NS j = true)
    (hlive : 0 < LIVE &&& (1 <<< j)) :
    ∀ x : Fin 412896, ∃ i < RN j, entryOK RD LIVE j (fld (RL j) (20 * i) (ones 20)) = true ∧
      ∃ s ∈ Subgroup.closure ((fun t => ρΩ (evalWord (yGen 4 3 2) (wList (RW (genOf GS j t))))) ''
          {t | t < GN j}),
        x = s (ρΩ (evalWord (yGen 4 3 2)
          (wList (PW (dPt (RD (fld (RL j) (20 * i) (ones 20))))))) 0) := by
  obtain ⟨hall, hlast⟩ := covS_finChk hfin hlive
  have hEb : ∀ s ≤ GN j, eOf RD PW CB LIVE RN RL XO STL j s < 2 ^ 412896 := fun s hs =>
    lt_of_le_of_lt (covS_eOf_mono RD PW CB LIVE RN RL XO STL j s (GN j) hs)
      (hall.trans_lt (covS_ones_lt 412896))
  have hcov : ∀ s ≤ GN j, ∀ x : Fin 412896,
      (eOf RD PW CB LIVE RN RL XO STL j s).testBit x = true →
      ∃ i < RN j, entryOK RD LIVE j (fld (RL j) (20 * i) (ones 20)) = true ∧
        ∃ σ ∈ Subgroup.closure ((fun t => ρΩ (evalWord (yGen 4 3 2) (wList (RW (genOf GS j t))))) ''
            {t | t < GN j}),
          x = σ (ρΩ (evalWord (yGen 4 3 2)
            (wList (PW (dPt (RD (fld (RL j) (20 * i) (ones 20))))))) 0) := by
    intro s
    induction s with
    | zero =>
      intro _ x hx
      rcases covS_rs_spec RD PW CB LIVE j (RN j) (RL j) 0 x hx with h | ⟨i, hi, hok, hxw⟩
      · rw [Nat.zero_testBit] at h
        exact absurd h Bool.false_ne_true
      · refine ⟨i, hi, hok, 1, Subgroup.one_mem _, ?_⟩
        rw [Equiv.Perm.one_apply]
        exact Fin.ext (hxw.trans (covS_walkId ρΩ hcol (covS_wAt_lt (hpw _))))
    | succ s ih =>
      intro hs x hx
      rw [covS_eOf_succ, Nat.testBit_or, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · exact ih (by omega) x hx
      · obtain ⟨hk, hj, hst, hlen⟩ := hlast s (by omega)
        obtain ⟨-, hset⟩ := covS_seg ρΩ hrw hnet hsa0 hseg (hEb s (by omega)) _ hk hj hst
        rw [hlen, Nat.sub_self, covS_suf_zero] at hset
        have hxm : x ∈ {x : Fin 412896 | (XO (STL (128 * j + s))).testBit x = true} := hx
        rw [hset] at hxm
        obtain ⟨y, hy, rfl⟩ := hxm
        obtain ⟨i, hi, hok, σ, hσ, rfl⟩ := ih (by omega) y hy
        refine ⟨i, hi, hok, ρΩ (evalWord (yGen 4 3 2) (wList (RW (genOf GS j s)))) * σ,
          Subgroup.mul_mem _ (Subgroup.subset_closure ⟨s, show s < GN j by omega, rfl⟩) hσ, ?_⟩
        rw [Equiv.Perm.mul_apply]
  intro x
  apply hcov (GN j) le_rfl x
  rw [hall]
  exact covS_ones_testBit x.isLt

end CFSG.KC.B433Alt

end
