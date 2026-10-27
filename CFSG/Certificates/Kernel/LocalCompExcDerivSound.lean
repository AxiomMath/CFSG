module

public import Certificates.Data.Kernel.LocalComp.ExcDeriv
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6Inputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Defs
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Child3Reps

public section

namespace CFSG.KC.LocalComp.ExcDeriv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CodesImg
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier CFSG.Certificates

variable {n w : Nat}

theorem imgInj {g h : Equiv.Perm (Fin n)} (e : imageList g = imageList h) : g = h := by
  unfold imageList at e
  rw [List.ofFn_inj] at e
  exact Equiv.ext fun i => Fin.ext (congrFun e i)

theorem eq_of_img {g h : Equiv.Perm (Fin n)} {P : Nat} (hg : imageList g = (unpack n w P).toList)
    (hh : imageList h = (unpack n w P).toList) : g = h :=
  imgInj (hg.trans hh.symm)

theorem val_of_img {g : Equiv.Perm (Fin n)} {P : Nat} (hg : imageList g = (unpack n w P).toList)
    (i : Fin n) : (g i : Nat) = pg w (mask w) P i := by
  have hl : i.val < (imageList g).length := by simp [imageList]
  have e := List.getElem_of_eq hg hl
  simp only [imageList, List.getElem_ofFn, Array.getElem_toList, Fin.eta] at e
  rw [e, ← CFSG.KC.Child3.unpack_get' i.isLt, getElem!_pos _ i.val (by simp [unpack])]

theorem ne_of_neCK {g h : Equiv.Perm (Fin n)} {P Q : Nat}
    (hg : imageList g = (unpack n w P).toList) (hh : imageList h = (unpack n w Q).toList)
    (hne : neCK n w (mask w) (n * w) P Q = true) : g ≠ h := by
  unfold neCK at hne
  simp only [bAnd_iff] at hne
  obtain ⟨hp, hq, hb⟩ := hne
  obtain ⟨-, hw, hp0, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq0, -⟩ := CFSG.KS.PF.canon_facts hq
  intro e
  subst e
  have hPQ : P = Q := by
    refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp0 hq0 fun i hi => ?_
    rw [← val_of_img hg ⟨i, hi⟩, ← val_of_img hh ⟨i, hi⟩]
  rw [hPQ, Nat.beq_refl] at hb
  exact Bool.false_ne_true hb

theorem schreierPermEq_of_img {g h : Equiv.Perm (Fin n)} {P : Nat}
    (hg : imageList g = (unpack n w P).toList) (hh : imageList h = (unpack n w P).toList) :
    schreierPermEq g h = true :=
  (schreierPermEq_eq_true_iff g h).2 (eq_of_img hg hh)

theorem schreierPermEq_of_neCK {g h : Equiv.Perm (Fin n)} {P Q : Nat}
    (hg : imageList g = (unpack n w P).toList) (hh : imageList h = (unpack n w Q).toList)
    (hne : neCK n w (mask w) (n * w) P Q = true) : schreierPermEq g h = false := by
  cases e : schreierPermEq g h
  · rfl
  · exact absurd ((schreierPermEq_eq_true_iff g h).1 e) (ne_of_neCK hg hh hne)

theorem fixCntK_eq (P : Nat) : ∀ k, fixCntK w (mask w) P k =
    (List.range k).countP (fun i => Nat.beq (pg w (mask w) P i) i)
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.countP_append, ← fixCntK_eq P k]
    change Nat.add (fixCntK w (mask w) P k) (nIf(Nat.beq (pg w (mask w) P k) k, 1, 0)) = _
    cases h : Nat.beq (pg w (mask w) P k) k <;> simp [h]

theorem countFix_eq {g : Equiv.Perm (Fin n)} {P : Nat} (hg : imageList g = (unpack n w P).toList) :
    (List.finRange n).countP (fun i => decide (g i = i)) = fixCntK w (mask w) P n := by
  rw [fixCntK_eq, ← List.map_coe_finRange_eq_range, List.countP_map]
  apply List.countP_congr
  intro i _
  simp only [Function.comp_apply, Fin.ext_iff, val_of_img hg i, decide_eq_true_eq]
  constructor
  · intro h
    rw [h, Nat.beq_refl]
  · intro h
    exact Nat.eq_of_beq_eq_true h

abbrev Corr (n w : Nat) (cur : List (Equiv.Perm (Fin n))) (CUR : List Nat) : Prop :=
  List.Forall₂ (fun g G => imageList g = (unpack n w G).toList) cur CUR

theorem lenK_eq : ∀ L : List Nat, lenK L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenK_eq L)

theorem snocK_eq (x : Nat) : ∀ L : List Nat, snocK L x = L ++ [x]
  | [] => rfl
  | y :: L => congrArg (y :: ·) (snocK_eq x L)

theorem memK_spec {x : Nat} : ∀ {L : List Nat}, memK x L = true → x ∈ L
  | [], h => absurd h Bool.false_ne_true
  | y :: L, h => by
    change bIf(Nat.beq x y, true, memK x L) = true at h
    cases e : Nat.beq x y
    · rw [e] at h
      exact List.mem_cons_of_mem _ (memK_spec h)
    · rw [Nat.eq_of_beq_eq_true e]
      exact List.mem_cons_self

theorem anyL_spec {f : Nat → Bool} : ∀ {L : List Nat}, anyL f L = true → ∃ x ∈ L, f x = true
  | [], h => absurd h Bool.false_ne_true
  | y :: L, h => by
    change bIf(f y, true, anyL f L) = true at h
    cases e : f y
    · rw [e] at h
      obtain ⟨x, hx, hf⟩ := anyL_spec h
      exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩
    · exact ⟨y, List.mem_cons_self, e⟩

theorem anyN_spec {f : Nat → Bool} : ∀ {k : Nat}, anyN k f = true → ∃ i < k, f i = true
  | 0, h => absurd h Bool.false_ne_true
  | k + 1, h => by
    change bIf(f k, true, anyN k f) = true at h
    cases e : f k
    · rw [e] at h
      obtain ⟨i, hi, hf⟩ := anyN_spec h
      exact ⟨i, by omega, hf⟩
    · exact ⟨k, by omega, e⟩

theorem Corr.mem {cur : List (Equiv.Perm (Fin n))} {CUR : List Nat} (hc : Corr n w cur CUR) :
    ∀ {G : Nat}, G ∈ CUR → ∃ g ∈ cur, imageList g = (unpack n w G).toList := by
  induction hc with
  | nil => intro G hG; exact absurd hG List.not_mem_nil
  | @cons g G' cur CUR hg _ ih =>
    intro G hG
    rcases List.mem_cons.1 hG with rfl | h
    · exact ⟨g, List.mem_cons_self, hg⟩
    · obtain ⟨g', hg', e⟩ := ih h
      exact ⟨g', List.mem_cons_of_mem _ hg', e⟩

theorem Corr.getD {cur : List (Equiv.Perm (Fin n))} {CUR : List Nat} (hc : Corr n w cur CUR) :
    ∀ i < cur.length, imageList (cur.getD i 1) = (unpack n w (lget CUR i)).toList := by
  induction hc with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | @cons g G cur CUR hg _ ih =>
    intro i hi
    rcases i with _ | i
    · exact hg
    · exact ih i (by simpa using hi)

theorem Corr.snoc {cur : List (Equiv.Perm (Fin n))} {CUR : List Nat} (hc : Corr n w cur CUR)
    {g : Equiv.Perm (Fin n)} {G : Nat} (hg : imageList g = (unpack n w G).toList) :
    Corr n w (cur ++ [g]) (snocK CUR G) := by
  rw [snocK_eq]
  exact List.rel_append hc (List.Forall₂.cons hg List.Forall₂.nil)

theorem maskProd_img (hsz : szOK n w = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList)
    {mp : List (Equiv.Perm (Fin n)) → ℕ → Equiv.Perm (Fin n)} (h0 : ∀ m, mp [] m = 1)
    (h1 : ∀ g gs m, mp (g :: gs) m = (if m % 2 = 1 then g else 1) * mp gs (m / 2))
    {cur : List (Equiv.Perm (Fin n))} {CUR : List Nat} (hc : Corr n w cur CUR) :
    ∀ m, imageList (mp cur m) = (unpack n w (maskProdK n w (mask w) (pidn n w) CUR m)).toList := by
  induction hc with
  | nil => intro m; rw [h0]; exact hid
  | @cons g G cur CUR hg _ ih =>
    intro m
    rw [h1]
    change _ = (unpack n w (strictN (maskProdK n w (mask w) (pidn n w) CUR
      (Nat.shiftRight m 1)) (fun r => nIf(Nat.beq (Nat.land m 1) 1,
        pcomp n w (mask w) G r, r)))).toList
    have hr : Nat.shiftRight m 1 = m / 2 := by
      change m >>> 1 = m / 2
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    have hl : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
    rw [CFSG.KS.PF.strictN_eqP, hr, hl]
    by_cases hm : m % 2 = 1
    · rw [ite_eq_left hm, hm, Nat.beq_refl]
      exact mulK_rep hsz hg (ih (m / 2))
    · have hb : Nat.beq (m % 2) 1 = false := by
        cases e : Nat.beq (m % 2) 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hm
      rw [ite_eq_right hm, hb, one_mul]
      exact ih (m / 2)

section Sp6

open CFSG.ComponentClassification.RankTwoClassical.ExcSp6

variable {Zp : Nat} {forbid : List Nat}

theorem maskProd_sp6 (hsz : szOK 276 9 = true)
    (hid : imageList (1 : Equiv.Perm (Fin 276)) = (unpack 276 9 (pidn 276 9)).toList)
    {cur : List (Equiv.Perm (Fin 276))} {CUR : List Nat} (hc : Corr 276 9 cur CUR) (m : Nat) :
    imageList (maskProd cur m) = (unpack 276 9 (maskProdK 276 9 (mask 9) (pidn 276 9) CUR m)).toList :=
  maskProd_img hsz hid (mp := maskProd) (fun _ => rfl) (fun _ _ _ => rfl) hc m

theorem badK_sound_sp6 (hsz : szOK 276 9 = true)
    (hid : imageList (1 : Equiv.Perm (Fin 276)) = (unpack 276 9 (pidn 276 9)).toList)
    (hZ : imageList zC = (unpack 276 9 Zp).toList)
    {cur : List (Equiv.Perm (Fin 276))} {CUR : List Nat} (hc : Corr 276 9 cur CUR)
    (h : badK 276 9 (mask 9) (276 * 9) (pidn 276 9) [Zp] forbid CUR = true) :
    badState forbid cur = true := by
  unfold badK at h
  unfold badState
  simp only [Bool.or_eq_true, List.any_eq_true]
  cases e1 : anyL (fun g => neCK 276 9 (mask 9) (276 * 9) (pcomp 276 9 (mask 9) g g)
      (pidn 276 9)) CUR
  · rw [e1] at h
    cases e2 : anyL (fun g => anyL (fun h => neCK 276 9 (mask 9) (276 * 9)
        (pcomp 276 9 (mask 9) g h) (pcomp 276 9 (mask 9) h g)) CUR) CUR
    · rw [e2] at h
      right
      obtain ⟨mm, hmm, hf⟩ := anyN_spec h
      rw [CFSG.KS.PF.strictB_eqP] at hf
      simp only [bAnd_iff] at hf
      obtain ⟨hne, hz⟩ := hf
      have hp := maskProd_sp6 hsz hid hc mm
      have hlen : Nat.shiftLeft 1 (lenK CUR) = 2 ^ cur.length := by
        rw [lenK_eq, ← List.Forall₂.length_eq hc]
        exact (Nat.shiftLeft_eq 1 _).trans (Nat.one_mul _)
      refine ⟨mm, List.mem_range.2 ?_, ?_⟩
      · rwa [hlen] at hmm
      · simp only [tab_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
        refine ⟨schreierPermEq_of_neCK hp hid hne, ?_⟩
        cases ez : memK (maskProdK 276 9 (mask 9) (pidn 276 9) CUR mm) [Zp]
        · rw [ez] at hz
          right
          have hm := memK_spec hz
          unfold fixCount
          rw [countFix_eq hp]
          exact List.elem_iff.2 hm
        · left
          have hm := memK_spec ez
          rw [List.mem_singleton] at hm
          rw [hm] at hp
          exact schreierPermEq_of_img hp hZ
    · left
      right
      obtain ⟨G, hG, hf⟩ := anyL_spec e2
      obtain ⟨H, hH, hf'⟩ := anyL_spec hf
      obtain ⟨g, hg, eg⟩ := hc.mem hG
      obtain ⟨h', hh, eh⟩ := hc.mem hH
      refine ⟨g, hg, h', hh, ?_⟩
      rw [Bool.not_eq_true']
      exact schreierPermEq_of_neCK (mulK_rep hsz eg eh) (mulK_rep hsz eh eg) hf'
  · left
    left
    obtain ⟨G, hG, hf⟩ := anyL_spec e1
    obtain ⟨g, hg, eg⟩ := hc.mem hG
    refine ⟨g, hg, ?_⟩
    rw [Bool.not_eq_true']
    exact schreierPermEq_of_neCK (mulK_rep hsz eg eg) hid hf

theorem derivK_sound_sp6 {A AI : Nat → Nat} (hsz : szOK 276 9 = true)
    (hid : imageList (1 : Equiv.Perm (Fin 276)) = (unpack 276 9 (pidn 276 9)).toList)
    (hlen : mGens.length = 7)
    (hA : ∀ j < mGens.length, imageList (mGens.getD j 1) = (unpack 276 9 (A j)).toList)
    (hAp : ∀ j < mGens.length, permOK 276 9 (mask 9) (276 * 9) (A j) (AI j) = true)
    (hZ : imageList zC = (unpack 276 9 Zp).toList) :
    ∀ (steps : List (ℕ × List ℤ × ℕ)) {cur : List (Equiv.Perm (Fin 276))} {CUR : List Nat},
      Corr 276 9 cur CUR →
      derivK 276 9 (mask 9) (276 * 9) (pidn 276 9) A AI 7 (fun _ => true) [Zp] forbid steps CUR =
        true →
      derivCheck forbid cur steps = true := by
  intro steps
  induction steps with
  | nil =>
    intro cur CUR hc h
    rw [derivCheck]
    exact badK_sound_sp6 hsz hid hZ hc h
  | cons st rest ih =>
    intro cur CUR hc h
    obtain ⟨mm, wd, i⟩ := st
    rw [derivCheck, Bool.or_eq_true]
    change bIf(badK 276 9 (mask 9) (276 * 9) (pidn 276 9) [Zp] forbid CUR, true,
      stepK 276 9 (mask 9) (276 * 9) (pidn 276 9) A AI 7 (fun _ => true) CUR mm wd i
        (derivK 276 9 (mask 9) (276 * 9) (pidn 276 9) A AI 7 (fun _ => true) [Zp] forbid rest)) =
      true at h
    cases hb : badK 276 9 (mask 9) (276 * 9) (pidn 276 9) [Zp] forbid CUR
    · rw [hb] at h
      right
      unfold stepK at h
      simp only [CFSG.KS.PF.strictB_eqP, bAnd_iff] at h
      obtain ⟨h1, h3, h4, h5, h6, h7⟩ := h
      have hp := maskProd_sp6 hsz hid hc mm
      have hc' := evalCodes_img hsz hA hAp hid (hlen ▸ h3)
      have hci := invK_rep hc' h4
      have hcl : CUR.length = cur.length := (List.Forall₂.length_eq hc).symm
      have hi : i < cur.length := by
        have := Nat.blt_eq.mp h6
        rwa [lenK_eq, hcl] at this
      have hnew := mulK_rep hsz (mulK_rep hsz hc' (hc.getD i hi)) hci
      simp only [tab_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      refine ⟨⟨⟨schreierPermEq_of_neCK hp hid h1, ?_⟩, hi⟩, ih (hc.snoc hnew) h7⟩
      have e2 := mulK_rep hsz hp hc'
      rw [← Nat.eq_of_beq_eq_true h5] at e2
      exact schreierPermEq_of_img (mulK_rep hsz hc' hp) e2
    · left
      exact badK_sound_sp6 hsz hid hZ hc hb

end Sp6

section O8

open CFSG.ComponentClassification.RankTwoClassical.ExcO8

variable {forbid : List Nat}

theorem badK_sound_o8 (hsz : szOK n w = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList)
    {zs : List (Equiv.Perm (Fin n))} {Z : List Nat} (hZ : Corr n w zs Z)
    {cur : List (Equiv.Perm (Fin n))} {CUR : List Nat} (hc : Corr n w cur CUR)
    (h : badK n w (mask w) (n * w) (pidn n w) Z forbid CUR = true) :
    badState zs forbid cur = true := by
  unfold badK at h
  unfold badState
  simp only [Bool.or_eq_true, List.any_eq_true]
  cases e1 : anyL (fun g => neCK n w (mask w) (n * w) (pcomp n w (mask w) g g)
      (pidn n w)) CUR
  · rw [e1] at h
    cases e2 : anyL (fun g => anyL (fun h => neCK n w (mask w) (n * w)
        (pcomp n w (mask w) g h) (pcomp n w (mask w) h g)) CUR) CUR
    · rw [e2] at h
      right
      obtain ⟨mm, hmm, hf⟩ := anyN_spec h
      rw [CFSG.KS.PF.strictB_eqP] at hf
      simp only [bAnd_iff] at hf
      obtain ⟨hne, hz⟩ := hf
      have hp := maskProd_img hsz hid (mp := maskProd) (fun _ => rfl) (fun _ _ _ => rfl) hc mm
      have hlen : Nat.shiftLeft 1 (lenK CUR) = 2 ^ cur.length := by
        rw [lenK_eq, ← List.Forall₂.length_eq hc]
        exact (Nat.shiftLeft_eq 1 _).trans (Nat.one_mul _)
      refine ⟨mm, List.mem_range.2 ?_, ?_⟩
      · rwa [hlen] at hmm
      · simp only [tab_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true]
        refine ⟨schreierPermEq_of_neCK hp hid hne, ?_⟩
        cases ez : memK (maskProdK n w (mask w) (pidn n w) CUR mm) Z
        · rw [ez] at hz
          right
          have hm := memK_spec hz
          unfold fixNum
          rw [countFix_eq hp]
          exact List.elem_iff.2 hm
        · left
          obtain ⟨z, hz', ez'⟩ := hZ.mem (memK_spec ez)
          exact ⟨z, hz', schreierPermEq_of_img hp ez'⟩
    · left
      right
      obtain ⟨G, hG, hf⟩ := anyL_spec e2
      obtain ⟨H, hH, hf'⟩ := anyL_spec hf
      obtain ⟨g, hg, eg⟩ := hc.mem hG
      obtain ⟨h', hh, eh⟩ := hc.mem hH
      refine ⟨g, hg, h', hh, ?_⟩
      rw [Bool.not_eq_true']
      exact schreierPermEq_of_neCK (mulK_rep hsz eg eh) (mulK_rep hsz eh eg) hf'
  · left
    left
    obtain ⟨G, hG, hf⟩ := anyL_spec e1
    obtain ⟨g, hg, eg⟩ := hc.mem hG
    refine ⟨g, hg, ?_⟩
    rw [Bool.not_eq_true']
    exact schreierPermEq_of_neCK (mulK_rep hsz eg eg) hid hf

theorem derivK_sound_o8 {A AI : Nat → Nat} {kA : Nat} (hsz : szOK n w = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList)
    {al : List (Equiv.Perm (Fin n))} (hlen : al.length = kA)
    (hA : ∀ j < al.length, imageList (al.getD j 1) = (unpack n w (A j)).toList)
    (hAp : ∀ j < al.length, permOK n w (mask w) (n * w) (A j) (AI j) = true)
    {okW : List ℤ → Bool} {zs : List (Equiv.Perm (Fin n))} {Z : List Nat} (hZ : Corr n w zs Z) :
    ∀ (steps : List (ℕ × List ℤ × ℕ)) {cur : List (Equiv.Perm (Fin n))} {CUR : List Nat},
      Corr n w cur CUR →
      derivK n w (mask w) (n * w) (pidn n w) A AI kA okW Z forbid steps CUR = true →
      derivCheck al okW zs forbid cur steps = true := by
  intro steps
  induction steps with
  | nil =>
    intro cur CUR hc h
    rw [derivCheck]
    exact badK_sound_o8 hsz hid hZ hc h
  | cons st rest ih =>
    intro cur CUR hc h
    obtain ⟨mm, wd, i⟩ := st
    rw [derivCheck, Bool.or_eq_true]
    change bIf(badK n w (mask w) (n * w) (pidn n w) Z forbid CUR, true,
      stepK n w (mask w) (n * w) (pidn n w) A AI kA okW CUR mm wd i
        (derivK n w (mask w) (n * w) (pidn n w) A AI kA okW Z forbid rest)) = true at h
    cases hb : badK n w (mask w) (n * w) (pidn n w) Z forbid CUR
    · rw [hb] at h
      right
      unfold stepK at h
      simp only [CFSG.KS.PF.strictB_eqP, bAnd_iff] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      have hp := maskProd_img hsz hid (mp := maskProd) (fun _ => rfl) (fun _ _ _ => rfl) hc mm
      have h3' : lettersK al.length wd = true := by rw [hlen]; exact h3
      have hc' := evalCodes_img hsz hA hAp hid h3'
      have hci := invK_rep hc' h4
      have hcl : CUR.length = cur.length := (List.Forall₂.length_eq hc).symm
      have hi : i < cur.length := by
        have := Nat.blt_eq.mp h6
        rwa [lenK_eq, hcl] at this
      have hnew := mulK_rep hsz (mulK_rep hsz hc' (hc.getD i hi)) hci
      simp only [tab_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      refine ⟨⟨⟨⟨schreierPermEq_of_neCK hp hid h1, h2⟩, ?_⟩, hi⟩, ih (hc.snoc hnew) h7⟩
      have e2 := mulK_rep hsz hp hc'
      rw [← Nat.eq_of_beq_eq_true h5] at e2
      exact schreierPermEq_of_img (mulK_rep hsz hc' hp) e2
    · left
      exact badK_sound_o8 hsz hid hZ hc hb

end O8

end CFSG.KC.LocalComp.ExcDeriv

end
