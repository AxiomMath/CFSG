module

public import Certificates.Data.Kernel.LocalComp.ThreeWP
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRuData
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.LocalCompThreeWitnessSound
import CFSG.Certificates.Kernel.LocalComp.Spec.ThreeW
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness

public section

namespace CFSG.KC.LocalComp.ThreeWP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.RestrictedStd.Spor

private def Cn (n w P : Nat) : Prop := P >>> (n * w) = 0 ∧ ∀ i < n, pg w (mask w) P i < n

private theorem szOK_facts {n w : Nat} (h : szOK n w = true) :
    n < 16777216 ∧ n + 1 < 2 ^ w := by
  unfold szOK at h
  simp only [bAnd_iff] at h
  exact ⟨by simpa [Nat.blt_eq] using h.1, by simpa [Nat.blt_eq, Nat.shiftLeft_eq] using h.2⟩

private theorem cn_of_canonK {n w P : Nat} (h : canonK n w (mask w) (n * w) P = true) :
    Cn n w P :=
  ⟨(CFSG.KS.PF.canon_facts h).2.2.1, (CFSG.KS.PF.canon_facts h).2.2.2⟩

private theorem unpack_get {n w P i : Nat} (hi : i < n) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [getElem!_pos _ i (by simpa [unpack] using hi)]
  simp [unpack]

private theorem arrTable_get (a : Array Nat) (i : Nat) :
    (arrTable a)[i]! = UInt32.ofNat a[i]! := by
  by_cases hs : i < a.size
  · rw [getElem!_pos (arrTable a) i (by simpa [arrTable] using hs), getElem!_pos a i hs]
    simp [arrTable]
  · rw [getElem!_neg (arrTable a) i (by simpa [arrTable] using hs), getElem!_neg a i hs]
    rfl

private theorem tab_ap {n w P i : Nat} (hn : n < 2 ^ 32) (hP : Cn n w P) (hi : i < n) :
    ap (arrTable (unpack n w P)) i = pg w (mask w) P i := by
  rw [ap, arrTable_get, unpack_get hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  exact Nat.lt_trans (hP.2 i hi) hn

private theorem compT_tab {n w P P' : Nat} (hn : n < 2 ^ 32)
    (hP' : ∀ i < n, pg w (mask w) P' i < n) :
    compT n (arrTable (unpack n w P)) (arrTable (unpack n w P')) =
      arrTable (unpack n w (pcomp n w (mask w) P P')) := by
  apply Array.ext
  · simp [compT, arrTable, unpack]
  · intro i h1 h2
    have hi : i < n := by simpa [compT] using h1
    simp only [compT, Array.getElem_ofFn]
    have e1 : ((arrTable (unpack n w P'))[i]!).toNat = pg w (mask w) P' i := by
      rw [arrTable_get, unpack_get hi, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.lt_trans (hP' i hi) hn)]
    rw [← getElem!_pos _ i h2, e1, arrTable_get, arrTable_get, unpack_get (hP' i hi),
      unpack_get hi, CFSG.KS.PF.pg_pcomp hn hi]

private theorem idT_tab {n w : Nat} (hn : szOK n w = true) :
    idT n = arrTable (unpack n w (pidn n w)) := by
  have hf := szOK_facts hn
  apply Array.ext
  · simp [idT, arrTable, unpack]
  · intro i h1 h2
    have hi : i < n := by simpa [idT] using h1
    simp only [idT, Array.getElem_ofFn]
    rw [← getElem!_pos _ i h2, arrTable_get, unpack_get hi, CFSG.KS.PF.pg_pidn hf.1 hf.2 hi]

private theorem cn_pidn {n w : Nat} (hn : szOK n w = true) : Cn n w (pidn n w) := by
  have hf := szOK_facts hn
  exact ⟨CFSG.KS.PF.pidn_shr hf.1 hf.2, fun i hi => by rw [CFSG.KS.PF.pg_pidn hf.1 hf.2 hi]; exact hi⟩

private theorem cn_pcomp {n w P P' : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (hP : Cn n w P)
    (hP' : Cn n w P') : Cn n w (pcomp n w (mask w) P P') :=
  ⟨CFSG.KS.PF.pcomp_shr P P' hn hw, fun i hi => by
    rw [CFSG.KS.PF.pg_pcomp hn hi]
    exact hP.2 _ (hP'.2 i hi)⟩

private theorem wordT_size (n : Nat) (f : Int → Table) :
    ∀ wd : List Int, (wordT n f wd).size = n
  | [] => by simp [wordT, idT]
  | z :: zs => by
    have ih := wordT_size n f zs
    have e : wordT n f (z :: zs) = (wordT n f zs).map fun t => (f z)[t.toNat]! := rfl
    rw [e, Array.size_map, ih]

private theorem wordT_cons (n : Nat) (f : Int → Table) (z : Int) (zs : List Int) :
    wordT n f (z :: zs) = compT n (f z) (wordT n f zs) := by
  have e : wordT n f (z :: zs) = (wordT n f zs).map fun t => (f z)[t.toNat]! := rfl
  have hs := wordT_size n f zs
  rw [e]
  apply Array.ext
  · rw [Array.size_map, hs]
    simp [compT]
  · intro i h1 h2
    have hi : i < n := by simpa [compT] using h2
    simp only [Array.getElem_map, compT, Array.getElem_ofFn]
    rw [getElem!_pos _ i (by rw [hs]; exact hi)]

private theorem wordT_sound {n w : Nat} (hn : szOK n w = true) {f : Int → Table} {F : Int → Nat} :
    ∀ wd : List Int, (∀ z ∈ wd, f z = arrTable (unpack n w (F z))) →
      (∀ z ∈ wd, canonK n w (mask w) (n * w) (F z) = true) →
      wordT n f wd = arrTable (unpack n w (wordP n w F wd)) ∧ Cn n w (wordP n w F wd)
  | [], _, _ => by
    exact ⟨idT_tab hn, cn_pidn hn⟩
  | z :: zs, hf, hc => by
    have hnf := szOK_facts hn
    have hn32 : n < 2 ^ 32 := by omega
    have hw : 0 < w := CFSG.KS.PF.w_pos hnf.2
    obtain ⟨ih1, ih2⟩ := wordT_sound hn zs (fun z' hz' => hf z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hc z' (List.mem_cons_of_mem _ hz'))
    have hz := cn_of_canonK (hc z List.mem_cons_self)
    have e : wordP n w F (z :: zs) = pcomp n w (mask w) (F z) (wordP n w F zs) :=
      CFSG.KS.PF.strictN_eqP _ _
    rw [wordT_cons, e, hf z List.mem_cons_self, ih1, compT_tab hn32 ih2.2]
    exact ⟨rfl, cn_pcomp hn32 hw hz ih2⟩

private theorem powT_sound {n w P : Nat} (hn : szOK n w = true) (hP : Cn n w P) :
    ∀ e : Nat, powT n e (arrTable (unpack n w P)) =
        arrTable (unpack n w (ppow n w (mask w) (pidn n w) P e)) ∧
      Cn n w (ppow n w (mask w) (pidn n w) P e)
  | 0 => ⟨idT_tab hn, cn_pidn hn⟩
  | e + 1 => by
    have hnf := szOK_facts hn
    have hn32 : n < 2 ^ 32 := by omega
    have hw : 0 < w := CFSG.KS.PF.w_pos hnf.2
    obtain ⟨ih1, ih2⟩ := powT_sound hn hP e
    have eq : ppow n w (mask w) (pidn n w) P (e + 1) =
        pcomp n w (mask w) P (ppow n w (mask w) (pidn n w) P e) :=
      CFSG.KS.PF.strictN_eqP _ _
    have et : powT n (e + 1) (arrTable (unpack n w P)) =
        compT n (arrTable (unpack n w P)) (powT n e (arrTable (unpack n w P))) := rfl
    rw [et, eq, ih1, compT_tab hn32 ih2.2]
    exact ⟨rfl, cn_pcomp hn32 hw hP ih2⟩

theorem powT_wordT_sound {n w e Q : Nat} {f : Int → Table} {F : Int → Nat} {wd : List Int}
    (hn : CFSG.KS.Raw.szOK n w = true) (hf : ∀ z ∈ wd, f z = arrTable (unpack n w (F z)))
    (hc : ∀ z ∈ wd, canonK n w (mask w) (n * w) (F z) = true)
    (h : Nat.beq Q (ppow n w (mask w) (pidn n w) (wordP n w F wd) e) = true) :
    powT n e (wordT n f wd) = arrTable (unpack n w Q) := by
  obtain ⟨h1, h2⟩ := wordT_sound hn wd hf hc
  have hQ : Q = ppow n w (mask w) (pidn n w) (wordP n w F wd) e := Nat.eq_of_beq_eq_true h
  rw [h1, hQ]
  exact (powT_sound hn h2 e).1

section Search

open CFSG.Sporadic.Schreier.Native

private theorem bIf_false_true {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

private theorem head_facts {n w m nc Q Y : Nat} {E : Nat → Nat}
    (hh : headWP n w E m Q Y nc = true) :
    0 < m ∧ E 0 = Q ∧ canonK n w (mask w) (n * w) Q = true ∧ canonK n w (mask w) (n * w) Y = true ∧
      ppow n w (mask w) (pidn n w) Y 3 = pidn n w ∧ Y ≠ pidn n w ∧ nc < m ∧
      commP n w Y (E nc) = false := by
  unfold headWP at hh
  simp only [bAnd_iff] at hh
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hh
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, h3, h4, Nat.eq_of_beq_eq_true h5, ?_,
    Nat.blt_eq.mp h7, bIf_false_true h8⟩
  intro e
  rw [e] at h6
  simp at h6

private theorem row_facts {n w k m j : Nat} {G GI E R : Nat → Nat}
    (hr : rowWP n w G GI k E R m j = true) :
    (∀ l < k, (∃ a < m, E a = conjP n w (G l) (GI l) (E j)) ∧
      (∃ b < m, E b = conjP n w (GI l) (G l) (E j))) ∧
    (j ≠ 0 → ∃ p < j, ∃ l < k, E j = conjP n w (G l) (GI l) (E p)) := by
  unfold rowWP at hr
  rw [bAnd_iff] at hr
  obtain ⟨h1, h2⟩ := hr
  refine ⟨fun l hl => ?_, fun hj => ?_⟩
  · have h := allN_spec h1 l hl
    rw [bAnd_iff] at h
    obtain ⟨ha, hb⟩ := h
    rw [CFSG.KS.PF.strictB_eqP, bAnd_iff] at ha hb
    exact ⟨⟨_, Nat.blt_eq.mp ha.1, Nat.eq_of_beq_eq_true ha.2⟩,
      ⟨_, Nat.blt_eq.mp hb.1, Nat.eq_of_beq_eq_true hb.2⟩⟩
  · have hb : Nat.beq j 0 = false := by
      cases e : Nat.beq j 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hj
    rw [hb] at h2
    change (strictB (rf (R j) 0) fun p => strictB (rf (R j) 1) fun l =>
        bAnd(Nat.blt p j, bAnd(Nat.blt l k, Nat.beq (E j) (conjP n w (G l) (GI l) (E p))))) =
      true at h2
    rw [CFSG.KS.PF.strictB_eqP, CFSG.KS.PF.strictB_eqP, bAnd_iff, bAnd_iff] at h2
    exact ⟨_, Nat.blt_eq.mp h2.1, _, Nat.blt_eq.mp h2.2.1, Nat.eq_of_beq_eq_true h2.2.2⟩

private theorem comm_facts {n w i : Nat} {E : Nat → Nat} (hc : commWP n w E i = true) :
    ∀ j < i, pcomp n w (mask w) (E i) (E j) = pcomp n w (mask w) (E j) (E i) := by
  intro j hj
  have h := allN_spec hc j hj
  exact Nat.eq_of_beq_eq_true h

private theorem permOK_range {n w p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    (∀ i < n, pg w (mask w) p i < n) ∧ ∀ i < n, pg w (mask w) q i < n := by
  unfold permOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, ha⟩ := h
  have hpr : ∀ i < n, pg w (mask w) p i < n ∧ pg w (mask w) q (pg w (mask w) p i) = i := by
    intro i hi
    have := allN_spec ha i hi
    rw [CFSG.KS.PF.strictB_eqP] at this
    simp only [bAnd_iff] at this
    exact ⟨by simpa [Nat.blt_eq] using this.1, Nat.eq_of_beq_eq_true this.2⟩
  refine ⟨fun i hi => (hpr i hi).1, fun j hj => ?_⟩
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => pg w (mask w) p a) (fun a ha => by simpa using (hpr a (by simpa using ha)).1)
    (fun a₁ a₂ h₁ h₂ e => by
      have e1 := (hpr a₁ (by simpa using h₁)).2
      have e2 := (hpr a₂ (by simpa using h₂)).2
      have e' : pg w (mask w) p a₁ = pg w (mask w) p a₂ := e
      rw [e'] at e1
      omega) le_rfl
  obtain ⟨i, hi, e⟩ := hsurj j (by simpa using hj)
  have e' : pg w (mask w) p i = j := e.symm
  rw [← e', (hpr i (by simpa using hi)).2]
  simpa using hi

private theorem conjT_tab {n w g gi x : Nat} (hn : n < 2 ^ 32)
    (hgi : ∀ i < n, pg w (mask w) gi i < n) (hx : ∀ i < n, pg w (mask w) x i < n) :
    conjT n (arrTable (unpack n w g)) (arrTable (unpack n w gi)) (arrTable (unpack n w x)) =
      arrTable (unpack n w (conjP n w g gi x)) := by
  unfold conjT conjP
  rw [compT_tab hn hx, compT_tab hn hgi]

private theorem cn_conjP {n w g gi x : Nat} (hn : n < 2 ^ 32) (hw : 0 < w)
    (hg : ∀ i < n, pg w (mask w) g i < n) (hgi : ∀ i < n, pg w (mask w) gi i < n)
    (hx : Cn n w x) : Cn n w (conjP n w g gi x) := by
  have h1 : ∀ i < n, pg w (mask w) (pcomp n w (mask w) g x) i < n := fun i hi => by
    rw [CFSG.KS.PF.pg_pcomp hn hi]
    exact hg _ (hx.2 i hi)
  exact ⟨CFSG.KS.PF.pcomp_shr _ _ hn hw, fun i hi => by
    unfold conjP
    rw [CFSG.KS.PF.pg_pcomp hn hi]
    exact h1 _ (hgi i hi)⟩

private theorem foldr_digits_inj (f f' : ℕ → ℕ) (n : ℕ) :
    ∀ s len, (∀ i, s ≤ i → i < s + len → f i < n ∧ f' i < n) →
      (List.range' s len).foldr (fun i acc => f i + n * acc) 0 =
        (List.range' s len).foldr (fun i acc => f' i + n * acc) 0 →
      ∀ i, s ≤ i → i < s + len → f i = f' i
  | _, 0, _, _, _, h1, h2 => absurd h2 (by omega)
  | s, len + 1, hlt, he, i, h1, h2 => by
    simp only [List.range'_succ, List.foldr_cons] at he
    have hs := hlt s le_rfl (by omega)
    have e1 : f s = f' s := by
      have := congrArg (· % n) he
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs.1, Nat.mod_eq_of_lt hs.2] at this
      exact this
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact e1
    · rw [e1] at he
      have hn : 0 < n := by omega
      have e2 := Nat.eq_of_mul_eq_mul_left hn (Nat.add_left_cancel he)
      exact foldr_digits_inj f f' n (s + 1) len (fun j hj1 hj2 => hlt j (by omega) (by omega)) e2 i
        (by omega) (by omega)

private theorem key_tab_inj {n w P P' : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (hP : Cn n w P)
    (hP' : Cn n w P')
    (h : key n (arrTable (unpack n w P)) = key n (arrTable (unpack n w P'))) : P = P' := by
  unfold key at h
  rw [List.range_eq_range'] at h
  have key := foldr_digits_inj (fun i => ap (arrTable (unpack n w P)) i)
    (fun i => ap (arrTable (unpack n w P')) i) n 0 n (fun i _ hi => by
      simp only [Nat.zero_add] at hi
      rw [tab_ap hn hP hi, tab_ap hn hP' hi]
      exact ⟨hP.2 i hi, hP'.2 i hi⟩) h
  refine CFSG.KS.PF.eq_of_fields hw hP.1 hP'.1 (fun i hi => ?_)
  have := key i (Nat.zero_le _) (by omega)
  simpa only [tab_ap hn hP hi, tab_ap hn hP' hi] using this

section BFS

open CFSG.KC.LocalComp.ThreeW CFSG.KC.LocalComp.Spec

private inductive Reach (n : Nat) (gens gensInv : Array Table) (x : Table) : Table → Prop
  | base : Reach n gens gensInv x x
  | step {z : Table} (l : Nat) (hl : l < gens.size) :
      Reach n gens gensInv x z → Reach n gens gensInv x (conjT n gens[l]! gensInv[l]! z)

private structure BI (n : Nat) (gens gensInv : Array Table) (x : Table) (st : ClosSt) : Prop where
  par_size : st.2.1.size = st.1.size
  lab_size : st.2.2.1.size = st.1.size
  pos : 0 < st.1.size
  first : st.1[0]! = x
  tree : ∀ k, 0 < k → k < st.1.size → st.2.1[k]! < k ∧ st.2.2.1[k]! < gens.size ∧
    st.1[k]! = conjT n gens[st.2.2.1[k]!]! gensInv[st.2.2.1[k]!]! st.1[st.2.1[k]!]!
  seen : ∀ kk, st.2.2.2.contains kk = true ↔ ∃ k < st.1.size, key n st.1[k]! = kk
  reach : ∀ k < st.1.size, Reach n gens gensInv x st.1[k]!
  dist : ∀ k < st.1.size, ∀ k' < st.1.size, key n st.1[k]! = key n st.1[k']! → k = k'

private def Prog (n : Nat) (gens gensInv : Array Table) (h l₀ : Nat) (st : ClosSt) : Prop :=
  ∀ k < st.1.size, ∀ l < gens.size, (k < h ∨ (k = h ∧ l < l₀)) →
    st.2.2.2.contains (key n (conjT n gens[l]! gensInv[l]! st.1[k]!)) = true

private theorem push_get_eq {α : Type} [Inhabited α] {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by simp)]
  exact Array.getElem_push_eq

private theorem inner_step {n : Nat} {gens gensInv : Array Table} {x : Table} {st : ClosSt}
    {h l : Nat} (hl : l < gens.size) (hI : BI n gens gensInv x st)
    (hP : Prog n gens gensInv h l st) (hh : h < st.1.size) :
    BI n gens gensInv x (closStepAt n gens gensInv h st l) ∧
      Prog n gens gensInv h (l + 1) (closStepAt n gens gensInv h st l) ∧
      h < (closStepAt n gens gensInv h st l).1.size ∧
      (closStepAt n gens gensInv h st l).1[h]! = st.1[h]! := by
  unfold closStepAt
  dsimp only
  by_cases hc : st.2.2.2.contains (key n (conjT n gens[l]! gensInv[l]! st.1[h]!)) = true
  · rw [if_pos hc]
    refine ⟨hI, fun k hk l' hl' hkl => ?_, hh, rfl⟩
    rcases hkl with h1 | ⟨rfl, h2⟩
    · exact hP k hk l' hl' (Or.inl h1)
    · rcases Nat.lt_or_ge l' l with h3 | h3
      · exact hP k hk l' hl' (Or.inr ⟨rfl, h3⟩)
      · have : l' = l := by omega
        subst this
        exact hc
  · rw [if_neg hc]
    obtain ⟨hps, hls, hpos, hfirst, htree, hseen, hreach, hdist⟩ := hI
    set z := conjT n gens[l]! gensInv[l]! st.1[h]! with hz
    have hget : ∀ k < st.1.size, (st.1.push z)[k]! = st.1[k]! := fun k hk => spec_getElem!_push _ _ hk
    have hsz : (st.1.push z).size = st.1.size + 1 := Array.size_push _
    refine ⟨⟨by simp [hps], by simp [hls], by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_, by simp; omega, hget h hh⟩
    · rw [hget 0 hpos, hfirst]
    · intro k hk0 hk
      simp only [Array.size_push] at hk ⊢
      rcases Nat.lt_or_ge k st.1.size with hk1 | hk1
      · rw [spec_getElem!_push _ _ (by omega), spec_getElem!_push _ _ (by omega), hget k hk1]
        obtain ⟨a, b, c⟩ := htree k hk0 hk1
        refine ⟨a, b, ?_⟩
        rw [hget _ (by omega)]
        exact c
      · have hk2 : k = st.1.size := by omega
        subst hk2
        have e1 : (st.2.1.push h)[st.1.size]! = h := by rw [← hps]; exact push_get_eq
        have e2 : (st.2.2.1.push l)[st.1.size]! = l := by rw [← hls]; exact push_get_eq
        rw [e1, e2, push_get_eq, hget h hh]
        exact ⟨hh, hl, rfl⟩
    · intro kk
      rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq, hseen kk]
      constructor
      · rintro (e | ⟨k, hk, e⟩)
        · exact ⟨st.1.size, by simp, by rw [push_get_eq]; exact e.symm⟩
        · exact ⟨k, by simp; omega, by rw [hget k hk]; exact e⟩
      · rintro ⟨k, hk, e⟩
        simp only [Array.size_push] at hk
        rcases Nat.lt_or_ge k st.1.size with hk1 | hk1
        · exact Or.inr ⟨k, hk1, by rw [← hget k hk1]; exact e⟩
        · have : k = st.1.size := by omega
          subst this
          rw [push_get_eq] at e
          exact Or.inl e.symm
    · intro k hk
      simp only [Array.size_push] at hk
      rcases Nat.lt_or_ge k st.1.size with hk1 | hk1
      · rw [hget k hk1]
        exact hreach k hk1
      · have : k = st.1.size := by omega
        subst this
        rw [push_get_eq]
        exact Reach.step l hl (hreach h hh)
    · intro k hk k' hk' e
      simp only [Array.size_push] at hk hk'
      have hnot : ∀ k < st.1.size, key n st.1[k]! ≠ key n z := fun k hk e' =>
        hc ((hseen _).2 ⟨k, hk, e'⟩)
      rcases Nat.lt_or_ge k st.1.size with hk1 | hk1 <;>
        rcases Nat.lt_or_ge k' st.1.size with hk1' | hk1'
      · rw [hget k hk1, hget k' hk1'] at e
        exact hdist k hk1 k' hk1' e
      · have : k' = st.1.size := by omega
        subst this
        rw [hget k hk1, push_get_eq] at e
        exact absurd e (hnot k hk1)
      · have : k = st.1.size := by omega
        subst this
        rw [hget k' hk1', push_get_eq] at e
        exact absurd e.symm (hnot k' hk1')
      · omega
    · intro k hk l' hl' hkl
      simp only [Array.size_push] at hk
      rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq]
      rcases Nat.lt_or_ge k st.1.size with hk1 | hk1
      · rw [hget k hk1]
        rcases hkl with h1 | ⟨rfl, h2⟩
        · exact Or.inr (hP k hk1 l' hl' (Or.inl h1))
        · rcases Nat.lt_or_ge l' l with h3 | h3
          · exact Or.inr (hP k hk1 l' hl' (Or.inr ⟨rfl, h3⟩))
          · have : l' = l := by omega
            subst this
            exact Or.inl rfl
      · rcases hkl with h1 | ⟨h1, -⟩ <;> omega


private theorem fold_inv {n : Nat} {gens gensInv : Array Table} {x : Table} {st0 : ClosSt}
    {h : Nat} (hI : BI n gens gensInv x st0) (hP : Prog n gens gensInv h 0 st0)
    (hh : h < st0.1.size) :
    ∀ c, c ≤ gens.size →
      BI n gens gensInv x ((List.range c).foldl (closStepAt n gens gensInv h) st0) ∧
      Prog n gens gensInv h c ((List.range c).foldl (closStepAt n gens gensInv h) st0) ∧
      h < ((List.range c).foldl (closStepAt n gens gensInv h) st0).1.size ∧
      ((List.range c).foldl (closStepAt n gens gensInv h) st0).1[h]! = st0.1[h]! := by
  intro c
  induction c with
  | zero => intro _; exact ⟨hI, hP, hh, rfl⟩
  | succ c ih =>
    intro hc
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨g1, g2, g3, g4⟩ := inner_step (l := c) (by omega) h1 h2 h3
    exact ⟨g1, g2, g3, g4.trans h4⟩

private def Done (n : Nat) (gens gensInv : Array Table) (st : ClosSt) : Prop :=
  ∀ k < st.1.size, ∀ l < gens.size,
    st.2.2.2.contains (key n (conjT n gens[l]! gensInv[l]! st.1[k]!)) = true

private theorem loop_spec {n : Nat} {gens gensInv : Array Table} {x : Table} :
    ∀ (f h : Nat) (st : ClosSt), BI n gens gensInv x st → Prog n gens gensInv h 0 st →
      ∃ st' : ClosSt, closLoop n gens gensInv f h st = (st'.1, st'.2.1, st'.2.2.1) ∧
        BI n gens gensInv x st' ∧ (st'.1.size ≤ h + f → Done n gens gensInv st')
  | 0, h, st, hI, hP => by
    exact ⟨st, rfl, hI, fun hs k hk l hl => hP k hk l hl (Or.inl (by omega))⟩
  | f + 1, h, st, hI, hP => by
    by_cases hh : h < st.1.size
    · have hc : closLoop n gens gensInv (f + 1) h st =
          closLoop n gens gensInv f (h + 1) (closStep n gens gensInv h st) := by
        simp only [closLoop, hh, ↓reduceIte]
      rw [hc, closStep_eq_foldl]
      obtain ⟨g1, g2, g3, g4⟩ := fold_inv hI hP hh gens.size le_rfl
      obtain ⟨st', e, hb, hd⟩ := loop_spec f (h + 1)
        ((List.range gens.size).foldl (closStepAt n gens gensInv h) st) g1
        (fun k hk l hl hkl => g2 k hk l hl (by
          rcases hkl with h1 | ⟨_, h2⟩
          · rcases Nat.lt_or_ge k h with h3 | h3
            · exact Or.inl h3
            · exact Or.inr ⟨by omega, hl⟩
          · exact absurd h2 (Nat.not_lt_zero _)))
      exact ⟨st', e, hb, fun hs => hd (by omega)⟩
    · have hc : closLoop n gens gensInv (f + 1) h st = (st.1, st.2.1, st.2.2.1) := by
        simp only [closLoop, hh, ↓reduceIte]
      exact ⟨st, hc, hI, fun hs k hk l hl => hP k hk l hl (Or.inl (by omega))⟩

private theorem closure_spec {n : Nat} {gens gensInv : Array Table} {x : Table} {cap : Nat}
    (hinj : ∀ u v, Reach n gens gensInv x u → Reach n gens gensInv x v → key n u = key n v →
      u = v)
    (φ : Table → ℕ) (hφ : ∀ u, Reach n gens gensInv x u → φ u < cap)
    (hφi : ∀ u v, Reach n gens gensInv x u → Reach n gens gensInv x v → φ u = φ v → u = v) :
    ∃ st : ClosSt, conjClosureL n gens gensInv x cap = (st.1, st.2.1, st.2.2.1) ∧
      BI n gens gensInv x st ∧ Done n gens gensInv st ∧
      ∀ u, Reach n gens gensInv x u → ∃ k < st.1.size, st.1[k]! = u := by
  have hinit : BI n gens gensInv x (#[x], #[0], #[0], [key n x]) :=
    ⟨rfl, rfl, by simp, rfl, fun k hk hk' => by simp at hk'; omega, fun kk => by
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq]
      constructor
      · intro e
        exact ⟨0, by simp, by simp [e]⟩
      · rintro ⟨k, hk, e⟩
        have : k = 0 := by simpa using hk
        subst this
        simpa using e.symm,
      fun k hk => by
        have : k = 0 := by simpa using hk
        subst this
        exact Reach.base, fun k hk k' hk' _ => by simp at hk hk'; omega⟩
  obtain ⟨st, e, hb, hd⟩ := loop_spec cap 0 (#[x], #[0], #[0], [key n x]) hinit
    (fun k hk l hl hkl => by rcases hkl with h1 | ⟨_, h2⟩ <;> omega)
  have hsize : st.1.size ≤ cap := by
    have := Finset.card_le_card_of_injOn (s := Finset.range st.1.size) (t := Finset.range cap)
      (fun k => φ st.1[k]!)
      (fun k hk => by
        simpa using hφ _ (hb.reach k (by simpa using hk)))
      (fun k hk k' hk' e => by
        have hk1 : k < st.1.size := by simpa using hk
        have hk2 : k' < st.1.size := by simpa using hk'
        exact hb.dist k hk1 k' hk2 (by
          rw [hφi _ _ (hb.reach k hk1) (hb.reach k' hk2) e]))
    simpa using this
  have hD := hd (by omega)
  refine ⟨st, e, hb, hD, fun u hu => ?_⟩
  induction hu with
  | base => exact ⟨0, hb.pos, hb.first⟩
  | step l hl hz ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨k', hk', e'⟩ := (hb.seen _).1 (hD k hk l hl)
    exact ⟨k', hk', hinj _ _ (hb.reach k' hk') (Reach.step l hl (hb.reach k hk)) e'⟩

private theorem allFrom_iff (lo : Nat) (p : Nat → Bool) :
    ∀ m, allFrom lo p m = true ↔ ∀ k < m, p (lo + k) = true
  | 0 => by simp [allFrom]
  | m + 1 => by
    simp only [allFrom, Bool.and_eq_true, allFrom_iff lo p m]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h1 k h
      · subst h
        exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h m (by omega)⟩

private theorem allInK_iff {lo hi : Nat} {p : Nat → Bool} :
    allInK lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold allInK
  rw [allFrom_iff]
  constructor
  · intro h i h1 h2
    have := h (i - lo) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  · intro h k hk
    exact h (lo + k) (by omega) (by omega)

private theorem tblEqK_iff {n : Nat} {S T : Table} :
    tblEqK n S T = true ↔ ∀ i < n, ap S i = ap T i := by
  unfold tblEqK
  rw [allInK_iff]
  exact ⟨fun h i hi => beq_iff_eq.1 (h i (Nat.zero_le _) hi),
    fun h i _ hi => beq_iff_eq.2 (h i hi)⟩

private theorem tblEqK_refl (n : Nat) (S : Table) : tblEqK n S S = true :=
  tblEqK_iff.2 fun _ _ => rfl

private theorem conjTreeOKK_of_BI {n : Nat} {gens gensInv : Array Table} {x : Table}
    {st : ClosSt} (hI : BI n gens gensInv x st) :
    conjTreeOKK n gens gensInv x st.1 st.2.1 st.2.2.1 = true := by
  unfold conjTreeOKK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hI.pos, by rw [hI.first]; exact tblEqK_refl n x⟩, allInK_iff.2 fun k hk1 hk2 => ?_⟩
  obtain ⟨a, b, c⟩ := hI.tree k hk1 hk2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨a, b⟩, by rw [← c]; exact tblEqK_refl n _⟩

private theorem ppow_succ_eq (n w P e : Nat) :
    ppow n w (mask w) (pidn n w) P (e + 1) =
      pcomp n w (mask w) P (ppow n w (mask w) (pidn n w) P e) :=
  CFSG.KS.PF.strictN_eqP _ _

private theorem ordTestK_of {n w Y : Nat} (hn : szOK n w = true) (hY : Cn n w Y)
    (hY3 : ppow n w (mask w) (pidn n w) Y 3 = pidn n w) (hYne : Y ≠ pidn n w) :
    ordTestK n 3 (arrTable (unpack n w Y)) = true := by
  have hnf := szOK_facts hn
  have hn32 : n < 2 ^ 32 := by omega
  have hw : 0 < w := CFSG.KS.PF.w_pos hnf.2
  have hap : ∀ i < n, ap (arrTable (unpack n w Y)) i = pg w (mask w) Y i := fun i hi =>
    tab_ap hn32 hY hi
  have h3 : ∀ i < n, pg w (mask w) Y (pg w (mask w) Y (pg w (mask w) Y i)) = i := by
    intro i hi
    have e : pg w (mask w) (ppow n w (mask w) (pidn n w) Y 3) i =
        pg w (mask w) (pidn n w) i := by rw [hY3]
    have p3 : ppow n w (mask w) (pidn n w) Y 3 =
        pcomp n w (mask w) Y (ppow n w (mask w) (pidn n w) Y 2) := ppow_succ_eq n w Y 2
    have p2 : ppow n w (mask w) (pidn n w) Y 2 =
        pcomp n w (mask w) Y (ppow n w (mask w) (pidn n w) Y 1) := ppow_succ_eq n w Y 1
    have p1 : ppow n w (mask w) (pidn n w) Y 1 =
        pcomp n w (mask w) Y (ppow n w (mask w) (pidn n w) Y 0) := ppow_succ_eq n w Y 0
    have p0 : ppow n w (mask w) (pidn n w) Y 0 = pidn n w := rfl
    rw [p3, CFSG.KS.PF.pg_pcomp hn32 hi, p2, CFSG.KS.PF.pg_pcomp hn32 hi, p1,
      CFSG.KS.PF.pg_pcomp hn32 hi, p0, CFSG.KS.PF.pg_pidn hnf.1 hnf.2 hi] at e
    exact e
  have hdiv : divParts 3 = [1] := by decide
  unfold ordTestK
  rw [hdiv]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold powFixWK
    rw [allInK_iff]
    intro i _ hi
    simp only [apPowW, apW, List.foldr_cons, List.foldr_nil]
    rw [hap i hi, hap _ (hY.2 i hi), hap _ (hY.2 _ (hY.2 i hi)), h3 i hi]
    exact beq_self_eq_true _
  · cases hb : powFixWK n [arrTable (unpack n w Y)] 1
    · rfl
    · exfalso
      unfold powFixWK at hb
      rw [allInK_iff] at hb
      apply hYne
      refine CFSG.KS.PF.eq_of_fields hw hY.1 (CFSG.KS.PF.pidn_shr hnf.1 hnf.2) (fun i hi => ?_)
      have := hb i (Nat.zero_le _) hi
      simp only [apPowW, apW, List.foldr_cons, List.foldr_nil, beq_iff_eq] at this
      rw [hap i hi] at this
      rw [this, CFSG.KS.PF.pg_pidn hnf.1 hnf.2 hi]

private theorem threeWitnessK_of_P {n w k m nc cap Q Y : Nat} {G GI E R : Nat → Nat}
    {gens gensInv : Array Table} {q y : Table} (hn : CFSG.KS.Raw.szOK n w = true)
    (hg : gens.size = k ∧ ∀ l < k, gens[l]! = arrTable (unpack n w (G l)))
    (hgi : gensInv.size = k ∧ ∀ l < k, gensInv[l]! = arrTable (unpack n w (GI l)))
    (hp : ∀ l < k, permOK n w (mask w) (n * w) (G l) (GI l) = true)
    (hq : q = arrTable (unpack n w Q)) (hy : y = arrTable (unpack n w Y)) (hm : m ≤ cap)
    (hh : headWP n w E m Q Y nc = true) (hr : ∀ j < m, rowWP n w G GI k E R m j = true)
    (hc : ∀ i < m, commWP n w E i = true) :
    threeWitnessK n gens gensInv q y cap = true := by
  have hnf := szOK_facts hn
  have hn32 : n < 2 ^ 32 := by omega
  have hw : 0 < w := CFSG.KS.PF.w_pos hnf.2
  obtain ⟨hm0, hE0, hQc, hYc, hY3, hYne, hnc, hcomm⟩ := head_facts hh
  have hQ' : Cn n w Q := cn_of_canonK hQc
  have hY' : Cn n w Y := cn_of_canonK hYc
  have hrows := fun j (hj : j < m) => row_facts (hr j hj)
  have hGr : ∀ l < k, (∀ i < n, pg w (mask w) (G l) i < n) ∧
      ∀ i < n, pg w (mask w) (GI l) i < n := fun l hl => permOK_range (hp l hl)
  obtain ⟨hgs, hgt⟩ := hg
  obtain ⟨hgis, hgit⟩ := hgi
  have hEc : ∀ j < m, Cn n w (E j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hj0 : j = 0
      · subst hj0
        rw [hE0]
        exact hQ'
      · obtain ⟨p', hp', l, hl, e⟩ := (hrows j hj).2 hj0
        rw [e]
        exact cn_conjP hn32 hw (hGr l hl).1 (hGr l hl).2 (ih p' hp' (by omega))
  have hcom : ∀ i < m, ∀ j < m,
      pcomp n w (mask w) (E i) (E j) = pcomp n w (mask w) (E j) (E i) := by
    intro i hi j hj
    rcases Nat.lt_trichotomy j i with h | h | h
    · exact comm_facts (hc i hi) j h
    · rw [h]
    · exact (comm_facts (hc j hj) i h).symm
  have hconj1 : ∀ l < gens.size, ∀ j < m, ∃ a < m,
      conjT n gens[l]! gensInv[l]! (arrTable (unpack n w (E j))) = arrTable (unpack n w (E a)) := by
    intro l hl j hj
    obtain ⟨⟨a, ha, ea⟩, -⟩ := (hrows j hj).1 l (by omega)
    refine ⟨a, ha, ?_⟩
    rw [hgt l (by omega), hgit l (by omega), conjT_tab hn32 (hGr l (by omega)).2 (hEc j hj).2, ea]
  have hconj2 : ∀ l < gens.size, ∀ j < m, ∃ b < m,
      conjT n gensInv[l]! gens[l]! (arrTable (unpack n w (E j))) = arrTable (unpack n w (E b)) := by
    intro l hl j hj
    obtain ⟨-, ⟨b, hb, eb⟩⟩ := (hrows j hj).1 l (by omega)
    refine ⟨b, hb, ?_⟩
    rw [hgt l (by omega), hgit l (by omega), conjT_tab hn32 (hGr l (by omega)).1 (hEc j hj).2, eb]
  subst hq hy
  have hq0 : arrTable (unpack n w Q) = arrTable (unpack n w (E 0)) := by rw [hE0]
  have hReachE : ∀ u, Reach n gens gensInv (arrTable (unpack n w Q)) u →
      ∃ j < m, u = arrTable (unpack n w (E j)) := by
    intro u hu
    induction hu with
    | base => exact ⟨0, hm0, hq0⟩
    | step l hl hz ih =>
      obtain ⟨j, hj, rfl⟩ := ih
      obtain ⟨a, ha, e⟩ := hconj1 l hl j hj
      exact ⟨a, ha, e⟩
  have hEReach : ∀ j < m, Reach n gens gensInv (arrTable (unpack n w Q))
      (arrTable (unpack n w (E j))) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hj0 : j = 0
      · subst hj0
        rw [← hq0]
        exact Reach.base
      · obtain ⟨p', hp', l, hl, e⟩ := (hrows j hj).2 hj0
        have h1 := Reach.step l (by omega) (ih p' hp' (by omega))
        have h2 : conjT n gens[l]! gensInv[l]! (arrTable (unpack n w (E p'))) =
            arrTable (unpack n w (E j)) := by
          rw [hgt l (by omega), hgit l (by omega),
            conjT_tab hn32 (hGr l hl).2 (hEc p' (by omega)).2, e]
        rw [← h2]
        exact h1
  have hinj : ∀ u v, Reach n gens gensInv (arrTable (unpack n w Q)) u →
      Reach n gens gensInv (arrTable (unpack n w Q)) v → key n u = key n v → u = v := by
    intro u v hu hv huv
    obtain ⟨j, hj, rfl⟩ := hReachE u hu
    obtain ⟨j', hj', rfl⟩ := hReachE v hv
    rw [key_tab_inj hn32 hw (hEc j hj) (hEc j' hj') huv]
  classical
  let φ : Table → ℕ := fun u =>
    if h : ∃ j, j < m ∧ u = arrTable (unpack n w (E j)) then Classical.choose h else 0
  have hφ : ∀ u, Reach n gens gensInv (arrTable (unpack n w Q)) u →
      φ u < m ∧ u = arrTable (unpack n w (E (φ u))) := by
    intro u hu
    obtain ⟨j, hj, e⟩ := hReachE u hu
    have h : ∃ j, j < m ∧ u = arrTable (unpack n w (E j)) := ⟨j, hj, e⟩
    simp only [φ, h, ↓reduceDIte]
    exact Classical.choose_spec h
  obtain ⟨st, hcl, hb, hD, hcomp⟩ := closure_spec hinj φ
    (fun u hu => lt_of_lt_of_le (hφ u hu).1 hm)
    (fun u v hu hv e => by rw [(hφ u hu).2, (hφ v hv).2, e])
  have hmem1 : ∀ s ∈ st.1.toList, ∃ j < m, s = arrTable (unpack n w (E j)) := by
    intro s hs
    obtain ⟨k', hk', rfl⟩ := exists_getElem!_of_mem hs
    exact hReachE _ (hb.reach k' hk')
  have hmem2 : ∀ j < m, ∃ s ∈ st.1.toList, s = arrTable (unpack n w (E j)) := by
    intro j hj
    obtain ⟨k', hk', e⟩ := hcomp _ (hEReach j hj)
    exact ⟨_, getElem!_mem hk', e⟩
  unfold threeWitnessK
  dsimp only
  rw [hcl]
  dsimp only
  rw [Bool.and_eq_true]
  refine ⟨conjTreeOKK_of_BI hb, ?_⟩
  unfold witnessCoreK
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro s hs l hl
    obtain ⟨j, hj, rfl⟩ := hmem1 s hs
    have hl' : l < gens.size := List.mem_range.1 hl
    obtain ⟨a, ha, ea⟩ := hconj1 l hl' j hj
    obtain ⟨b, hb', eb⟩ := hconj2 l hl' j hj
    obtain ⟨s1, hs1, e1⟩ := hmem2 a ha
    obtain ⟨s2, hs2, e2⟩ := hmem2 b hb'
    refine ⟨⟨s1, hs1, ?_⟩, ⟨s2, hs2, ?_⟩⟩
    · rw [ea, e1]
      exact tblEqK_refl n _
    · rw [eb, e2]
      exact tblEqK_refl n _
  · intro s hs s' hs'
    obtain ⟨j, hj, rfl⟩ := hmem1 s hs
    obtain ⟨j', hj', rfl⟩ := hmem1 s' hs'
    unfold commTK
    rw [compT_tab hn32 (hEc j' hj').2, compT_tab hn32 (hEc j hj).2, hcom j hj j' hj']
    exact tblEqK_refl n _
  · obtain ⟨s, hs, e⟩ := hmem2 nc hnc
    refine ⟨s, hs, ?_⟩
    rw [e]
    cases hcc : commTK n (arrTable (unpack n w Y)) (arrTable (unpack n w (E nc)))
    · rfl
    · exfalso
      unfold commTK at hcc
      rw [compT_tab hn32 (hEc nc hnc).2, compT_tab hn32 hY'.2] at hcc
      have hA := cn_pcomp hn32 hw hY' (hEc nc hnc)
      have hB := cn_pcomp hn32 hw (hEc nc hnc) hY'
      have h1 := tblEqK_iff.1 hcc
      have heq : pcomp n w (mask w) Y (E nc) = pcomp n w (mask w) (E nc) Y :=
        CFSG.KS.PF.eq_of_fields hw hA.1 hB.1 (fun i hi => by
          have h2 := h1 i hi
          rwa [tab_ap hn32 hA hi, tab_ap hn32 hB hi] at h2)
      have h3 : commP n w Y (E nc) = true := by
        unfold commP
        rw [heq]
        exact Nat.beq_refl _
      rw [hcomm] at h3
      exact Bool.false_ne_true h3
  · exact ordTestK_of hn hY' hY3 hYne

end BFS

end Search

theorem threeWitnessOK_of_P {n w k m nc cap Q Y : Nat} {G GI E R : Nat → Nat}
    {gens gensInv : Array Table} {q y : Table} (hn : CFSG.KS.Raw.szOK n w = true)
    (hg : gens.size = k ∧ ∀ l < k, gens[l]! = arrTable (unpack n w (G l)))
    (hgi : gensInv.size = k ∧ ∀ l < k, gensInv[l]! = arrTable (unpack n w (GI l)))
    (hp : ∀ l < k, permOK n w (mask w) (n * w) (G l) (GI l) = true)
    (hq : q = arrTable (unpack n w Q)) (hy : y = arrTable (unpack n w Y)) (hm : m ≤ cap)
    (hh : headWP n w E m Q Y nc = true) (hr : ∀ j < m, rowWP n w G GI k E R m j = true)
    (hc : ∀ i < m, commWP n w E i = true) :
    threeWitnessOK n gens gensInv q y cap = true :=
  CFSG.KC.LocalComp.ThreeW.threeWitnessOK_of_K
    (threeWitnessK_of_P hn hg hgi hp hq hy hm hh hr hc)

end CFSG.KC.LocalComp.ThreeWP

end
