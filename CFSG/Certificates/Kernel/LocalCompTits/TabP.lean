module

public import Certificates.Data.Kernel.LocalComp.TitsChain
public import CFSG.Certificates.Kernel.LocalCompTits.Defs
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.PK.Enc
import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KS.PK CFSG.KS.TW CFSG.SectionRank.Native.Tits
  CFSG.Sporadic.Th.Native CFSG.KC.LocalComp.Tits

@[expose] def Mp (N P : Nat) : Prop := ∀ i < N, pg 11 (mask 11) P i < N

@[expose] def Bd (N P : Nat) : Prop := P >>> (N * 11) = 0

structure Gd (N P : Nat) : Prop where
  mp : Mp N P
  bd : Bd N P

theorem mask11 : mask 11 = 2047 := rfl

theorem pg_lt11 (P i : Nat) : pg 11 (mask 11) P i < 2048 := by
  have := pg_lt 11 P i
  simpa using this

theorem lt_of_bd {N P : Nat} (h : Bd N P) : P < 2 ^ (N * 11) := by
  unfold Bd at h
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 h

theorem pg_ge_of_bd {N P i : Nat} (h : Bd N P) (hi : N ≤ i) : pg 11 (mask 11) P i = 0 := by
  have h1 := lt_of_bd h
  rw [pg_eq]
  have : P / 2 ^ (11 * i) = 0 :=
    (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).2
      (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [this]

theorem tabP_size (N P : Nat) : (tabP N P).size = N := by
  simp [tabP]

theorem tabP_get {N P i : Nat} (hi : i < N) :
    (tabP N P)[i]! = UInt32.ofNat (pg 11 (mask 11) P i) := by
  unfold tabP
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ap_tabP_lt {N P i : Nat} (hi : i < N) : ap (tabP N P) i = pg 11 (mask 11) P i := by
  unfold ap
  rw [tabP_get hi, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (pg_lt11 _ _) (by decide))

theorem ap_tabP_ge (N P : Nat) {i : Nat} (hi : N ≤ i) : ap (tabP N P) i = 0 := by
  unfold ap
  rw [getElem!_neg _ i (by rw [tabP_size]; omega)]
  rfl

theorem ap_tabP {N P : Nat} (h : Bd N P) (i : Nat) : ap (tabP N P) i = pg 11 (mask 11) P i := by
  by_cases hi : i < N
  · exact ap_tabP_lt hi
  · rw [ap_tabP_ge N P (by omega), pg_ge_of_bd h (by omega)]

theorem tabP_TR {N P : Nat} (hN : N < 2 ^ 32) (h : Mp N P) :
    TR N (tabP N P) (pg 11 (mask 11) P) :=
  ⟨tabP_size N P, fun i hi => ⟨ap_tabP_lt hi, h i hi⟩⟩

theorem TR_ext' {n : Nat} {t u : Table} {f : Nat → Nat} (ht : TR n t f) (hu : TR n u f) :
    t = u := by
  apply Array.ext (by rw [ht.1, hu.1])
  intro i hi1 hi2
  have hi : i < n := by rw [← ht.1]; exact hi1
  have e1 := (ht.2 i hi).1
  have e2 := (hu.2 i hi).1
  unfold ap at e1 e2
  rw [getElem!_pos _ i hi1] at e1
  rw [getElem!_pos _ i hi2] at e2
  exact UInt32.toNat_inj.mp (e1.trans e2.symm)

theorem TR_congr' {n : Nat} {t : Table} {f g : Nat → Nat} (h : TR n t f)
    (hfg : ∀ i < n, f i = g i) : TR n t g :=
  ⟨h.1, fun i hi => by rw [← hfg i hi]; exact h.2 i hi⟩

theorem compT_TR' {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f)
    (hQ : TR n Q g) : TR n (compT n P Q) fun x => f (g x) := by
  refine ⟨by simp [compT], fun i hi => ?_⟩
  obtain ⟨hq1, hq2⟩ := hQ.2 i hi
  obtain ⟨hp1, hp2⟩ := hP.2 _ hq2
  refine ⟨?_, hp2⟩
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have e : (Q[i]!).toNat = g i := hq1
  rw [e]
  exact hp1

theorem powT_TR' {n : Nat} (hn : n < 2 ^ 32) {P : Table} {f : Nat → Nat} (hP : TR n P f) (e : Nat) :
    TR n (powT n e P) (CFSG.KS.PK.itr f e) := by
  induction e with
  | zero => exact idT_TR hn
  | succ e ih => exact compT_TR' (f := f) (g := CFSG.KS.PK.itr f e) hP ih


theorem gd_pidn {N : Nat} (hN : N + 1 < 2048) : Gd N (pidn N 11) :=
  ⟨fun i hi => by rw [pg_pidn (by omega) (by omega) hi]; exact hi,
    pidn_shr (by omega) (by omega)⟩

theorem mp_pcomp {N A B : Nat} (hN : N < 2048) (hB : Mp N B) (hA : Mp N A) :
    Mp N (pcomp N 11 (mask 11) A B) := fun i hi => by
  rw [pg_pcomp (by omega) hi]
  exact hA _ (hB i hi)

theorem gd_pcomp {N A B : Nat} (hN : N < 2048) (hA : Gd N A) (hB : Gd N B) :
    Gd N (pcomp N 11 (mask 11) A B) :=
  ⟨mp_pcomp hN hB.mp hA.mp, pcomp_shr A B (by omega) (by omega)⟩

theorem permOK_facts {N P Q : Nat} (h : permOK N 11 (mask 11) (N * 11) P Q = true) :
    Gd N P ∧ Gd N Q ∧ (∀ i < N, pg 11 (mask 11) Q (pg 11 (mask 11) P i) = i) ∧
      ∀ i < N, pg 11 (mask 11) P (pg 11 (mask 11) Q i) = i := by
  obtain ⟨hP, hQ, hi⟩ := permOK_iff.1 h
  have hi' : ∀ i < N, pg 11 (mask 11) P i < N ∧
      pg 11 (mask 11) Q (pg 11 (mask 11) P i) = i := fun i hi' => by
    rw [pg_eq, pg_eq]; exact hi i hi'
  have hbd : ∀ {R : Nat}, R < 2 ^ (11 * N) → Bd N R := fun {R} hR => by
    unfold Bd
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm N 11]
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).2 hR
  have hinj : ∀ i < N, ∀ j < N, pg 11 (mask 11) P i = pg 11 (mask 11) P j → i = j :=
    fun i hi j hj e => by
      rw [← (hi' i hi).2, ← (hi' j hj).2, e]
  have hsurj := surj_of_inj (f := fun i => pg 11 (mask 11) P i) (fun i hi => (hi' i hi).1) hinj
  have hQmp : Mp N Q := fun i hi => by
    obtain ⟨x, hx, e⟩ := hsurj i hi
    have : pg 11 (mask 11) Q i = x := by rw [← e]; exact (hi' x hx).2
    rw [this]; exact hx
  refine ⟨⟨fun i hi => (hi' i hi).1, hbd hP⟩, ⟨hQmp, hbd hQ⟩, fun i hi => (hi' i hi).2,
    fun i hi => ?_⟩
  obtain ⟨x, hx, e⟩ := hsurj i hi
  have : pg 11 (mask 11) Q i = x := by rw [← e]; exact (hi' x hx).2
  rw [this]; exact e

theorem tabP_pcomp {N A B : Nat} (hN : N < 2048) (hA : Mp N A) (hB : Mp N B) :
    tabP N (pcomp N 11 (mask 11) A B) = compT N (tabP N A) (tabP N B) := by
  refine TR_ext' (tabP_TR (by omega) (mp_pcomp hN hB hA)) ?_
  refine TR_congr' (compT_TR' (tabP_TR (by omega) hA) (tabP_TR (by omega) hB)) ?_
  intro i hi
  rw [pg_pcomp (by omega) hi]

theorem tabP_pidn {N : Nat} (hN : N + 1 < 2048) : tabP N (pidn N 11) = idT N := by
  refine TR_ext' (tabP_TR (by omega) (gd_pidn hN).mp) ?_
  refine TR_congr' (idT_TR (n := N) (by omega)) ?_
  intro i hi
  rw [pg_pidn (by omega) (by omega) hi]

theorem ppow_succ (N P k : Nat) : ppow N 11 (mask 11) (pidn N 11) P (k + 1) =
    pcomp N 11 (mask 11) P (ppow N 11 (mask 11) (pidn N 11) P k) := by
  show strictN _ _ = _
  exact strictN_eqP _ _

theorem gd_ppow {N P : Nat} (hN : N + 1 < 2048) (hP : Gd N P) (k : Nat) :
    Gd N (ppow N 11 (mask 11) (pidn N 11) P k) := by
  induction k with
  | zero => exact gd_pidn hN
  | succ k ih => rw [ppow_succ]; exact gd_pcomp (by omega) hP ih

theorem tabP_ppow {N P : Nat} (hN : N + 1 < 2048) (hP : Gd N P) (k : Nat) :
    tabP N (ppow N 11 (mask 11) (pidn N 11) P k) = powT N k (tabP N P) := by
  induction k with
  | zero => exact tabP_pidn hN
  | succ k ih =>
    rw [ppow_succ, tabP_pcomp (by omega) hP.mp (gd_ppow hN hP k).mp, ih]
    rfl

theorem tabP_inv {N P Q : Nat} (hN : N < 2048)
    (h : permOK N 11 (mask 11) (N * 11) P Q = true) : invT N (tabP N P) = tabP N Q := by
  obtain ⟨hP, hQ, h1, h2⟩ := permOK_facts h
  refine TR_ext' (invT_TR (by omega) (tabP_TR (by omega) hP.mp) fun i hi => ?_)
    (tabP_TR (by omega) hQ.mp)
  exact ⟨hQ.mp i hi, h2 i hi, h1 i hi⟩

theorem invOK_tabP {N P : Nat}
    (h : permOK N 11 (mask 11) (N * 11) P (pinvS N 11 (mask 11) P) = true)
    (hN : N < 2048) : invOK N (tabP N P) (invT N (tabP N P)) = true := by
  rw [tabP_inv hN h]
  obtain ⟨hP, hQ, h1, -⟩ := permOK_facts h
  exact invOK_of (tabP_TR (by omega) hP.mp) (tabP_TR (by omega) hQ.mp) h1


theorem tbls_get {N : Nat} {TG : Nat → Nat} {j : Nat} (hj : j < 4) :
    (Array.ofFn (n := 4) fun s => tabP N (TG s.val))[j]! = tabP N (TG j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem letterT_eq {N : Nat} {TG : Nat → Nat} {tbls : Array Table}
    (hg : tbls = Array.ofFn (n := 4) fun s => tabP N (TG s.val)) (hN : N + 1 < 2048)
    (hTG : ∀ s < 4, permOK N 11 (mask 11) (N * 11) (TG s) (pinvS N 11 (mask 11) (TG s)) = true)
    (z : Int) : letterT N tbls z = tabP N (letK N 11 TG z) ∧ Gd N (letK N 11 TG z) := by
  have hs : tbls.size = 4 := by subst hg; simp
  unfold letterT letK
  rw [hs]
  by_cases h1 : 0 < z ∧ z ≤ 4
  · have h1' : 0 < z ∧ z ≤ ((4 : Nat) : Int) := h1
    have hj : z.toNat - 1 < 4 := by omega
    rw [if_pos h1', if_pos h1, hg, tbls_get hj]
    exact ⟨rfl, (permOK_facts (hTG _ hj)).1⟩
  · by_cases h2 : z < 0 ∧ -z ≤ 4
    · have h2' : z < 0 ∧ -z ≤ ((4 : Nat) : Int) := h2
      have hj : (-z).toNat - 1 < 4 := by omega
      rw [if_neg (by omega), if_neg h1, if_pos h2', if_pos h2, hg, tbls_get hj]
      exact ⟨tabP_inv (by omega) (hTG _ hj), (permOK_facts (hTG _ hj)).2.1⟩
    · rw [if_neg (by omega), if_neg h1, if_neg (by omega), if_neg h2]
      exact ⟨(tabP_pidn hN).symm, gd_pidn hN⟩

theorem map_eq_compT {N : Nat} {L T : Table} (hT : T.size = N) :
    T.map (fun t => L[t.toNat]!) = compT N L T := by
  apply Array.ext (by simp [compT, hT])
  intro i h1 h2
  have hi : i < N := by simp [compT] at h2; exact h2
  simp only [compT, Array.getElem_map, Array.getElem_ofFn]
  rw [getElem!_pos T i (by omega)]

theorem wordT_eq {N : Nat} {TG : Nat → Nat} {tbls : Array Table}
    (hg : tbls = Array.ofFn (n := 4) fun s => tabP N (TG s.val)) (hN : N + 1 < 2048)
    (hTG : ∀ s < 4, permOK N 11 (mask 11) (N * 11) (TG s) (pinvS N 11 (mask 11) (TG s)) = true)
    (w : List Int) :
    wordT N (letterT N tbls) w = tabP N (wordK N 11 TG w) ∧ Gd N (wordK N 11 TG w) := by
  induction w with
  | nil =>
    refine ⟨?_, gd_pidn hN⟩
    show idT N = tabP N (pidn N 11)
    exact (tabP_pidn hN).symm
  | cons z zs ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨l1, l2⟩ := letterT_eq hg hN hTG z
    have e : wordK N 11 TG (z :: zs) = pcomp N 11 (mask 11) (letK N 11 TG z) (wordK N 11 TG zs) :=
      strictN_eqP _ _
    have e2 : wordT N (letterT N tbls) (z :: zs) =
        (wordT N (letterT N tbls) zs).map fun t => (letterT N tbls z)[t.toNat]! := rfl
    rw [e, e2, ih1, l1]
    refine ⟨?_, gd_pcomp (by omega) l2 ih2⟩
    rw [map_eq_compT (tabP_size _ _), tabP_pcomp (by omega) l2.mp ih2.mp]

theorem mask11_eq : (CFSG.KC.LocalComp.TitsChain.m11) = mask 11 := rfl

open CFSG.KC.LocalComp.TitsChain in
theorem letters_sound {TG TL : Nat → Nat} {words : Array (List Int)} {tbls : Array Table}
    (hg : tbls = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (h : lettersOK TG TL words = true) :
    CFSG.Perm.Native.buildLetters 1755 (letterT 1755 tbls) words =
      Array.ofFn (n := 2 * words.size) fun l => tabP 1755 (TL l.val) := by
  unfold CFSG.KC.LocalComp.TitsChain.lettersOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hTG : ∀ s < 4, permOK 1755 11 (mask 11) (1755 * 11) (TG s) (pinvS 1755 11 (mask 11) (TG s))
      = true := fun s hs => allN_spec h1 s hs
  unfold CFSG.Perm.Native.buildLetters
  refine congrArg (Array.ofFn (n := 2 * words.size)) (funext fun i => ?_)
  have hj : i.val / 2 < words.size := by omega
  have h3 := allN_spec h2 (i.val / 2) hj
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h5
  have e4 := Nat.eq_of_beq_eq_true h4
  have e6 := Nat.eq_of_beq_eq_true h6
  have hw : words[i.val / 2]! = words.toList.getD (i.val / 2) [] := by
    rw [getElem!_pos words _ hj, List.getD_eq_getElem?_getD]
    simp [hj]
  have hword := wordT_eq hg (by omega) hTG words[i.val / 2]!
  have e4' : TL (2 * (i.val / 2)) = wordK 1755 11 TG words[i.val / 2]! := by
    rw [hw]; exact e4
  have h7' : permOK 1755 11 (mask 11) (1755 * 11) (TL (2 * (i.val / 2)))
      (TL (2 * (i.val / 2) + 1)) = true := h7
  generalize hjd : i.val / 2 = j at *
  have hi2 : i.val = 2 * j ∨ i.val = 2 * j + 1 := by omega
  show (if i.val % 2 = 0 then wordT 1755 (letterT 1755 tbls) words[j]! else
    invT 1755 (wordT 1755 (letterT 1755 tbls) words[j]!)) = tabP 1755 (TL i.val)
  rcases hi2 with hi | hi
  · rw [hi, if_pos (by omega), hword.1, ← e4']
  · rw [hi, if_neg (by omega), hword.1, ← e4']
    exact tabP_inv (by omega) h7'

end CFSG.KC.LocalComp.TitsSound

end
