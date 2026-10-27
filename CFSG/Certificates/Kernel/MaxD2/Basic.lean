module

public import Certificates.Data.MaxD2Perm
public import Certificates.Data.Kernel.MaxD2.Check
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.PSL3Four.Native
open Certificates.MaxD2Perm

abbrev Cn (n w p : Nat) : Prop := canonK n w (mask w) (n * w) p = true

theorem band_e {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := (bAnd_iff a b).1 h

theorem bif_t {c t e : Bool} (hc : c = true) (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    t = true := by
  subst hc
  exact h

theorem bif_f {c t e : Bool} (hc : c = false) (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    e = true := by
  subst hc
  exact h

theorem bor_e {c x : Bool} (h : Bool.rec (motive := fun _ => Bool) x true c = true) :
    c = true ∨ x = true := by
  cases c
  · exact Or.inr h
  · exact Or.inl rfl

theorem bnot_e {c : Bool} (h : Bool.rec (motive := fun _ => Bool) true false c = true) :
    c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

section

variable {n w : Nat}

theorem size_u (p : Nat) : (unpack n w p).size = n := by simp [unpack]

theorem get_u {p i : Nat} (hi : i < n) : (unpack n w p)[i]! = pg w (mask w) p i := by
  simp only [unpack]
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem tab_ext {a b : Tab} (ha : a.size = n) (hb : b.size = n) (h : ∀ i < n, a[i]! = b[i]!) :
    a = b := by
  apply Array.ext (by rw [ha, hb])
  intro i h1 h2
  have e := h i (by omega)
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at e

theorem comp_get {a b : Tab} {i : Nat} (hi : i < n) : (comp n a b)[i]! = a[b[i]!]! := by
  unfold comp
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem comp_size (a b : Tab) : (comp n a b).size = n := by simp [comp]

theorem canon_lt {p : Nat} (hp : Cn n w p) {i : Nat} (hi : i < n) : pg w (mask w) p i < n :=
  (CFSG.KS.PF.canon_facts hp).2.2.2 i hi

theorem comp_u {p q : Nat} (hp : Cn n w p) (hq : Cn n w q) :
    comp n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem cc {p q : Nat} (hp : Cn n w p) (hq : Cn n w q) : Cn n w (pcomp n w (mask w) p q) :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem u_inj {p q : Nat} (hp : Cn n w p) (hq : Cn n w q) (h : unpack n w p = unpack n w q) :
    p = q := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hq
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [← get_u hi, ← get_u hi, h]

theorem eq_u {p q : Nat} (hp : Cn n w p) (hq : Cn n w q) :
    (unpack n w p == unpack n w q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · rw [beq_eq_false_iff_ne]
    intro e
    have := u_inj hp hq e
    rw [this, Nat.beq_refl] at h
    exact absurd h (by simp)
  · rw [Nat.eq_of_beq_eq_true h, beq_self_eq_true]

theorem id_u (hn : szOK n w = true) : idTab n = unpack n w (pidn n w) := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Raw.Orb.szOK_facts hn
  refine tab_ext (by simp [idTab]) (size_u _) fun i hi => ?_
  rw [get_u hi, CFSG.KS.PF.pg_pidn h1 h2 hi]
  unfold idTab
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem perm_spec {p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    (∀ i < n, pg w (mask w) p i < n ∧ pg w (mask w) q (pg w (mask w) p i) = i) ∧
      (∀ j < n, pg w (mask w) q j < n ∧ pg w (mask w) p (pg w (mask w) q j) = j) := by
  have hpr : ∀ i < n, pg w (mask w) p i < n ∧ pg w (mask w) q (pg w (mask w) p i) = i := by
    intro i hi
    unfold permOK at h
    simp only [PK.bAnd_eq, Bool.and_eq_true] at h
    have := (PK.allN_iff.1 h.2.2) i hi
    simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  refine ⟨hpr, ?_⟩
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => pg w (mask w) p a) (fun a ha => by simpa using (hpr a (by simpa using ha)).1)
    (fun a₁ a₂ h₁ h₂ e => by
      have e1 := (hpr a₁ (by simpa using h₁)).2
      have e2 := (hpr a₂ (by simpa using h₂)).2
      have e' : pg w (mask w) p a₁ = pg w (mask w) p a₂ := e
      rw [e'] at e1
      omega) le_rfl
  intro j hj
  obtain ⟨i, hi, e⟩ := hsurj j (by simpa using hj)
  have hi' : i < n := by simpa using hi
  have e' : pg w (mask w) p i = j := e.symm
  rw [← e', (hpr i hi').2]
  exact ⟨hi', rfl⟩

theorem perm_canon {p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) (hn : szOK n w = true) :
    Cn n w p ∧ Cn n w q := by
  have h' := h
  unfold permOK at h'
  simp only [PK.bAnd_eq, Bool.and_eq_true] at h'
  have hs := perm_spec h
  unfold Cn canonK
  simp only [PK.bAnd_eq, Bool.and_eq_true, hn, true_and]
  refine ⟨⟨h'.1, PK.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hs.1 i hi).1⟩,
    ⟨h'.2.1, PK.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hs.2 i hi).1⟩⟩

theorem inv_u {p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    invTab n (unpack n w p) = unpack n w q :=
  (invEqK_sound h).1

theorem inv_comp {p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    comp n (unpack n w q) (unpack n w p) = idTab n := by
  refine tab_ext (comp_size _ _) (by simp [idTab]) fun i hi => ?_
  rw [comp_get hi, get_u hi, get_u ((perm_spec h).1 i hi).1, ((perm_spec h).1 i hi).2]
  unfold idTab
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem comp_inv {p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    comp n (unpack n w p) (unpack n w q) = idTab n := by
  refine tab_ext (comp_size _ _) (by simp [idTab]) fun i hi => ?_
  rw [comp_get hi, get_u hi, get_u ((perm_spec h).2 i hi).1, ((perm_spec h).2 i hi).2]
  unfold idTab
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem pidn_canon (hn : szOK n w = true) : Cn n w (pidn n w) := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Raw.Orb.szOK_facts hn
  unfold Cn canonK
  simp only [PK.bAnd_eq, Bool.and_eq_true, hn, true_and]
  refine ⟨?_, PK.allN_iff.2 fun i hi => Nat.blt_eq.mpr ?_⟩
  · have := CFSG.KS.PF.pidn_shr h1 h2
    simp only [Nat.shiftRight_eq] at this ⊢
    rw [this]
    rfl
  · rw [CFSG.KS.PF.pg_pidn h1 h2 hi]
    exact hi

theorem pidn_get (hn : szOK n w = true) {i : Nat} (hi : i < n) : pg w (mask w) (pidn n w) i = i :=
  CFSG.KS.PF.pg_pidn (CFSG.KS.Raw.Orb.szOK_facts hn).1 (CFSG.KS.Raw.Orb.szOK_facts hn).2 hi

theorem pg_pc (hn : szOK n w = true) {p q i : Nat} (hi : i < n) :
    pg w (mask w) (pcomp n w (mask w) p q) i = pg w (mask w) p (pg w (mask w) q i) :=
  CFSG.KS.PF.pg_pcomp (by have := (CFSG.KS.Raw.Orb.szOK_facts hn).1; omega) hi

theorem pw_canon (hn : szOK n w = true) {p : Nat} (hp : Cn n w p) : ∀ e, Cn n w (pw n w p e)
  | 0 => pidn_canon hn
  | e + 1 => cc hp (pw_canon hn hp e)

theorem powT_u (hn : szOK n w = true) {p : Nat} (hp : Cn n w p) :
    ∀ e, Certificates.FusD2Perm.powT n (unpack n w p) e = unpack n w (pw n w p e)
  | 0 => id_u hn
  | e + 1 => by
    change comp n (unpack n w p) (Certificates.FusD2Perm.powT n (unpack n w p) e) = _
    rw [powT_u hn hp e, comp_u hp (pw_canon hn hp e)]
    rfl

theorem pt_spec {m nw k cnt i : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true) :
    canonK n w m nw (T i) = true ∧ (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧
      T i = stepK n w m conj G GI (labOf PL i) (T (parOf PL i))) := by
  unfold penumPtK at h
  rw [PK.strictB_eq] at h
  obtain ⟨h1, h⟩ := band_e h
  obtain ⟨h2, -⟩ := band_e h
  refine ⟨h1, fun hi => ?_⟩
  have h3 := bif_f (Bool.eq_false_iff.2 (fun e => hi (Nat.eq_of_beq_eq_true e))) h2
  rw [PK.strictB_eq, PK.strictB_eq] at h3
  obtain ⟨a, h3⟩ := band_e h3
  obtain ⟨b, h3⟩ := band_e h3
  obtain ⟨c, -⟩ := band_e h3
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.eq_of_beq_eq_true c⟩

end

theorem allBelow_iff' {m : Nat} {f : Nat → Bool} : allBelow m f = true ↔ ∀ i < m, f i = true := by
  unfold allBelow
  rw [List.all_eq_true]
  simp

theorem anyBelow_iff {m : Nat} {f : Nat → Bool} : anyBelow m f = true ↔ ∃ i < m, f i = true := by
  unfold anyBelow
  rw [List.any_eq_true]
  simp

theorem countBelow_eq {m : Nat} {f g : Nat → Bool} (h : ∀ i < m, f i = g i) :
    countBelow m f = countBelow m g := by
  unfold countBelow
  congr 1
  apply List.filter_congr
  intro x hx
  exact h x (List.mem_range.1 hx)

theorem found_iff (A : Array Tab) (x : Tab) :
    found (indexOf A) A x = true ↔ ∃ i < A.size, A[i]! = x :=
  found_indexOf_iff A x

theorem memFp_iff {pts : List Nat} {T : Array Tab}
    (hinj : ∀ a < T.size, ∀ b < T.size, fpTab pts T[a]! = fpTab pts T[b]! → a = b) (y : Tab) :
    memFp pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T y = true ↔
      ∃ m < T.size, T[m]! = y := by
  have hsz : (T.map (fpTab pts)).size = T.size := by simp
  have hget : ∀ i < T.size, (T.map (fpTab pts))[i]! = fpTab pts T[i]! := fun i hi => by
    rw [getElem!_pos _ i (by simpa using hi), getElem!_pos T i hi]
    simp
  have hinj' : ∀ a < (T.map (fpTab pts)).size, ∀ b < (T.map (fpTab pts)).size,
      (T.map (fpTab pts))[a]! = (T.map (fpTab pts))[b]! → a = b := fun a ha b hb e => by
    rw [hsz] at ha hb
    rw [hget a ha, hget b hb] at e
    exact hinj a ha b hb e
  obtain ⟨h1, -⟩ := CFSG.KS.BfsReplay.indexOf_spec hinj'
  unfold memFp posOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨_, h, e⟩
  · rintro ⟨m, hm, rfl⟩
    rw [← hget m hm, h1 m (by rw [hsz]; exact hm)]
    exact ⟨hm, rfl⟩

theorem fpOK_of {pts : List Nat} {T : Array Tab}
    (hinj : ∀ a < T.size, ∀ b < T.size, fpTab pts T[a]! = fpTab pts T[b]! → a = b) :
    fpOK pts T = true := by
  have hsz : (T.map (fpTab pts)).size = T.size := by simp
  have hget : ∀ i < T.size, (T.map (fpTab pts))[i]! = fpTab pts T[i]! := fun i hi => by
    rw [getElem!_pos _ i (by simpa using hi), getElem!_pos T i hi]
    simp
  have hinj' : ∀ a < (T.map (fpTab pts)).size, ∀ b < (T.map (fpTab pts)).size,
      (T.map (fpTab pts))[a]! = (T.map (fpTab pts))[b]! → a = b := fun a ha b hb e => by
    rw [hsz] at ha hb
    rw [hget a ha, hget b hb] at e
    exact hinj a ha b hb e
  obtain ⟨h1, -⟩ := CFSG.KS.BfsReplay.indexOf_spec hinj'
  unfold fpOK
  simp only [allBelow_iff', beq_iff_eq]
  intro k hk
  unfold posOf
  exact h1 k hk

end CFSG.KS.MaxD2

end
