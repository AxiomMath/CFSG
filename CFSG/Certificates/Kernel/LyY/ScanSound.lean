module

public import CFSG.Certificates.Kernel.J2EnumSound
public import Certificates.Data.Kernel.LyY.Orb
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.VOrbSound
import all CFSG.Certificates.Kernel.J2Enum.Count
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.KC.LyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Enum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

@[expose] def pairLetW (x y xi yi : Table) (l : Int) : Table :=
  if l = 1 then x else if l = -1 then xi else if l = 2 then y else yi

@[expose] def relTestW (n : Nat) (R W : List (List Int)) (x y : Table) : Bool :=
  let xi := invT n x
  let yi := invT n y
  invOK n x xi && invOK n y yi && R.all (fun w => powFixW n (w.map (pairLetW x y xi yi)) 1) &&
    W.all (fun w => !powFixW n (w.map (pairLetW x y xi yi)) 1)

@[expose] def lettersTwo (R : List (List Int)) : Prop :=
  ∀ w ∈ R, ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2

private theorem ksLY_lenN_eq : ∀ l : List Nat, lenN l = l.length
  | [] => rfl
  | _ :: l => by
    rw [show lenN (_ :: l) = Nat.succ (lenN l) from rfl, ksLY_lenN_eq l, List.length_cons]

private theorem ksLY_memN_iff (p : Nat) : ∀ l : List Nat, memN p l = true ↔ p ∈ l
  | [] => by simp only [memN, List.not_mem_nil, Bool.false_eq_true]
  | x :: l => by
    change Bool.rec (motive := fun _ => Bool) (memN p l) true (Nat.beq x p) = true ↔
      p ∈ x :: l
    rw [CFSG.KS.Raw.Orb.bIf_eq]
    by_cases h : Nat.beq x p = true
    · have hxp : x = p := Nat.eq_of_beq_eq_true h
      rw [if_pos h]
      simp [hxp]
    · have hxp : x ≠ p := fun e => h (by rw [e, Nat.beq_refl])
      rw [if_neg h, ksLY_memN_iff p l]
      simp only [List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hmem)
        · exact absurd rfl hxp
        · exact hmem

private theorem ksLY_allL_iff (f : Nat → Bool) : ∀ l : List Nat,
    allL f l = true ↔ ∀ x ∈ l, f x = true
  | [] => by simp [allL]
  | x :: l => by
    change Bool.rec (motive := fun _ => Bool) false (allL f l) (f x) = true ↔ _
    rw [CFSG.KS.bAnd_iff, ksLY_allL_iff f l]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨hx, hl⟩ y (rfl | hy)
      · exact hx
      · exact hl y hy
    · intro h
      exact ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩

private theorem ksLY_incN_cons : ∀ {a : Nat} {as : List Nat}, incN (a :: as) = true →
    incN as = true ∧ ∀ x ∈ as, a < x
  | a, [], _ => ⟨rfl, by simp⟩
  | a, b :: bs, h => by
    change Bool.rec (motive := fun _ => Bool) false (incN (b :: bs)) (Nat.blt a b) = true at h
    rw [CFSG.KS.bAnd_iff, Nat.blt_eq] at h
    obtain ⟨hab, hb⟩ := h
    obtain ⟨hbs, hlt⟩ := ksLY_incN_cons (a := b) hb
    refine ⟨hb, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab
    · have := hlt x hx
      omega

private theorem ksLY_incN_nodup : ∀ {l : List Nat}, incN l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: as, h => by
    obtain ⟨has, hlt⟩ := ksLY_incN_cons h
    exact List.nodup_cons.mpr ⟨fun ha => Nat.lt_irrefl a (hlt a ha), ksLY_incN_nodup has⟩

private theorem ksLY_eq_of_inc_mem : ∀ {l l' : List Nat}, incN l = true → incN l' = true →
    l.length = l'.length → (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], l', _, hl', hlen, _ => by
    have : l' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    simp [this]
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | a :: as, b :: bs, hl, hl', hlen, hmem => by
    have hlen' : as.length = bs.length := by simpa using hlen
    have hab : a = b := by
      by_cases h : a = b
      · exact h
      · have ha : a ∈ b :: bs := (hmem a).1 (by simp)
        have hb : b ∈ a :: as := (hmem b).2 (by simp)
        have ha' : a ∈ bs := by
          rcases List.mem_cons.mp ha with h' | h'
          · exact absurd h' h
          · exact h'
        have hb' : b ∈ as := by
          rcases List.mem_cons.mp hb with h' | h'
          · exact absurd h'.symm h
          · exact h'
        have h1 : b < a := (ksLY_incN_cons hl').2 a ha'
        have h2 : a < b := (ksLY_incN_cons hl).2 b hb'
        omega
    have hmem' : ∀ x, x ∈ as ↔ x ∈ bs := by
      intro x
      have h' := hmem x
      rw [hab] at h'
      by_cases hx : x = b
      · rw [hx]
        have ha : b ∉ as := by
          intro hba
          have hlt : a < b := (ksLY_incN_cons hl).2 b hba
          omega
        have hb : b ∉ bs := fun hbb => Nat.lt_irrefl b ((ksLY_incN_cons hl').2 b hbb)
        simp [ha, hb]
      · simpa [hx] using h'
    rw [hab, ksLY_eq_of_inc_mem (ksLY_incN_cons hl).1 (ksLY_incN_cons hl').1 hlen' hmem']

private def ksLY_letter (l : Int) : Prop := l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2

private def ksLY_per {n : Nat} (x y : Equiv.Perm (Fin n)) (l : Int) : Equiv.Perm (Fin n) :=
  if l = 1 then x else if l = -1 then x⁻¹ else if l = 2 then y else y⁻¹

private def ksLY_wperm {n : Nat} (per : Int → Equiv.Perm (Fin n)) :
    List Int → Equiv.Perm (Fin n)
  | [] => 1
  | l :: ls => per l * ksLY_wperm per ls

private theorem ksLY_letP_one (x xi y yi : Nat → Nat) (q : Nat) :
    letP x xi y yi (CFSG.KS.Mathieu.icode 1) q = x q := rfl

private theorem ksLY_letP_neg_one (x xi y yi : Nat → Nat) (q : Nat) :
    letP x xi y yi (CFSG.KS.Mathieu.icode (-1)) q = xi q := rfl

private theorem ksLY_letP_two (x xi y yi : Nat → Nat) (q : Nat) :
    letP x xi y yi (CFSG.KS.Mathieu.icode 2) q = y q := rfl

private theorem ksLY_letP_neg_two (x xi y yi : Nat → Nat) (q : Nat) :
    letP x xi y yi (CFSG.KS.Mathieu.icode (-2)) q = yi q := rfl

private theorem ksLY_letP_eq {n : Nat} {x xi y yi : Nat → Nat}
    {ξ η : Equiv.Perm (Fin n)} (hx : CntPf.Acts n x ξ) (hxi : CntPf.Acts n xi ξ⁻¹)
    (hy : CntPf.Acts n y η) (hyi : CntPf.Acts n yi η⁻¹) {l : Int} (hl : ksLY_letter l)
    {q : Nat} (hq : q < n) :
    letP x xi y yi (CFSG.KS.Mathieu.icode l) q = (ksLY_per ξ η l ⟨q, hq⟩ : Nat) := by
  rcases hl with rfl | rfl | rfl | rfl
  · rw [ksLY_letP_one]
    simp [ksLY_per, hx q hq]
  · rw [ksLY_letP_neg_one]
    simp [ksLY_per, hxi q hq]
  · rw [ksLY_letP_two]
    simp [ksLY_per, hy q hq]
  · rw [ksLY_letP_neg_two]
    simp [ksLY_per, hyi q hq]

private theorem ksLY_per_mem {n : Nat} {Γ : Subgroup (Equiv.Perm (Fin n))}
    {ξ η : Equiv.Perm (Fin n)} (hξ : ξ ∈ Γ) (hη : η ∈ Γ) {l : Int}
    (hl : ksLY_letter l) : ksLY_per ξ η l ∈ Γ := by
  rcases hl with rfl | rfl | rfl | rfl
  · simpa [ksLY_per] using hξ
  · simpa [ksLY_per] using inv_mem hξ
  · simpa [ksLY_per] using hη
  · simpa [ksLY_per] using inv_mem hη

private theorem ksLY_wperm_mem {n : Nat} {Γ : Subgroup (Equiv.Perm (Fin n))}
    {ξ η : Equiv.Perm (Fin n)} (hξ : ξ ∈ Γ) (hη : η ∈ Γ) :
    ∀ wd : List Int, (∀ l ∈ wd, ksLY_letter l) → ksLY_wperm (ksLY_per ξ η) wd ∈ Γ
  | [], _ => one_mem Γ
  | l :: ls, hl => by
    change ksLY_per ξ η l * ksLY_wperm (ksLY_per ξ η) ls ∈ Γ
    exact mul_mem (ksLY_per_mem hξ hη (hl l (by simp)))
      (ksLY_wperm_mem hξ hη ls fun x hx => hl x (by simp [hx]))

private theorem ksLY_wP_cons (x xi y yi : Nat → Nat) (l : Int) (ls : List Int) (p : Nat) :
    wP x xi y yi (l :: ls) p =
      letP x xi y yi (CFSG.KS.Mathieu.icode l) (wP x xi y yi ls p) := by
  change strictN (wP x xi y yi ls p)
    (fun q => letP x xi y yi (CFSG.KS.Mathieu.icode l) q) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq]

private theorem ksLY_acts_wP {n : Nat} {x xi y yi : Nat → Nat}
    {ξ η : Equiv.Perm (Fin n)} (hx : CntPf.Acts n x ξ) (hxi : CntPf.Acts n xi ξ⁻¹)
    (hy : CntPf.Acts n y η) (hyi : CntPf.Acts n yi η⁻¹) :
    ∀ wd : List Int, (∀ l ∈ wd, ksLY_letter l) →
      CntPf.Acts n (wP x xi y yi wd) (ksLY_wperm (ksLY_per ξ η) wd)
  | [], _ => fun p _ => by simp [wP, ksLY_wperm]
  | l :: ls, hl => fun p hp => by
    have ih := ksLY_acts_wP hx hxi hy hyi ls (fun z hz => hl z (by simp [hz])) p hp
    have hp' : wP x xi y yi ls p < n := by
      rw [ih]; exact (ksLY_wperm (ksLY_per ξ η) ls ⟨p, hp⟩).2
    rw [ksLY_wP_cons]
    change letP x xi y yi (CFSG.KS.Mathieu.icode l) (wP x xi y yi ls p) =
      ((ksLY_per ξ η l * ksLY_wperm (ksLY_per ξ η) ls) ⟨p, hp⟩ : Nat)
    rw [ksLY_letP_eq hx hxi hy hyi (hl l (by simp)) hp', Equiv.Perm.mul_apply]
    exact congrArg (fun z : Fin n => ((ksLY_per ξ η l) z : Nat)) (Fin.ext ih)

private theorem ksLY_acts_apW {n : Nat} {per : Int → Equiv.Perm (Fin n)}
    {tbl : Int → Table} (htbl : ∀ l, ksLY_letter l → CntPf.Acts n (ap (tbl l)) (per l)) :
    ∀ wd : List Int, (∀ l ∈ wd, ksLY_letter l) →
      CntPf.Acts n (apW (wd.map tbl)) (ksLY_wperm per wd)
  | [], _ => fun p _ => by simp [apW, ksLY_wperm]
  | l :: ls, hl => fun p hp => by
    have ih := ksLY_acts_apW htbl ls (fun z hz => hl z (by simp [hz])) p hp
    have hp' : apW (ls.map tbl) p < n := by
      rw [ih]; exact (ksLY_wperm per ls ⟨p, hp⟩).2
    change ap (tbl l) (apW (ls.map tbl) p) =
      ((per l * ksLY_wperm per ls) ⟨p, hp⟩ : Nat)
    rw [htbl l (hl l (by simp)) (apW (ls.map tbl) p) hp', Equiv.Perm.mul_apply]
    exact congrArg (fun z : Fin n => ((per l) z : Nat)) (Fin.ext ih)

private theorem ksLY_itP_one (f : Nat → Nat) (p : Nat) : itP f 1 p = f p := by
  change strictN p f = f p
  rw [CFSG.KS.Raw.Orb.strictN_eq]

private theorem ksLY_idW_eq_fix3 (w m BP : Nat) (x xi y yi : Nat → Nat) (wd : List Int) :
    idW w m BP x xi y yi wd = fix3 w m BP (wP x xi y yi wd) 1 := by
  unfold idW fix3
  simp only [ksLY_itP_one]

private theorem ksLY_idW_eq_powFixW {n w BP : Nat} {Γ : Subgroup (Equiv.Perm (Fin n))}
    {x xi y yi : Nat → Nat} {ξ η : Equiv.Perm (Fin n)} {tbl : Int → Table}
    (hbp : ∀ t < 3, pg w (mask w) BP t < n)
    (hsep : ∀ γ : Equiv.Perm (Fin n), γ ∈ Γ →
      (∀ t < 3, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
    (hx : CntPf.Acts n x ξ) (hxi : CntPf.Acts n xi ξ⁻¹)
    (hy : CntPf.Acts n y η) (hyi : CntPf.Acts n yi η⁻¹)
    (hξ : ξ ∈ Γ) (hη : η ∈ Γ)
    (htbl : ∀ l, ksLY_letter l → CntPf.Acts n (ap (tbl l)) (ksLY_per ξ η l))
    (wd : List Int) (hl : ∀ l ∈ wd, ksLY_letter l) :
    idW w (mask w) BP x xi y yi wd = powFixW n (wd.map tbl) 1 := by
  rw [ksLY_idW_eq_fix3]
  rw [CntPf.fix3_eq hbp hsep (ksLY_acts_wP hx hxi hy hyi wd hl)
    (ksLY_wperm_mem hξ hη wd hl)]
  rw [CntPf.powFixW_eq (ksLY_acts_apW htbl wd hl) 1]

private theorem ksLY_all_eq_of_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.all_cons, List.all_cons, h a (by simp),
      ih fun x hx => h x (by simp [hx])]

private theorem ksLY_acts_tabP {n w P : Nat} {γ : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (h : Raw.Orb.PRep n w P γ) : CntPf.Acts n (ap (tabP n w P)) γ := fun p hp => by
  have hp' : pg w (mask w) P p < 2 ^ 32 := by
    rw [h ⟨p, hp⟩]
    exact lt_of_lt_of_le (γ ⟨p, hp⟩).2 (by omega)
  rw [ap_tabP hp hp']
  exact h ⟨p, hp⟩

private theorem ksLY_pairLetW_invT_acts {n w X Y : Nat} {ξ η : Equiv.Perm (Fin n)}
    (hx : CntPf.Acts n (ap (tabP n w X)) ξ)
    (hxi : CntPf.Acts n (ap (invT n (tabP n w X))) ξ⁻¹)
    (hy : CntPf.Acts n (ap (tabP n w Y)) η)
    (hyi : CntPf.Acts n (ap (invT n (tabP n w Y))) η⁻¹) :
    ∀ l, ksLY_letter l → CntPf.Acts n
      (ap (pairLetW (tabP n w X) (tabP n w Y) (invT n (tabP n w X))
        (invT n (tabP n w Y)) l)) (ksLY_per ξ η l) := by
  intro l hl
  rcases hl with rfl | rfl | rfl | rfl
  · simpa [pairLetW, ksLY_per] using hx
  · simpa [pairLetW, ksLY_per] using hxi
  · simpa [pairLetW, ksLY_per] using hy
  · simpa [pairLetW, ksLY_per] using hyi

private theorem ksLY_relB_R_eq (w m BP : Nat) (x xi f g : Nat → Nat) (R : List (List Int)) :
    List.rec (motive := fun _ => Bool) true
      (fun wd _ ih => Bool.rec (motive := fun _ => Bool) false ih
        (idW w m BP x xi f g wd)) R =
    R.all (fun wd => idW w m BP x xi f g wd) := by
  induction R with
  | nil => rfl
  | cons a as ih =>
    change Bool.rec (motive := fun _ => Bool) false
      (List.rec (motive := fun _ => Bool) true
        (fun wd _ ih => Bool.rec (motive := fun _ => Bool) false ih
          (idW w m BP x xi f g wd)) as) (idW w m BP x xi f g a) =
      List.all (a :: as) (fun wd => idW w m BP x xi f g wd)
    rw [CFSG.KS.Raw.Orb.bAnd_eq, List.all_cons, ih]

private theorem ksLY_relB_W_eq (w m BP : Nat) (x xi f g : Nat → Nat) (W : List (List Int)) :
    List.rec (motive := fun _ => Bool) true
      (fun wd _ ih => Bool.rec (motive := fun _ => Bool) false ih
        (Bool.rec (motive := fun _ => Bool) true false (idW w m BP x xi f g wd))) W =
    W.all (fun wd => Bool.rec (motive := fun _ => Bool) true false
      (idW w m BP x xi f g wd)) := by
  induction W with
  | nil => rfl
  | cons a as ih =>
    change Bool.rec (motive := fun _ => Bool) false
      (List.rec (motive := fun _ => Bool) true
        (fun wd _ ih => Bool.rec (motive := fun _ => Bool) false ih
          (Bool.rec (motive := fun _ => Bool) true false
            (idW w m BP x xi f g wd))) as)
      (Bool.rec (motive := fun _ => Bool) true false (idW w m BP x xi f g a)) =
      List.all (a :: as) (fun wd => Bool.rec (motive := fun _ => Bool) true false
        (idW w m BP x xi f g wd))
    rw [CFSG.KS.Raw.Orb.bAnd_eq, List.all_cons, ih]

private theorem ksLY_relB_eq {n w BP : Nat} {Γ : Subgroup (Equiv.Perm (Fin n))}
    {X XI Y : Nat} {ξ η : Equiv.Perm (Fin n)} {f g : Nat → Nat}
    (hbp : ∀ t < 3, pg w (mask w) BP t < n)
    (hsep : ∀ γ : Equiv.Perm (Fin n), γ ∈ Γ →
      (∀ t < 3, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
    (hξ : ξ ∈ Γ) (hη : η ∈ Γ) (hX : Raw.Orb.PRep n w X ξ)
    (hXI : Raw.Orb.PRep n w XI ξ⁻¹) (hY : Raw.Orb.PRep n w Y η)
    (hy : CntPf.Acts n f η) (hyi : CntPf.Acts n g η⁻¹) (hn : n < 2 ^ 32)
    (hIX : invOK n (tabP n w X) (invT n (tabP n w X)) = true ∧
      ∀ y (hy : y < n), ap (invT n (tabP n w X)) y = (ξ⁻¹ ⟨y, hy⟩ : Nat))
    (hIY : invOK n (tabP n w Y) (invT n (tabP n w Y)) = true ∧
      ∀ y (hy : y < n), ap (invT n (tabP n w Y)) y = (η⁻¹ ⟨y, hy⟩ : Nat))
    {R W : List (List Int)} (hR : lettersTwo R) (hW : lettersTwo W) :
    relB w (mask w) BP (pg w (mask w) X) (pg w (mask w) XI) f g R W =
      relTestW n R W (tabP n w X) (tabP n w Y) := by
  have hx : CntPf.Acts n (pg w (mask w) X) ξ := CntPf.acts_pg hX
  have hxi : CntPf.Acts n (pg w (mask w) XI) ξ⁻¹ := CntPf.acts_pg hXI
  have hYtab : CntPf.Acts n (ap (tabP n w Y)) η := ksLY_acts_tabP hn hY
  have hIXa : CntPf.Acts n (ap (invT n (tabP n w X))) ξ⁻¹ := fun p hp => hIX.2 p hp
  have hIYa : CntPf.Acts n (ap (invT n (tabP n w Y))) η⁻¹ := fun p hp => hIY.2 p hp
  have htbl := ksLY_pairLetW_invT_acts (ksLY_acts_tabP hn hX) hIXa hYtab hIYa
  have hId : ∀ wd : List Int, (∀ l ∈ wd, ksLY_letter l) →
      idW w (mask w) BP (pg w (mask w) X) (pg w (mask w) XI) f g wd =
        powFixW n (wd.map fun l => pairLetW (tabP n w X) (tabP n w Y)
          (invT n (tabP n w X)) (invT n (tabP n w Y)) l) 1 :=
    fun wd hl => ksLY_idW_eq_powFixW hbp hsep hx hxi hy hyi hξ hη htbl wd hl
  unfold relB
  simp only [relTestW]
  rw [hIX.1, hIY.1, ksLY_relB_R_eq, ksLY_relB_W_eq]
  simp only [Bool.true_and, Bool.and_true]
  rw [CFSG.KS.Raw.Orb.bAnd_eq]
  rw [ksLY_all_eq_of_mem (l := R) fun wd hwd =>
      hId wd fun l hl => hR wd hwd l hl]
  congr 1
  exact ksLY_all_eq_of_mem (l := W) fun wd hwd => by
    rw [CFSG.KS.Raw.Orb.bIf_eq, hId wd fun l hl => hW wd hwd l hl]
    cases powFixW n (wd.map fun l => pairLetW (tabP n w X) (tabP n w Y)
      (invT n (tabP n w X)) (invT n (tabP n w Y)) l) 1 <;> rfl

private def ksLY_apply (n : Nat) (hn : 0 < n) (g : Equiv.Perm (Fin n)) (x : Nat) : Nat :=
  (g ⟨x % n, Nat.mod_lt x hn⟩ : Nat)

private theorem ksLY_mem_image_iff {n : Nat} (hn : 0 < n) (g : Equiv.Perm (Fin n))
    (S : Finset Nat) (hS : ∀ x ∈ S, x < n) {p : Fin n} :
    (p : Nat) ∈ S.image (ksLY_apply n hn g) ↔ ((g⁻¹ p : Fin n) : Nat) ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hyS, hy⟩
    have hyp : y < n := hS y hyS
    have hya : ksLY_apply n hn g y = (g ⟨y, hyp⟩ : Nat) := by
      simp [ksLY_apply, Nat.mod_eq_of_lt hyp]
    rw [hya] at hy
    have hgy : g ⟨y, hyp⟩ = p := Fin.ext hy
    have hpre : g⁻¹ p = ⟨y, hyp⟩ := by rw [← hgy]; simp
    simpa [hpre] using hyS
  · intro h
    refine ⟨((g⁻¹ p : Fin n) : Nat), h, ?_⟩
    simp only [ksLY_apply]
    have hmod : (g⁻¹ p).val % n = (g⁻¹ p).val := Nat.mod_eq_of_lt (g⁻¹ p).2
    have hfin : (⟨(g⁻¹ p).val % n, Nat.mod_lt (g⁻¹ p).val hn⟩ : Fin n) = g⁻¹ p :=
      Fin.ext hmod
    rw [hfin]
    exact congrArg Fin.val (Equiv.apply_symm_apply g p)

private theorem ksLY_img_facts {n w A B k N : Nat} {TL OP OG : List Nat}
    {OS : List (List Nat)} (h : imgOK n w A B TL k OS OP OG N = true) :
    (∀ p ∈ lgetL OS 0, lget TL p = k) ∧
    ∀ i < N, lenN (lgetL OS i) = 12 ∧ incN (lgetL OS i) = true ∧
      (∀ p ∈ lgetL OS i, p < n) ∧
      (i ≠ 0 → lget OP i < i ∧ lget OG i < 2 ∧
        ∀ p ∈ lgetL OS (lget OP i),
          memN (pg w (mask w)
            (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) p)
            (lgetL OS i) = true) := by
  unfold imgOK at h
  rw [CFSG.KS.bAnd_iff] at h
  obtain ⟨h0, hN⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · rw [ksLY_allL_iff] at h0
    exact fun p hp => Nat.eq_of_beq_eq_true (h0 p hp)
  · have hi' := CFSG.KS.allN_spec hN i hi
    rw [CFSG.KS.bAnd_iff] at hi'
    obtain ⟨hl, hi''⟩ := hi'
    rw [CFSG.KS.bAnd_iff] at hi''
    obtain ⟨hinc, hi3⟩ := hi''
    rw [CFSG.KS.bAnd_iff] at hi3
    obtain ⟨hlt, hb⟩ := hi3
    refine ⟨Nat.eq_of_beq_eq_true hl, hinc, ?_, ?_⟩
    · rw [ksLY_allL_iff] at hlt
      exact fun p hp => Nat.blt_eq.mp (hlt p hp)
    · intro hi0
      rw [CFSG.KS.Raw.Orb.bIf_eq] at hb
      have hb' : Nat.beq i 0 = false := by
        cases h : Nat.beq i 0 with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true h) hi0
      rw [if_neg (by rw [hb']; exact Bool.false_ne_true)] at hb
      rw [CFSG.KS.bAnd_iff] at hb
      obtain ⟨hOP, hb2⟩ := hb
      rw [CFSG.KS.bAnd_iff] at hb2
      obtain ⟨hOG, hmem⟩ := hb2
      rw [ksLY_allL_iff] at hmem
      exact ⟨Nat.blt_eq.mp hOP, Nat.blt_eq.mp hOG, fun p hp => hmem p hp⟩

private theorem ksLY_img_rep {n w A B OG : Nat} {α β : Equiv.Perm (Fin n)}
    (hA : Raw.Orb.PRep n w A α) (hB : Raw.Orb.PRep n w B β) :
    ∃ γ ∈ Subgroup.closure ({α, β} : Set (Equiv.Perm (Fin n))),
      Raw.Orb.PRep n w (Bool.rec (motive := fun _ => Nat) B A (Nat.beq OG 0)) γ := by
  by_cases h : Nat.beq OG 0 = true
  · refine ⟨α, Subgroup.subset_closure (by simp), ?_⟩
    rw [show Bool.rec (motive := fun _ => Nat) B A (Nat.beq OG 0) = A
      from by rw [CFSG.KS.Raw.Orb.nIf_eq, if_pos h]]
    exact hA
  · refine ⟨β, Subgroup.subset_closure (by simp), ?_⟩
    rw [show Bool.rec (motive := fun _ => Nat) B A (Nat.beq OG 0) = B
      from by rw [CFSG.KS.Raw.Orb.nIf_eq, if_neg h]]
    exact hB

private theorem ksLY_img_set_eq {n : Nat} {OS : List (List Nat)} {OP : List Nat} {i : Nat}
    (hn : 0 < n)
    (hb0 : ∀ x ∈ lgetL OS 0, x < n)
    (hbP : ∀ x ∈ lgetL OS (lget OP i), x < n)
    {g : Equiv.Perm (Fin n)}
    (hgi : ∀ p : Fin n, (p : Nat) ∈ lgetL OS (lget OP i) ↔
      ((g⁻¹ p : Fin n) : Nat) ∈ lgetL OS 0) :
    (lgetL OS (lget OP i)).toFinset =
      (lgetL OS 0).toFinset.image (ksLY_apply n hn g) := by
  ext x
  rw [Finset.mem_image]
  constructor
  · intro hxP
    have hxlt : x < n := hbP x (by simpa using hxP)
    have hxS : x ∈ (lgetL OS (lget OP i)).toFinset := by simpa using hxP
    have hpre : ((g⁻¹ ⟨x, hxlt⟩ : Fin n) : Nat) ∈ (lgetL OS 0).toFinset := by
      have := (hgi ⟨x, hxlt⟩).1 (by simpa [List.mem_toFinset] using hxS)
      simpa [List.mem_toFinset] using this
    refine ⟨((g⁻¹ ⟨x, hxlt⟩ : Fin n) : Nat), hpre, ?_⟩
    have hmod : (g⁻¹ ⟨x, hxlt⟩).val % n = (g⁻¹ ⟨x, hxlt⟩).val :=
      Nat.mod_eq_of_lt (g⁻¹ ⟨x, hxlt⟩).2
    simp only [ksLY_apply, hmod]
    exact congrArg Fin.val (Equiv.apply_symm_apply g ⟨x, hxlt⟩)
  · rintro ⟨y, hy0, hyx⟩
    have hylt : y < n := hb0 y (by simpa using hy0)
    have hyapply : ksLY_apply n hn g y = (g ⟨y, hylt⟩ : Nat) := by
      simp [ksLY_apply, Nat.mod_eq_of_lt hylt]
    have hxlt : x < n := by
      rw [← hyx, hyapply]
      exact (g ⟨y, hylt⟩).2
    have hgy : (g ⟨y, hylt⟩ : Nat) = x := by rw [← hyapply]; exact hyx
    have hgfin : g ⟨y, hylt⟩ = ⟨x, hxlt⟩ := Fin.ext hgy
    have hpre : ((g⁻¹ ⟨x, hxlt⟩ : Fin n) : Nat) ∈ (lgetL OS 0).toFinset := by
      have hsymm : g⁻¹ ⟨x, hxlt⟩ = ⟨y, hylt⟩ := by rw [← hgfin]; simp
      simpa [hsymm] using hy0
    have hxParent := (hgi ⟨x, hxlt⟩).2 (by simpa [List.mem_toFinset] using hpre)
    simpa [List.mem_toFinset] using hxParent

private theorem ksLY_img_subset {n w A B : Nat} {OG : List Nat}
    {OS : List (List Nat)} {OP : List Nat} {i : Nat} {g γ : Equiv.Perm (Fin n)}
    (hn : 0 < n)
    (hset : (lgetL OS (lget OP i)).toFinset =
      (lgetL OS 0).toFinset.image (ksLY_apply n hn g))
    (himg : ∀ p ∈ lgetL OS (lget OP i),
      memN (pg w (mask w)
        (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) p)
        (lgetL OS i) = true)
    (hγrep : Raw.Orb.PRep n w (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) γ)
    (hb0 : ∀ x ∈ lgetL OS 0, x < n) :
    (lgetL OS 0).toFinset.image (ksLY_apply n hn (γ * g)) ⊆
      (lgetL OS i).toFinset := by
  have hsub : (lgetL OS 0).toFinset.image (ksLY_apply n hn (γ * g)) ⊆
      (lgetL OS i).toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy0, hyx⟩ := hx
    have hylt : y < n := hb0 y (by simpa using hy0)
    have hyapply : ksLY_apply n hn (γ * g) y = (γ (g ⟨y, hylt⟩) : Nat) := by
      simp [ksLY_apply, Nat.mod_eq_of_lt hylt, Equiv.Perm.mul_apply]
    have hyapplyg : ksLY_apply n hn g y = (g ⟨y, hylt⟩ : Nat) := by
      simp [ksLY_apply, Nat.mod_eq_of_lt hylt]
    have hgyS : (g ⟨y, hylt⟩ : Nat) ∈ (lgetL OS (lget OP i)).toFinset := by
      rw [hset, ← hyapplyg]
      exact Finset.mem_image_of_mem _ hy0
    have hmem : (g ⟨y, hylt⟩ : Nat) ∈ lgetL OS (lget OP i) := by
      simpa using hgyS
    have himg' := himg _ hmem
    rw [ksLY_memN_iff] at himg'
    have hpg : pg w (mask w)
        (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) (g ⟨y, hylt⟩) =
        (γ (g ⟨y, hylt⟩) : Nat) := hγrep ⟨g ⟨y, hylt⟩, (g ⟨y, hylt⟩).2⟩
    rw [hpg] at himg'
    rw [List.mem_toFinset]
    rw [← hyx, hyapply]
    exact himg'
  exact hsub

private theorem ksLY_img_next {n w A B : Nat} {OG : List Nat}
    {OS : List (List Nat)} {OP : List Nat} {i : Nat}
    {g γ : Equiv.Perm (Fin n)}
    (hn : 0 < n)
    (hset : (lgetL OS (lget OP i)).toFinset =
      (lgetL OS 0).toFinset.image (ksLY_apply n hn g))
    (himg : ∀ p ∈ lgetL OS (lget OP i),
      memN (pg w (mask w)
        (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) p)
        (lgetL OS i) = true)
    (hγrep : Raw.Orb.PRep n w (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) γ)
    (hcard0 : (lgetL OS 0).toFinset.card = 12)
    (hcardi : (lgetL OS i).toFinset.card = 12)
    (hb0 : ∀ x ∈ lgetL OS 0, x < n) :
    ∀ p : Fin n, (p : Nat) ∈ lgetL OS i ↔
      (((γ * g)⁻¹ p : Fin n) : Nat) ∈ lgetL OS 0 := by
  have hsub := ksLY_img_subset hn hset himg hγrep hb0
  have hcardImg : ((lgetL OS 0).toFinset.image (ksLY_apply n hn (γ * g))).card = 12 := by
    rw [Finset.card_image_of_injOn]
    · exact hcard0
    · intro a ha b hb hab
      have halt : a < n := hb0 a (by simpa using ha)
      have hblt : b < n := hb0 b (by simpa using hb)
      simp only [ksLY_apply, Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] at hab
      have hfin : (γ * g) ⟨a, halt⟩ = (γ * g) ⟨b, hblt⟩ := Fin.ext hab
      exact congrArg Fin.val ((γ * g).injective hfin)
  have hEq : (lgetL OS 0).toFinset.image (ksLY_apply n hn (γ * g)) =
      (lgetL OS i).toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardi, hcardImg])
  intro p
  rw [← List.mem_toFinset, ← hEq,
    ksLY_mem_image_iff hn (γ * g) _ (fun x hx => hb0 x (by simpa using hx)),
    List.mem_toFinset]

private theorem ksLY_img_distinct {n w A B N : Nat} {OP OG : List Nat}
    {OS : List (List Nat)}
    (hfacts : ∀ i < N, lenN (lgetL OS i) = 12 ∧ incN (lgetL OS i) = true ∧
      (∀ p ∈ lgetL OS i, p < n) ∧
      (i ≠ 0 → lget OP i < i ∧ lget OG i < 2 ∧
        ∀ p ∈ lgetL OS (lget OP i),
          memN (pg w (mask w) (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) p)
            (lgetL OS i) = true))
    (hd : distinctOK w OS N = true) {i j : Nat} (hiN : i < N) (hji : j < i) :
    ∃ p : Fin n, ¬ ((p : Nat) ∈ lgetL OS i ↔ (p : Nat) ∈ lgetL OS j) := by
  by_contra hno
  push Not at hno
  obtain ⟨hleni, hinci, hbi, _⟩ := hfacts i hiN
  obtain ⟨hlenj, hincj, hbj, _⟩ := hfacts j (lt_trans hji hiN)
  have hmem : ∀ x : Nat, x ∈ lgetL OS i ↔ x ∈ lgetL OS j := by
    intro x
    by_cases hx : x < n
    · exact hno ⟨x, hx⟩
    · have hxi : x ∉ lgetL OS i := fun h => hx (hbi x h)
      have hxj : x ∉ lgetL OS j := fun h => hx (hbj x h)
      simp [hxi, hxj]
  have hlen : (lgetL OS i).length = (lgetL OS j).length := by
    rw [← ksLY_lenN_eq, ← ksLY_lenN_eq, hleni, hlenj]
  have hlist := ksLY_eq_of_inc_mem hinci hincj hlen hmem
  have hkeyeq : keyN w (lgetL OS i) = keyN w (lgetL OS j) := congrArg (keyN w) hlist
  unfold distinctOK at hd
  have hi' := CFSG.KS.allN_spec hd i hiN
  have hj' := CFSG.KS.allN_spec hi' j hji
  rw [CFSG.KS.Raw.Orb.bIf_eq] at hj'
  have hbeq : Nat.beq (keyN w (lgetL OS i)) (keyN w (lgetL OS j)) = true := by
    rw [Nat.beq_eq]
    exact hkeyeq
  rw [if_pos hbeq] at hj'
  exact Bool.noConfusion hj'

private theorem ksLY_img_mem {n w A B N : Nat} {OP OG : List Nat}
    {OS : List (List Nat)} {α β : Equiv.Perm (Fin n)}
    (hA : Raw.Orb.PRep n w A α) (hB : Raw.Orb.PRep n w B β)
    (hfacts : ∀ i < N, lenN (lgetL OS i) = 12 ∧ incN (lgetL OS i) = true ∧
      (∀ p ∈ lgetL OS i, p < n) ∧
      (i ≠ 0 → lget OP i < i ∧ lget OG i < 2 ∧
        ∀ p ∈ lgetL OS (lget OP i),
          memN (pg w (mask w) (Bool.rec (motive := fun _ => Nat) B A (Nat.beq (lget OG i) 0)) p)
            (lgetL OS i) = true)) :
    ∀ i < N, ∃ g ∈ Subgroup.closure ({α, β} : Set (Equiv.Perm (Fin n))),
      ∀ p : Fin n, (p : Nat) ∈ lgetL OS i ↔
        ((g⁻¹ p : Fin n) : Nat) ∈ lgetL OS 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hiN
    by_cases hi0 : i = 0
    · subst i
      refine ⟨1, one_mem _, fun p => ?_⟩
      simp
    · obtain ⟨hleni, hinci, hbi, hmore⟩ := hfacts i hiN
      obtain ⟨hOP, hOG, himg⟩ := hmore hi0
      have hpiN : lget OP i < N := lt_trans hOP hiN
      obtain ⟨g, hgmem, hgi⟩ := ih (lget OP i) hOP hpiN
      obtain ⟨γ, hγmem, hγrep⟩ := ksLY_img_rep hA hB
      obtain ⟨hlen0, hinc0, hb0, _⟩ := hfacts 0 (lt_of_le_of_lt (Nat.zero_le i) hiN)
      obtain ⟨_, _, hbP, _⟩ := hfacts (lget OP i) hpiN
      have hlen0' : (lgetL OS 0).length = 12 := by
        rw [← ksLY_lenN_eq]
        exact hlen0
      have hn : 0 < n := by
        have hne : lgetL OS 0 ≠ [] := by
          intro e
          rw [e] at hlen0'
          simp at hlen0'
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
        exact Nat.pos_of_ne_zero (fun hn0 => by
          have := hb0 x hx
          omega)
      have hcard0 : (lgetL OS 0).toFinset.card = 12 := by
        rw [List.toFinset_card_of_nodup (ksLY_incN_nodup hinc0), ← ksLY_lenN_eq, hlen0]
      have hcardi : (lgetL OS i).toFinset.card = 12 := by
        rw [List.toFinset_card_of_nodup (ksLY_incN_nodup hinci), ← ksLY_lenN_eq, hleni]
      have hset := ksLY_img_set_eq hn hb0 hbP hgi
      have hnext := ksLY_img_next hn hset himg hγrep hcard0 hcardi hb0
      exact ⟨γ * g, mul_mem hγmem hgmem, hnext⟩

private theorem ksLY_shl_shl (c w : Nat) :
    Nat.shiftLeft (Nat.shiftLeft c w) w = Nat.shiftLeft c (Nat.mul 2 w) := by
  rw [show Nat.shiftLeft (Nat.shiftLeft c w) w = (Nat.shiftLeft c w) * 2 ^ w from
      Nat.shiftLeft_eq _ _,
    show Nat.shiftLeft c w = c * 2 ^ w from Nat.shiftLeft_eq _ _,
    show Nat.shiftLeft c (Nat.mul 2 w) = c * 2 ^ (Nat.mul 2 w) from
      Nat.shiftLeft_eq _ _,
    show Nat.mul 2 w = w + w by change 2 * w = w + w; ring, Nat.pow_add]
  ring

private theorem ksLY_keyN_three (w a b c : Nat) :
    keyN w [a, b, c] =
      Nat.lor a (Nat.lor (Nat.shiftLeft b w) (Nat.shiftLeft c (Nat.mul 2 w))) := by
  change Nat.lor a (Nat.shiftLeft (Nat.lor b (Nat.shiftLeft
      (Nat.lor c (Nat.shiftLeft 0 w)) w)) w) =
    Nat.lor a (Nat.lor (Nat.shiftLeft b w) (Nat.shiftLeft c (Nat.mul 2 w)))
  rw [show Nat.shiftLeft 0 w = 0 from Nat.zero_shiftLeft w]
  simp only [Nat.lor_eq, Nat.or_zero]
  rw [show Nat.shiftLeft (b ||| Nat.shiftLeft c w) w =
      Nat.shiftLeft b w ||| Nat.shiftLeft (Nat.shiftLeft c w) w from
      Nat.shiftLeft_or_distrib,
    ksLY_shl_shl]

private theorem ksLY_tr_tri_rep {n w kS kO BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    {i k : Nat} (hi : i < 3) (hk : k < rcnt (LR i)) :
    ∃ τ ∈ Raw.Orb.Gen n S kO,
      Raw.Orb.PRep n w (TR (roff n (n * w) (LR i) + k)) τ ∧
      Raw.Orb.PRep n w (TRI (roff n (n * w) (LR i) + k)) τ⁻¹ := by
  have C := CntPf.ch_of hb hh hl hNS hs
  obtain ⟨τ, hτmem, hτ⟩ := C.tr i hi k hk
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hspec := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  have hτ' : Raw.Orb.PRep n w (TR (roff n (n * w) (LR i) + k))
      (CFSG.Monster.B.Co2.permOfArr n
        (unpack n w (TR (roff n (n * w) (LR i) + k)))) := (hspec.2 k hk).1
  have hτi := (hspec.2 k hk).2
  have e : τ = CFSG.Monster.B.Co2.permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k))) :=
    CntPf.prep_unique hτ hτ'
  refine ⟨τ, hτmem, hτ, ?_⟩
  rwa [← e] at hτi

private theorem ksLY_codeProd_rep {n w : Nat} (hn : n < 2 ^ 32) {LR TR : Nat → Nat} (c : Nat)
    {τ0 τ1 τ2 : Equiv.Perm (Fin n)}
    (h0 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 0) + Nat.mod c (rcnt (LR 0)))) τ0)
    (h1 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 1) +
      Nat.mod (Nat.div c (rcnt (LR 0))) (rcnt (LR 1)))) τ1)
    (h2 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 2) +
      Nat.div (Nat.div c (rcnt (LR 0))) (rcnt (LR 1)))) τ2) :
    Raw.Orb.PRep n w (codeProd n w LR TR c) (τ0 * (τ1 * τ2)) := by
  simpa [codeProd, PF.strictN_eqP] using
    Raw.Orb.prep_pcomp hn h0 (Raw.Orb.prep_pcomp hn h1 h2)

private theorem ksLY_conjKey_eq_keyN (w BP X t0 t1 t2 t0i t1i t2i : Nat) :
    conjKey w BP X t0 t1 t2 t0i t1i t2i =
      keyN w [
        pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 (pg w (mask w) X
          (pg w (mask w) t2i (pg w (mask w) t1i (pg w (mask w) t0i
            (pg w (mask w) BP 2))))))),
        pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 (pg w (mask w) X
          (pg w (mask w) t2i (pg w (mask w) t1i (pg w (mask w) t0i
            (pg w (mask w) BP 1))))))),
        pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2 (pg w (mask w) X
          (pg w (mask w) t2i (pg w (mask w) t1i (pg w (mask w) t0i
            (pg w (mask w) BP 0)))))))] := by
  rw [ksLY_keyN_three]
  rfl

private theorem ksLY_conj_acts {n w : Nat} {X t0 t1 t2 t0i t1i t2i : Nat}
    {ξ τ0 τ1 τ2 : Equiv.Perm (Fin n)}
    (hX : Raw.Orb.PRep n w X ξ) (h0 : Raw.Orb.PRep n w t0 τ0)
    (h1 : Raw.Orb.PRep n w t1 τ1) (h2 : Raw.Orb.PRep n w t2 τ2)
    (h0i : Raw.Orb.PRep n w t0i τ0⁻¹) (h1i : Raw.Orb.PRep n w t1i τ1⁻¹)
    (h2i : Raw.Orb.PRep n w t2i τ2⁻¹) :
    CntPf.Acts n (fun p => pg w (mask w) t0 (pg w (mask w) t1 (pg w (mask w) t2
      (pg w (mask w) X (pg w (mask w) t2i (pg w (mask w) t1i (pg w (mask w) t0i p)))))))
      ((τ0 * τ1 * τ2) * ξ * (τ0 * τ1 * τ2)⁻¹) := by
  have hacts := CntPf.acts_comp (CntPf.acts_pg h0)
    (CntPf.acts_comp (CntPf.acts_pg h1)
      (CntPf.acts_comp (CntPf.acts_pg h2)
        (CntPf.acts_comp (CntPf.acts_pg hX)
          (CntPf.acts_comp (CntPf.acts_pg h2i)
            (CntPf.acts_comp (CntPf.acts_pg h1i) (CntPf.acts_pg h0i))))))
  have e : τ0 * (τ1 * (τ2 * (ξ * (τ2⁻¹ * (τ1⁻¹ * τ0⁻¹))))) =
      (τ0 * τ1 * τ2) * ξ * (τ0 * τ1 * τ2)⁻¹ := by group
  simpa [e] using hacts

private theorem ksLY_clsKey_key {n w : Nat} {LR TR TRI : Nat → Nat} {BP X c : Nat}
    {ξ τ0 τ1 τ2 : Equiv.Perm (Fin n)}
    (hbp : ∀ t < 3, pg w (mask w) BP t < n)
    (hX : Raw.Orb.PRep n w X ξ)
    (h0 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 0) + Nat.mod c (rcnt (LR 0)))) τ0)
    (h1 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 1) +
      Nat.mod (Nat.div c (rcnt (LR 0))) (rcnt (LR 1)))) τ1)
    (h2 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 2) +
      Nat.div (Nat.div c (rcnt (LR 0))) (rcnt (LR 1)))) τ2)
    (h0i : Raw.Orb.PRep n w (TRI (roff n (n * w) (LR 0) +
      Nat.mod c (rcnt (LR 0)))) τ0⁻¹)
    (h1i : Raw.Orb.PRep n w (TRI (roff n (n * w) (LR 1) +
      Nat.mod (Nat.div c (rcnt (LR 0))) (rcnt (LR 1)))) τ1⁻¹)
    (h2i : Raw.Orb.PRep n w (TRI (roff n (n * w) (LR 2) +
      Nat.div (Nat.div c (rcnt (LR 0))) (rcnt (LR 1)))) τ2⁻¹) :
    clsKey n w LR TR TRI BP X c =
      keyN w [
        (((τ0 * τ1 * τ2) * ξ * (τ0 * τ1 * τ2)⁻¹) ⟨pg w (mask w) BP 2, hbp 2 (by norm_num)⟩ : Nat),
        (((τ0 * τ1 * τ2) * ξ * (τ0 * τ1 * τ2)⁻¹) ⟨pg w (mask w) BP 1, hbp 1 (by norm_num)⟩ : Nat),
        (((τ0 * τ1 * τ2) * ξ * (τ0 * τ1 * τ2)⁻¹)
          ⟨pg w (mask w) BP 0, hbp 0 (by norm_num)⟩ : Nat)] := by
  have hacts := ksLY_conj_acts hX h0 h1 h2 h0i h1i h2i
  have hkey := ksLY_conjKey_eq_keyN (w := w) (BP := BP) (X := X)
    (t0 := TR (roff n (n * w) (LR 0) + Nat.mod c (rcnt (LR 0))))
    (t1 := TR (roff n (n * w) (LR 1) +
      Nat.mod (Nat.div c (rcnt (LR 0))) (rcnt (LR 1))))
    (t2 := TR (roff n (n * w) (LR 2) +
      Nat.div (Nat.div c (rcnt (LR 0))) (rcnt (LR 1))))
    (t0i := TRI (roff n (n * w) (LR 0) + Nat.mod c (rcnt (LR 0))))
    (t1i := TRI (roff n (n * w) (LR 1) +
      Nat.mod (Nat.div c (rcnt (LR 0))) (rcnt (LR 1))))
    (t2i := TRI (roff n (n * w) (LR 2) +
      Nat.div (Nat.div c (rcnt (LR 0))) (rcnt (LR 1))))
  have e2 := hacts (pg w (mask w) BP 2) (hbp 2 (by norm_num))
  have e1 := hacts (pg w (mask w) BP 1) (hbp 1 (by norm_num))
  have e0 := hacts (pg w (mask w) BP 0) (hbp 0 (by norm_num))
  unfold clsKey
  simp only [PF.strictN_eqP]
  refine hkey.trans ?_
  simp only [e2, e1, e0]

private noncomputable def ksLY_codePerm {n : Nat} (w : Nat) (LR TR : Nat → Nat)
    (S : Array (Array Nat)) (kO : Nat) (C : List Nat) (i : Nat) : Equiv.Perm (Fin n) := by
  classical
  exact if h : ∃ γ : Equiv.Perm (Fin n), γ ∈ Raw.Orb.Gen n S kO ∧
      Raw.Orb.PRep n w (codeProd n w LR TR (lget C i)) γ
    then Classical.choose h else 1

private theorem ksLY_codePerm_spec {n w kO : Nat} {LR TR : Nat → Nat}
    {S : Array (Array Nat)} {C : List Nat} {i : Nat}
    (h : ∃ γ : Equiv.Perm (Fin n), γ ∈ Raw.Orb.Gen n S kO ∧
      Raw.Orb.PRep n w (codeProd n w LR TR (lget C i)) γ) :
    ksLY_codePerm w LR TR S kO C i ∈ Raw.Orb.Gen n S kO ∧
      Raw.Orb.PRep n w (codeProd n w LR TR (lget C i))
        (ksLY_codePerm w LR TR S kO C i) := by
  classical
  unfold ksLY_codePerm
  rw [dif_pos h]
  exact Classical.choose_spec h

private theorem ksLY_code_rep {n w kS kO BP NS CH N : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {C : List Nat}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hcode : ∀ c ∈ C, codeOK LR c = true) (hlen : C.length = N) {i : Nat} (hi : i < N) :
    ∃ γ ∈ Raw.Orb.Gen n S kO,
      Raw.Orb.PRep n w (codeProd n w LR TR (lget C i)) γ := by
  have hltC : i < C.length := by rw [hlen]; exact hi
  have hget : lget C i = C[i] := by
    rw [CFSG.KC.Child3.lget_eq]
    exact (List.getElem_eq_getD (l := C) (i := i) (h := hltC) 0).symm
  have hcodei := hcode (lget C i) (by rw [hget]; exact List.getElem_mem hltC)
  have hbound : lget C i < rcnt (LR 0) * (rcnt (LR 1) * rcnt (LR 2)) := by
    simpa [codeOK] using hcodei
  have hpos : 0 < rcnt (LR 0) * (rcnt (LR 1) * rcnt (LR 2)) :=
    lt_of_le_of_lt (Nat.zero_le _) hbound
  have hr0 : 0 < rcnt (LR 0) := Nat.pos_of_mul_pos_right hpos
  have h12 : 0 < rcnt (LR 1) * rcnt (LR 2) := Nat.pos_of_mul_pos_left hpos
  have hr1 : 0 < rcnt (LR 1) := Nat.pos_of_mul_pos_right h12
  have hr2 : 0 < rcnt (LR 2) := Nat.pos_of_mul_pos_left h12
  have ha : Nat.mod (lget C i) (rcnt (LR 0)) < rcnt (LR 0) := Nat.mod_lt _ hr0
  have hb1 : Nat.mod (Nat.div (lget C i) (rcnt (LR 0))) (rcnt (LR 1)) < rcnt (LR 1) :=
    Nat.mod_lt _ hr1
  have hdiv1 : Nat.div (lget C i) (rcnt (LR 0)) < rcnt (LR 1) * rcnt (LR 2) := by
    refine (Nat.div_lt_iff_lt_mul (x := lget C i) (y := rcnt (LR 1) * rcnt (LR 2))
      (k := rcnt (LR 0)) hr0).2 ?_
    rwa [Nat.mul_comm (rcnt (LR 1) * rcnt (LR 2)) (rcnt (LR 0))]
  have hb2 : Nat.div (Nat.div (lget C i) (rcnt (LR 0))) (rcnt (LR 1)) < rcnt (LR 2) := by
    refine (Nat.div_lt_iff_lt_mul (x := Nat.div (lget C i) (rcnt (LR 0)))
      (y := rcnt (LR 2)) (k := rcnt (LR 1)) hr1).2 ?_
    rwa [Nat.mul_comm (rcnt (LR 2)) (rcnt (LR 1))]
  obtain ⟨τ0, hτ0mem, hτ0, hτ0i⟩ :=
    ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) ha
  obtain ⟨τ1, hτ1mem, hτ1, hτ1i⟩ :=
    ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) hb1
  obtain ⟨τ2, hτ2mem, hτ2, hτ2i⟩ :=
    ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) hb2
  have hn32 : n < 2 ^ 32 := by have := hb.2.2.1; omega
  refine ⟨τ0 * τ1 * τ2, by simpa [mul_assoc] using mul_mem hτ0mem (mul_mem hτ1mem hτ2mem), ?_⟩
  simpa [mul_assoc] using ksLY_codeProd_rep hn32 (lget C i) hτ0 hτ1 hτ2

private theorem ksLY_code_bounds {LR : Nat → Nat} {c : Nat}
    (hbound : c < rcnt (LR 0) * (rcnt (LR 1) * rcnt (LR 2))) :
    c % rcnt (LR 0) < rcnt (LR 0) ∧
    (c / rcnt (LR 0)) % rcnt (LR 1) < rcnt (LR 1) ∧
    c / rcnt (LR 0) < rcnt (LR 1) * rcnt (LR 2) ∧
    (c / rcnt (LR 0)) / rcnt (LR 1) < rcnt (LR 2) := by
  have hpos : 0 < rcnt (LR 0) * (rcnt (LR 1) * rcnt (LR 2)) :=
    lt_of_le_of_lt (Nat.zero_le _) hbound
  have hr0 : 0 < rcnt (LR 0) := Nat.pos_of_mul_pos_right hpos
  have h12 : 0 < rcnt (LR 1) * rcnt (LR 2) := Nat.pos_of_mul_pos_left hpos
  have hr1 : 0 < rcnt (LR 1) := Nat.pos_of_mul_pos_right h12
  have ha : c % rcnt (LR 0) < rcnt (LR 0) := Nat.mod_lt _ hr0
  have hb1 : (c / rcnt (LR 0)) % rcnt (LR 1) < rcnt (LR 1) :=
    Nat.mod_lt _ hr1
  have hdiv1 : c / rcnt (LR 0) < rcnt (LR 1) * rcnt (LR 2) := by
    refine (Nat.div_lt_iff_lt_mul (x := c) (y := rcnt (LR 1) * rcnt (LR 2))
      (k := rcnt (LR 0)) hr0).2 ?_
    rwa [Nat.mul_comm (rcnt (LR 1) * rcnt (LR 2)) (rcnt (LR 0))]
  have hb2 : (c / rcnt (LR 0)) / rcnt (LR 1) < rcnt (LR 2) := by
    refine (Nat.div_lt_iff_lt_mul (x := c / rcnt (LR 0))
      (y := rcnt (LR 2)) (k := rcnt (LR 1)) hr1).2 ?_
    rwa [Nat.mul_comm (rcnt (LR 2)) (rcnt (LR 1))]
  exact ⟨ha, hb1, hdiv1, hb2⟩

private theorem ksLY_code_data {n w kS kO BP NS CH N : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {C : List Nat}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hcode : ∀ c ∈ C, codeOK LR c = true) (hlen : C.length = N) {i : Nat} (hi : i < N) :
    ∃ τ0 τ1 τ2 : Equiv.Perm (Fin n),
      τ0 ∈ Raw.Orb.Gen n S kO ∧ τ1 ∈ Raw.Orb.Gen n S kO ∧ τ2 ∈ Raw.Orb.Gen n S kO ∧
      Raw.Orb.PRep n w (TR (roff n (n * w) (LR 0) +
        Nat.mod (lget C i) (rcnt (LR 0)))) τ0 ∧
      Raw.Orb.PRep n w (TRI (roff n (n * w) (LR 0) +
        Nat.mod (lget C i) (rcnt (LR 0)))) τ0⁻¹ ∧
      Raw.Orb.PRep n w (TR (roff n (n * w) (LR 1) +
        Nat.mod (Nat.div (lget C i) (rcnt (LR 0))) (rcnt (LR 1)))) τ1 ∧
      Raw.Orb.PRep n w (TRI (roff n (n * w) (LR 1) +
        Nat.mod (Nat.div (lget C i) (rcnt (LR 0))) (rcnt (LR 1)))) τ1⁻¹ ∧
      Raw.Orb.PRep n w (TR (roff n (n * w) (LR 2) +
        Nat.div (Nat.div (lget C i) (rcnt (LR 0))) (rcnt (LR 1)))) τ2 ∧
      Raw.Orb.PRep n w (TRI (roff n (n * w) (LR 2) +
        Nat.div (Nat.div (lget C i) (rcnt (LR 0))) (rcnt (LR 1)))) τ2⁻¹ := by
  have hltC : i < C.length := by rw [hlen]; exact hi
  have hget : lget C i = C[i] := by
    rw [CFSG.KC.Child3.lget_eq]
    exact (List.getElem_eq_getD (l := C) (i := i) (h := hltC) 0).symm
  have hcodei := hcode (lget C i) (by rw [hget]; exact List.getElem_mem hltC)
  have hbound : lget C i < rcnt (LR 0) * (rcnt (LR 1) * rcnt (LR 2)) := by
    simpa [codeOK] using hcodei
  obtain ⟨ha, hb1, hdiv1, hb2⟩ := ksLY_code_bounds hbound
  obtain ⟨τ0, hτ0mem, hτ0, hτ0i⟩ :=
    ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) ha
  obtain ⟨τ1, hτ1mem, hτ1, hτ1i⟩ :=
    ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) hb1
  obtain ⟨τ2, hτ2mem, hτ2, hτ2i⟩ :=
    ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) hb2
  exact ⟨τ0, τ1, τ2, hτ0mem, hτ1mem, hτ2mem, hτ0, hτ0i, hτ1, hτ1i, hτ2, hτ2i⟩

private theorem ksLY_clsKey_codePerm {n w kS kO BP NS CH N : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {C : List Nat}
    {X : Nat} {ξ : Equiv.Perm (Fin n)}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (hX : Raw.Orb.PRep n w X ξ) (hcode : ∀ c ∈ C, codeOK LR c = true)
    (hlen : C.length = N) {i : Nat} (hi : i < N) :
    clsKey n w LR TR TRI BP X (lget C i) =
      keyN w (let γ : Equiv.Perm (Fin n) := ksLY_codePerm w LR TR S kO C i;
        [ ((γ * ξ * γ⁻¹) ⟨pg w (mask w) BP 2, by
            obtain ⟨hb, hh, hl, hNS, hs, _⟩ := hc
            exact (CntPf.ch_of hb hh hl hNS hs).bp_lt 2 (by norm_num)⟩ : Nat),
          ((γ * ξ * γ⁻¹) ⟨pg w (mask w) BP 1, by
            obtain ⟨hb, hh, hl, hNS, hs, _⟩ := hc
            exact (CntPf.ch_of hb hh hl hNS hs).bp_lt 1 (by norm_num)⟩ : Nat),
          ((γ * ξ * γ⁻¹) ⟨pg w (mask w) BP 0, by
            obtain ⟨hb, hh, hl, hNS, hs, _⟩ := hc
            exact (CntPf.ch_of hb hh hl hNS hs).bp_lt 0 (by norm_num)⟩ : Nat)]) := by
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  obtain ⟨τ0, τ1, τ2, hτ0mem, hτ1mem, hτ2mem,
    hτ0, hτ0i, hτ1, hτ1i, hτ2, hτ2i⟩ :=
    ksLY_code_data hb hh hl hNS hs hp hcode hlen hi
  have Cch := CntPf.ch_of hb hh hl hNS hs
  have hkey := ksLY_clsKey_key Cch.bp_lt hX hτ0 hτ1 hτ2 hτ0i hτ1i hτ2i
  have hn32 : n < 2 ^ 32 := by have := hb.2.2.1; omega
  have hrepτ : Raw.Orb.PRep n w (codeProd n w LR TR (lget C i)) (τ0 * τ1 * τ2) := by
    simpa [mul_assoc] using ksLY_codeProd_rep hn32 (lget C i) hτ0 hτ1 hτ2
  have hex := ksLY_code_rep hb hh hl hNS hs hp hcode hlen hi
  have hspec := ksLY_codePerm_spec (w := w) hex
  have e : ksLY_codePerm w LR TR S kO C i = τ0 * τ1 * τ2 :=
    CntPf.prep_unique hspec.2 hrepτ
  rw [e]
  simpa using hkey

private theorem ksLY_lt_of_steps {f : Nat → Nat} {N : Nat}
    (h : ∀ i < Nat.pred N, f i < f (i + 1)) :
    ∀ i j, i < j → j < N → f i < f j := by
  intro i j hij hjN
  have hpred : Nat.pred N = N - 1 := by cases N <;> rfl
  have aux : ∀ d, i + (d + 1) < N → f i < f (i + (d + 1)) := by
    intro d
    induction d with
    | zero => intro hd; simpa using h i (by rw [hpred]; omega)
    | succ d ih =>
      intro hd
      have hprev : i + (d + 1) < N := by omega
      have hlt1 := ih hprev
      have hstep : f (i + (d + 1)) < f (i + (d + 1) + 1) :=
        h (i + (d + 1)) (by rw [hpred]; omega)
      have he : i + ((d + 1) + 1) = i + (d + 1) + 1 := by omega
      rw [he]
      exact lt_trans hlt1 hstep
  have hji : j = i + ((j - i - 1) + 1) := by omega
  rw [hji]
  exact aux (j - i - 1) (by omega)

private theorem ksLY_permOK_rep_inv {n w X XI : Nat} {ξ : Equiv.Perm (Fin n)}
    (hX : Raw.Orb.PRep n w X ξ)
    (hXI : permOK n w (mask w) (n * w) X XI = true) : Raw.Orb.PRep n w XI ξ⁻¹ := by
  obtain ⟨-, -, hinv⟩ := Raw.Orb.permOK_facts hXI
  intro x
  have hz : pg w (mask w) X (ξ⁻¹ x).val = x := by
    rw [hX (ξ⁻¹ x)]
    simp
  calc pg w (mask w) XI x = pg w (mask w) XI (pg w (mask w) X (ξ⁻¹ x)) := by rw [hz]
    _ = (ξ⁻¹ x).val := (hinv _ (ξ⁻¹ x).2).2

private theorem ksLY_XI_lt_ap {n w X XI : Nat} {ξ : Equiv.Perm (Fin n)}
    (hX : Raw.Orb.PRep n w X ξ) (hXI : Raw.Orb.PRep n w XI ξ⁻¹) :
    (∀ p < n, pg w (mask w) X p < n) ∧
    (∀ p < n, pg w (mask w) XI (pg w (mask w) X p) = p) := by
  have hXlt : ∀ p < n, pg w (mask w) X p < n := by
    intro p hp
    rw [hX ⟨p, hp⟩]
    exact (ξ ⟨p, hp⟩).2
  have hXIap : ∀ p < n, pg w (mask w) XI (pg w (mask w) X p) = p := by
    intro p hp
    have h1 : (⟨pg w (mask w) X p, hXlt p hp⟩ : Fin n) = ξ ⟨p, hp⟩ := Fin.ext (hX ⟨p, hp⟩)
    rw [hXI ⟨pg w (mask w) X p, hXlt p hp⟩, h1]
    simp
  exact ⟨hXlt, hXIap⟩

private theorem ksLY_contribY_eq {n w BP : Nat} {Γ : Subgroup (Equiv.Perm (Fin n))}
    {X XI Y : Nat} {ξ η : Equiv.Perm (Fin n)} {f g : Nat → Nat}
    (hbp : ∀ t < 3, pg w (mask w) BP t < n)
    (hsep : ∀ γ : Equiv.Perm (Fin n), γ ∈ Γ →
      (∀ t < 3, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
    (hX : Raw.Orb.PRep n w X ξ) (hXI : Raw.Orb.PRep n w XI ξ⁻¹)
    (hY : Raw.Orb.PRep n w Y η) (hy : CntPf.Acts n f η) (hyi : CntPf.Acts n g η⁻¹)
    (hξ : ξ ∈ Γ) (hη : η ∈ Γ) (hn : n < 2 ^ 32) {R W : List (List Int)}
    (hR : lettersTwo R) (hW : lettersTwo W) :
    contribY w (mask w) BP (pg w (mask w) X) (pg w (mask w) XI) f g R W =
      (if (ordTest n 12 (tabP n w Y) && relTestW n R W (tabP n w X) (tabP n w Y))
          then 1 else 0) +
        2 ^ 20 * (if ordTest n 2 (tabP n w Y) then 1 else 0) := by
  obtain ⟨hXlt, hXIap⟩ := ksLY_XI_lt_ap hX hXI
  have hIX := CFSG.KS.VO.invT_get hn (f := fun p => pg w (mask w) X p)
    (g := fun p => pg w (mask w) XI p)
    (fun x hx => ⟨by
        rw [ap_tabP (n := n) (w := w) (X := X) hx (lt_trans (hXlt x hx) hn)], hXlt x hx,
      hXIap x hx⟩)
  have hYtab : CntPf.Acts n (ap (tabP n w Y)) η := ksLY_acts_tabP hn hY
  have hYlt : ∀ p < n, pg w (mask w) Y p < n := by
    intro p hp
    rw [hY ⟨p, hp⟩]
    exact (η ⟨p, hp⟩).2
  have hYIinv : ∀ x < n, g (pg w (mask w) Y x) = x := by
    intro x hx
    have h1 : pg w (mask w) Y x = (η ⟨x, hx⟩ : Nat) := hY ⟨x, hx⟩
    rw [h1]
    simpa using hyi (η ⟨x, hx⟩).val (η ⟨x, hx⟩).2
  have hIY := CFSG.KS.VO.invT_get hn (f := fun p => pg w (mask w) Y p) (g := g)
    (fun x hx => ⟨by
        rw [ap_tabP (n := n) (w := w) (X := Y) hx (lt_trans (hYlt x hx) hn)], hYlt x hx,
      hYIinv x hx⟩)
  have hfix := CntPf.fix_eq hbp hsep hη hy (CntPf.acts_single hYtab)
  have h12 := CntPf.ord12B_eq hfix
  have h2 := CntPf.ordB_eq (k := 2) hfix (by decide)
  have hrel := ksLY_relB_eq hbp hsep hξ hη hX hXI hY hy hyi hn
    ⟨hIX.1, fun y hy => (hIX.2 y hy).trans (hXI ⟨y, hy⟩)⟩
    ⟨hIY.1, fun y hy => (hIY.2 y hy).trans (hyi y hy)⟩ hR hW
  unfold contribY
  rw [h12, h2, hrel]
  simp only [CFSG.KS.Raw.Orb.nIf_eq]
  unfold ordTest
  generalize ordW n [tabP n w Y] 12 = a
  generalize relTestW n R W (tabP n w X) (tabP n w Y) = b
  generalize ordW n [tabP n w Y] 2 = c
  cases a <;> cases b <;> cases c <;> norm_num

private theorem ksLY_blkY_eq (n w : Nat) (LR TR TRI : Nat → Nat) (BP X XI : Nat)
    (R W : List (List Int)) :
    sumF (rcnt (LR 0)) (blkY n w LR TR TRI BP X XI R W) =
      CntPf.tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
        contribY w (mask w) BP (fun p => pg w (mask w) X p) (fun p => pg w (mask w) XI p)
          (fun p => pg w (mask w) (TR (roff n (n * w) (LR 0) + a))
            (pg w (mask w) (TR (roff n (n * w) (LR 1) + b))
              (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p)))
          (fun p => pg w (mask w) (TRI (roff n (n * w) (LR 2) + c))
            (pg w (mask w) (TRI (roff n (n * w) (LR 1) + b))
              (pg w (mask w) (TRI (roff n (n * w) (LR 0) + a)) p))) R W := by
  rw [sumF_eq]
  unfold CntPf.tri
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [blkY, PF.strictN_eqP, sumF_eq]
  rfl

private theorem ksLY_prod3_rep {n w : Nat} {LR TR : Nat → Nat} {pidn : Nat → Nat → Nat}
    {a b c : Nat} {τ0 τ1 τ2 : Equiv.Perm (Fin n)}
    (hid : Raw.Orb.PRep n w (pidn n w) 1)
    (hτ0 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 0) + a)) τ0)
    (hτ1 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 1) + b)) τ1)
    (hτ2 : Raw.Orb.PRep n w (TR (roff n (n * w) (LR 2) + c)) τ2)
    (hn32 : n < 2 ^ 32) :
    Raw.Orb.PRep n w (CntPf.prod3 n w LR TR (pidn n w) a b c) (τ0 * τ1 * τ2) := by
  have h1 := Raw.Orb.prep_pcomp hn32 hid hτ0
  have h2 := Raw.Orb.prep_pcomp hn32 h1 hτ1
  have h3 := Raw.Orb.prep_pcomp hn32 h2 hτ2
  simpa [CntPf.prod3, mul_assoc] using h3

private theorem ksLY_contribY_at {n w kS kO BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {X XI : Nat}
    {ξ : Equiv.Perm (Fin n)} {R W : List (List Int)}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hX : Raw.Orb.PRep n w X ξ) (hXI : Raw.Orb.PRep n w XI ξ⁻¹)
    (hξ : ξ ∈ Raw.Orb.Gen n S kO) (hR : lettersTwo R) (hW : lettersTwo W)
    {a b c : Nat} (ha : a < rcnt (LR 0)) (hb1 : b < rcnt (LR 1))
    (hc : c < rcnt (LR 2)) :
    contribY w (mask w) BP (fun p => pg w (mask w) X p) (fun p => pg w (mask w) XI p)
      (fun p => pg w (mask w) (TR (roff n (n * w) (LR 0) + a))
        (pg w (mask w) (TR (roff n (n * w) (LR 1) + b))
          (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p)))
      (fun p => pg w (mask w) (TRI (roff n (n * w) (LR 2) + c))
        (pg w (mask w) (TRI (roff n (n * w) (LR 1) + b))
          (pg w (mask w) (TRI (roff n (n * w) (LR 0) + a)) p))) R W =
      (if (ordTest n 12 (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c)) &&
          relTestW n R W (tabP n w X)
            (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c))) then 1 else 0) +
        2 ^ 20 * (if ordTest n 2 (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c))
          then 1 else 0) := by
  obtain ⟨τ0, hτ0mem, hτ0, hτ0i⟩ := ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) ha
  obtain ⟨τ1, hτ1mem, hτ1, hτ1i⟩ := ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) hb1
  obtain ⟨τ2, hτ2mem, hτ2, hτ2i⟩ := ksLY_tr_tri_rep hb hh hl hNS hs hp (by norm_num) hc
  have C := CntPf.ch_of hb hh hl hNS hs
  have hn32 : n < 2 ^ 32 := by have := C.hn; omega
  have hid := Raw.Orb.prep_pidn (n := n) (w := w) C.hn C.hw
  let Y := CntPf.prod3 n w LR TR (pidn n w) a b c
  have hY : Raw.Orb.PRep n w Y (τ0 * τ1 * τ2) :=
    ksLY_prod3_rep hid hτ0 hτ1 hτ2 hn32
  have hy : CntPf.Acts n (fun p => pg w (mask w) (TR (roff n (n * w) (LR 0) + a))
        (pg w (mask w) (TR (roff n (n * w) (LR 1) + b))
          (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p))) (τ0 * τ1 * τ2) := by
    have h1 := CntPf.acts_comp (CntPf.acts_pg hτ0)
      (CntPf.acts_comp (CntPf.acts_pg hτ1) (CntPf.acts_pg hτ2))
    simpa [mul_assoc] using h1
  have hyi : CntPf.Acts n (fun p => pg w (mask w) (TRI (roff n (n * w) (LR 2) + c))
        (pg w (mask w) (TRI (roff n (n * w) (LR 1) + b))
          (pg w (mask w) (TRI (roff n (n * w) (LR 0) + a)) p))) (τ0 * τ1 * τ2)⁻¹ := by
    have h1 := CntPf.acts_comp (CntPf.acts_comp (CntPf.acts_pg hτ2i) (CntPf.acts_pg hτ1i))
      (CntPf.acts_pg hτ0i)
    have e : (τ2⁻¹ * τ1⁻¹) * τ0⁻¹ = (τ0 * τ1 * τ2)⁻¹ := by group
    simpa [e] using h1
  have hη : τ0 * τ1 * τ2 ∈ Raw.Orb.Gen n S kO :=
    mul_mem (mul_mem hτ0mem hτ1mem) hτ2mem
  exact ksLY_contribY_eq C.bp_lt C.sep hX hXI hY hy hyi hξ hη hn32 hR hW

private noncomputable def ksLY_clsZ {n : Nat} (w : Nat) (LR TR : Nat → Nat)
    (S : Array (Array Nat)) (kO : Nat) (C : List Nat) (ξ : Equiv.Perm (Fin n))
    (i : Nat) : Equiv.Perm (Fin n) :=
  let γ := ksLY_codePerm w LR TR S kO C i
  γ * ξ * γ⁻¹

private theorem ksLY_cls_nodup {n w kS kO BP NS CH N : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {C : List Nat}
    {X : Nat} {ξ : Equiv.Perm (Fin n)}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (hX : Raw.Orb.PRep n w X ξ) (hcode : ∀ c ∈ C, codeOK LR c = true)
    (hlen : C.length = N)
    (hinc : ∀ i < Nat.pred N, clsKey n w LR TR TRI BP X (lget C i) <
      clsKey n w LR TR TRI BP X (lget C (i + 1))) :
    ((List.range N).map (ksLY_clsZ w LR TR S kO C ξ)).Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i j hi hj hij
  have hiN : i < N := by simpa using hi
  have hjN : j < N := by simpa using hj
  by_contra hne
  have hz : ksLY_clsZ w LR TR S kO C ξ i = ksLY_clsZ w LR TR S kO C ξ j := by
    simpa [List.getElem_map] using hij
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hkeylt := ksLY_lt_of_steps hinc i j hlt hjN
    have hzi := ksLY_clsKey_codePerm hc hX hcode hlen hiN
    have hzj := ksLY_clsKey_codePerm hc hX hcode hlen hjN
    have hkeys : clsKey n w LR TR TRI BP X (lget C i) =
        clsKey n w LR TR TRI BP X (lget C j) := by
      rw [hzi, hzj]
      simp only [ksLY_clsZ] at hz ⊢
      rw [hz]
    exact (Nat.ne_of_lt hkeylt) hkeys
  · have hkeylt := ksLY_lt_of_steps hinc j i hgt hiN
    have hzi := ksLY_clsKey_codePerm hc hX hcode hlen hiN
    have hzj := ksLY_clsKey_codePerm hc hX hcode hlen hjN
    have hkeys : clsKey n w LR TR TRI BP X (lget C i) =
        clsKey n w LR TR TRI BP X (lget C j) := by
      rw [hzi, hzj]
      simp only [ksLY_clsZ] at hz ⊢
      rw [hz]
    exact (Nat.ne_of_lt hkeylt) hkeys.symm

private theorem ksLY_cls_mem {n w kS kO BP NS CH N : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {C : List Nat}
    {ξ : Equiv.Perm (Fin n)} {z : Equiv.Perm (Fin n)}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hcode : ∀ c ∈ C, codeOK LR c = true) (hlen : C.length = N)
    (hz : z ∈ (List.range N).map (ksLY_clsZ w LR TR S kO C ξ)) :
    ∃ γ ∈ Raw.Orb.Gen n S kO, z = γ * ξ * γ⁻¹ := by
  simp only [List.mem_map, List.mem_range] at hz
  obtain ⟨i, hiN, rfl⟩ := hz
  obtain ⟨γ, hγmem, hγrep⟩ := ksLY_code_rep hb hh hl hNS hs hp hcode hlen hiN
  have hspec := ksLY_codePerm_spec (w := w) ⟨γ, hγmem, hγrep⟩
  refine ⟨ksLY_codePerm w LR TR S kO C i, hspec.1, ?_⟩
  rfl

private theorem ksLY_orb_facts {n w k L : Nat} {G : Nat → Nat} {TL TP TG TD : List Nat}
    (h : orbOK n w G k L TL TP TG TD = true) {p : Nat} (hp : p < n) :
    lget TL p < L ∧
    (∀ j : Fin k, lget TL (pg w (mask w) (G j) p) = lget TL p) ∧
    (lget TP p = p → lget TD p = 0 ∧ ∀ r < p, lget TL r ≠ lget TL p) ∧
    (lget TP p ≠ p → lget TP p < n ∧ lget TG p < k ∧
      lget TD p = lget TD (lget TP p) + 1 ∧
      pg w (mask w) (G (lget TG p)) (lget TP p) = p) := by
  unfold orbOK at h
  have hp' := CFSG.KS.allN_spec h p hp
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.bAnd_iff] at hp'
  obtain ⟨hl, hp''⟩ := hp'
  rw [CFSG.KS.bAnd_iff] at hp''
  obtain ⟨hinv, hp3⟩ := hp''
  rw [CFSG.KS.Raw.Orb.strictB_eq] at hp3
  rw [CFSG.KS.Raw.Orb.bIf_eq] at hp3
  refine ⟨Nat.blt_eq.mp hl, fun j => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hinv j j.2), ?_, ?_⟩
  · intro hroot
    rw [if_pos (by rw [hroot, Nat.beq_refl])] at hp3
    rw [CFSG.KS.bAnd_iff] at hp3
    obtain ⟨hTD, hmin⟩ := hp3
    refine ⟨Nat.eq_of_beq_eq_true hTD, ?_⟩
    intro r hr hlab
    have hmin' := CFSG.KS.allN_spec hmin r hr
    rw [CFSG.KS.Raw.Orb.bIf_eq] at hmin'
    rw [if_pos (by rw [hlab, Nat.beq_refl])] at hmin'
    exact Bool.noConfusion hmin'
  · intro hroot
    have hbeq : Nat.beq (lget TP p) p = false := by
      cases h : Nat.beq (lget TP p) p with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true h) hroot
    rw [if_neg (by rw [hbeq]; exact Bool.false_ne_true)] at hp3
    rw [CFSG.KS.bAnd_iff] at hp3
    obtain ⟨hq, hp4⟩ := hp3
    rw [CFSG.KS.bAnd_iff] at hp4
    obtain ⟨hTG, hp5⟩ := hp4
    rw [CFSG.KS.bAnd_iff] at hp5
    obtain ⟨hTD, hstep⟩ := hp5
    exact ⟨Nat.blt_eq.mp hq, Nat.blt_eq.mp hTG, Nat.eq_of_beq_eq_true hTD,
      Nat.eq_of_beq_eq_true hstep⟩

private theorem ksLY_orb_inv {n w k L : Nat} {G : Nat → Nat} {TL TP TG TD : List Nat}
    (h : orbOK n w G k L TL TP TG TD = true) {γ : Fin k → Equiv.Perm (Fin n)}
    (hG : ∀ j : Fin k, Raw.Orb.PRep n w (G j) (γ j)) :
    ∀ t ∈ Subgroup.closure (Set.range γ), ∀ p : Fin n, lget TL (t p) = lget TL p := by
  intro t ht
  refine Subgroup.closure_induction (p := fun t _ => ∀ p : Fin n, lget TL (t p) = lget TL p)
    ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨j, rfl⟩ p
    have := (ksLY_orb_facts h p.2).2.1 j
    have hp : pg w (mask w) (G j) (p : Nat) = (γ j p : Nat) := hG j p
    rw [← hp]
    exact this
  · intro p; rfl
  · intro x y _ _ hx hy p
    rw [Equiv.Perm.mul_apply]
    exact (hx (y p)).trans (hy p)
  · intro x _ hx p
    have hq := hx ((x⁻¹) p)
    have hxinv : x (x⁻¹ p) = p := by simp
    rw [hxinv] at hq
    exact hq.symm

private theorem ksLY_orb_reach {n w k L : Nat} {G : Nat → Nat} {TL TP TG TD : List Nat}
    (h : orbOK n w G k L TL TP TG TD = true) {γ : Fin k → Equiv.Perm (Fin n)}
    (hG : ∀ j : Fin k, Raw.Orb.PRep n w (G j) (γ j)) :
    ∀ (d : Nat) (p : Fin n), lget TD p = d →
      ∃ t ∈ Subgroup.closure (Set.range γ), lget TP (t p) = t p ∧
        lget TL (t p) = lget TL p ∧
        ∀ u : Fin n, (u : Nat) < (t p : Nat) → lget TL u ≠ lget TL p := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hd
    have hpf := ksLY_orb_facts h p.2
    by_cases hroot : lget TP p = p
    · obtain ⟨hTD, hmin⟩ := hpf.2.2.1 hroot
      refine ⟨1, one_mem _, by simp [hroot], rfl, ?_⟩
      intro u hu
      exact hmin u (by simpa using hu)
    · obtain ⟨hqlt, hTG, hTD, hstep⟩ := hpf.2.2.2 hroot
      let q : Fin n := ⟨lget TP p, hqlt⟩
      have hdq : lget TD q = d - 1 := by
        have h := hTD
        change lget TD p = lget TD q + 1 at h
        omega
      have hdlt : lget TD q < d := by omega
      obtain ⟨t, ht, hrootr, hlabelr, hminr⟩ := ih (lget TD q) hdlt q rfl
      let j : Fin k := ⟨lget TG p, hTG⟩
      have hγj_nat : (γ j q : Nat) = p := by
        rw [← hG j q]
        exact hstep
      have hγj : γ j q = p := Fin.ext hγj_nat
      have hmemj : γ j ∈ Subgroup.closure (Set.range γ) :=
        Subgroup.subset_closure (Set.mem_range_self j)
      have hinv : (γ j)⁻¹ p = q := by
        rw [← hγj]
        simp
      have htq : (t * (γ j)⁻¹) p = t q := by
        rw [Equiv.Perm.mul_apply, hinv]
      have hlabelq : lget TL (q : Nat) = lget TL (p : Nat) := by
        have hq := (ksLY_orb_facts h q.2).2.1 j
        rw [hG j q, hγj_nat] at hq
        exact hq.symm
      refine ⟨t * (γ j)⁻¹, mul_mem ht (inv_mem hmemj), ?_, ?_, ?_⟩
      · simpa [htq] using hrootr
      · rw [htq]
        exact hlabelr.trans hlabelq
      · intro u hu
        have hmin := hminr u (by simpa [htq] using hu)
        rwa [hlabelq] at hmin

private theorem ksLY_ind (P : Prop) [Decidable P] : (if P then 1 else 0) ≤ 1 := by
  split <;> omega

theorem blkY_sound {n w kS kO BP NS CH X XI : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {R W : List (List Int)}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (h20 : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    (hX : canonK n w (mask w) (n * w) X = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 X = true)
    (hXI : permOK n w (mask w) (n * w) X XI = true) (hR : lettersTwo R) (hW : lettersTwo W) :
    (filterProducts n (ordTest n 12) (chainTables n S base) (idT n) []).countP
        (relTestW n R W (arrTable n (unpack n w X))) =
      fld20 (sumF (rcnt (LR 0)) (blkY n w LR TR TRI BP X XI R W)) 0 ∧
    (filterProducts n (ordTest n 2) (chainTables n S base) (idT n) []).length =
      fld20 (sumF (rcnt (LR 0)) (blkY n w LR TR TRI BP X XI R W)) 1 := by
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  have C := CntPf.ch_of hb hh hl hNS hs
  obtain ⟨-, -, hsift, -⟩ := GrpPf.group3 hb hh hl hNS hs
  have hn32 : n < 2 ^ 32 := by have := C.hn; omega
  obtain ⟨hct, hT⟩ := CFSG.KC.J2Cover.Snd.chainTables_eq_lvTab hb hp hl
  obtain ⟨ξ, hξG, hξP⟩ := (hsift X hX.1).1 hX.2
  have hXIP : Raw.Orb.PRep n w XI ξ⁻¹ := ksLY_permOK_rep_inv hξP hXI
  have hsum := ksLY_blkY_eq n w LR TR TRI BP X XI R W
  rw [CntPf.tri_congr (ψ := fun a b c =>
      (if (ordTest n 12 (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c)) &&
          relTestW n R W (tabP n w X)
            (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c))) then 1 else 0) +
        2 ^ 20 * (if ordTest n 2 (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c))
          then 1 else 0)) (fun a ha b hb1 c hc =>
        ksLY_contribY_at hb hh hl hNS hs hp hξP hXIP hξG hR hW ha hb1 hc)] at hsum
  simp only [CntPf.tri_add, CntPf.tri_mul] at hsum
  have ind : ∀ (P : Prop) [Decidable P], (if P then 1 else 0) ≤ 1 := fun P _ => ksLY_ind P
  have hcnt : ∀ (f p : Table → Bool),
      (filterProducts n f (chainTables n S base) (idT n) []).countP p =
        CntPf.tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
          if (f (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c)) &&
            p (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c))) then 1 else 0 := by
    intro f p
    rw [CntPf.countP_filterProducts, hct, CntPf.idT_eq_tabP' C.hn C.hw,
      CntPf.countProducts3 hn32 hT, List.countP_nil, Nat.zero_add]
  have hcnt12 := hcnt (ordTest n 12) (relTestW n R W (tabP n w X))
  have hlen : (filterProducts n (ordTest n 2) (chainTables n S base) (idT n) []).length =
        CntPf.tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
          if ordTest n 2 (tabP n w (CntPf.prod3 n w LR TR (pidn n w) a b c)) then 1 else 0 := by
    rw [← List.countP_true, hcnt (ordTest n 2) (fun _ => true)]
    simp only [Bool.and_true]
  have hbd : ∀ φ : Nat → Nat → Nat → Nat, (∀ a b c, φ a b c ≤ 1) →
      CntPf.tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) φ < 2 ^ 20 := fun φ h =>
    lt_of_le_of_lt (CntPf.tri_le _ _ _ φ h) h20
  rw [hsum]
  refine ⟨hcnt12.trans (CntPf.fld20_pack2 ?_ ?_).1.symm,
    (hlen).trans (CntPf.fld20_pack2 ?_ ?_).2.symm⟩
  all_goals exact hbd _ fun _ _ _ => ind _

theorem clsOK_sound {n w kS kO BP NS CH X N : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat} {C : List Nat}
    {ξ : Equiv.Perm (Fin n)}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (hX : Raw.Orb.PRep n w X ξ)
    (h : clsOK n w LR TR TRI BP X C N = true) :
    ∃ L : List (Equiv.Perm (Fin n)), L.Nodup ∧ L.length = N ∧
      ∀ z ∈ L, ∃ γ ∈ Raw.Orb.Gen n S kO, z = γ * ξ * γ⁻¹ := by
  have hcKeep := hc
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  unfold clsOK at h
  rw [CFSG.KS.bAnd_iff] at h
  obtain ⟨hlenN, h⟩ := h
  rw [CFSG.KS.bAnd_iff] at h
  obtain ⟨hcodeAll, hincAll⟩ := h
  have hlenN' : lenN C = N := Nat.eq_of_beq_eq_true hlenN
  have hlen : C.length = N := by rw [← ksLY_lenN_eq]; exact hlenN'
  rw [ksLY_allL_iff] at hcodeAll
  have hinc : ∀ i < Nat.pred N, clsKey n w LR TR TRI BP X (lget C i) <
      clsKey n w LR TR TRI BP X (lget C (i + 1)) :=
    fun i hi => Nat.blt_eq.mp (CFSG.KS.allN_spec hincAll i hi)
  refine ⟨(List.range N).map (ksLY_clsZ w LR TR S kO C ξ), ?_, ?_, ?_⟩
  · exact ksLY_cls_nodup hcKeep hX hcodeAll hlen hinc
  · simp
  · intro z hz
    exact ksLY_cls_mem hb hh hl hNS hs hp hcodeAll hlen hz

theorem orbOK_sound {n w k L : Nat} {G : Nat → Nat} {TL TP TG TD : List Nat}
    {γ : Fin k → Equiv.Perm (Fin n)} (hG : ∀ j : Fin k, Raw.Orb.PRep n w (G j) (γ j))
    (h : orbOK n w G k L TL TP TG TD = true) (p q : Fin n) :
    (∃ t ∈ Subgroup.closure (Set.range γ), t p = q) ↔ lget TL p = lget TL q := by
  constructor
  · rintro ⟨t, ht, htp⟩
    have hlab := ksLY_orb_inv h hG t ht p
    rw [htp] at hlab
    exact hlab.symm
  · intro hpq
    obtain ⟨tp, htp, hrootp, hlabelp, hminp⟩ :=
      ksLY_orb_reach h hG (lget TD p) p rfl
    obtain ⟨tq, htq, hrootq, hlabelq, hminq⟩ :=
      ksLY_orb_reach h hG (lget TD q) q rfl
    have hlabel : lget TL (tp p) = lget TL (tq q) :=
      hlabelp.trans (hpq.trans hlabelq.symm)
    have hroots : tp p = tq q := by
      by_cases hlt : (tp p : Nat) < (tq q : Nat)
      · exact False.elim ((hminq (tp p) hlt) (hlabel.trans hlabelq))
      · have hle : (tq q : Nat) ≤ (tp p : Nat) := Nat.le_of_not_lt hlt
        by_cases hgt : (tq q : Nat) < (tp p : Nat)
        · exact False.elim ((hminp (tq q) hgt) (hlabel.symm.trans hlabelp))
        · exact Fin.ext (Nat.le_antisymm (Nat.le_of_not_lt hgt) hle)
    refine ⟨tq⁻¹ * tp, mul_mem (inv_mem htq) htp, ?_⟩
    rw [Equiv.Perm.mul_apply, hroots]
    simp

theorem imgOK_sound {n w A B k N : Nat} {TL OP OG : List Nat} {OS : List (List Nat)}
    {α β : Equiv.Perm (Fin n)} (hA : Raw.Orb.PRep n w A α)
    (hB : Raw.Orb.PRep n w B β) (h : imgOK n w A B TL k OS OP OG N = true)
    (hd : distinctOK w OS N = true) :
    (∀ p ∈ lgetL OS 0, lget TL p = k) ∧
    (∀ i < N, ∃ g ∈ Subgroup.closure {α, β}, ∀ p : Fin n,
      (p : Nat) ∈ lgetL OS i ↔ ((g⁻¹ p : Fin n) : Nat) ∈ lgetL OS 0) ∧
    ∀ i < N, ∀ j < i, ∃ p : Fin n, ¬ ((p : Nat) ∈ lgetL OS i ↔ (p : Nat) ∈ lgetL OS j) := by
  obtain ⟨h0, hfacts⟩ := ksLY_img_facts h
  refine ⟨h0, fun i hiN => ksLY_img_mem hA hB hfacts i hiN, ?_⟩
  intro i hiN j hji
  exact ksLY_img_distinct hfacts hd hiN hji

end CFSG.KC.LyY

end
