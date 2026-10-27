module

public import CFSG.Certificates.Kernel.MaxD2.Basic
public import CFSG.Certificates.Kernel.Fi22LH.Prim

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.PSL3Four.Native

section

variable {n w : Nat}

@[expose] def LPerm (n w : Nat) (L : Nat → Nat) (p : Nat) : Prop :=
  (∀ x < n, pg w (mask w) p x < n) ∧ (∀ x < n, ∀ y < n, pg w (mask w) p x = pg w (mask w) p y → x = y) ∧
    ∀ x < n, L (pg w (mask w) p x) = L x

theorem lperm_pc (hn : szOK n w = true) {L : Nat → Nat} {p q : Nat} (hp : LPerm n w L p)
    (hq : LPerm n w L q) : LPerm n w L (pcomp n w (mask w) p q) := by
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_, fun x hx => ?_⟩
  · rw [pg_pc hn hx]
    exact hp.1 _ (hq.1 x hx)
  · rw [pg_pc hn hx, pg_pc hn hy] at e
    exact hq.2.1 x hx y hy (hp.2.1 _ (hq.1 x hx) _ (hq.1 y hy) e)
  · rw [pg_pc hn hx, hp.2.2 _ (hq.1 x hx), hq.2.2 x hx]

theorem enum_facts (hn : szOK n w = true) {k cnt cap : Nat} {G GI GN T PL POS SRT SRI : Nat → Nat}
    {L : Nat → Nat} (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true)
    (hG : ∀ j < k, permOK n w (mask w) (n * w) (G j) (GN j) = true)
    (hL : labK n w k G L = true) : ∀ i < cnt, LPerm n w L (T i) := by
  have hGL : ∀ j < k, LPerm n w L (G j) := fun j hj => by
    have hs := perm_spec (hG j hj)
    refine ⟨fun x hx => (hs.1 x hx).1, fun x hx y hy e => ?_, fun x hx => ?_⟩
    · rw [← (hs.1 x hx).2, ← (hs.1 y hy).2, e]
    · unfold labK at hL
      have := (PK.allN_iff.1 hL) j hj
      rw [PK.strictB_eq] at this
      exact Nat.eq_of_beq_eq_true ((PK.allN_iff.1 this) x hx)
  unfold penumHdK at hh
  simp only [PK.bAnd_eq, Bool.and_eq_true] at hh
  have hT0 : T 0 = pidn n w := Nat.eq_of_beq_eq_true hh.2.2.1
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      rw [hT0]
      refine ⟨fun x hx => by rw [pidn_get hn hx]; exact hx, fun x hx y hy e => ?_,
        fun x hx => by rw [pidn_get hn hx]⟩
      rwa [pidn_get hn hx, pidn_get hn hy] at e
    · obtain ⟨h1, h2, h3⟩ := (pt_spec (hp i hi)).2 h0
      rw [h3]
      exact lperm_pc hn (hGL _ h2) (ih _ h1 (by omega))

theorem sum_bij_range {b : Nat → Nat} (hb : ∀ x < n, b x < n)
    (hinj : ∀ x < n, ∀ y < n, b x = b y → x = y) (F : Nat → Nat) :
    ∑ y ∈ Finset.range n, F (b y) = ∑ z ∈ Finset.range n, F z := by
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => b a) (fun a ha => by simpa using hb a (by simpa using ha))
    (fun a₁ a₂ h₁ h₂ e => hinj a₁ (by simpa using h₁) a₂ (by simpa using h₂) e) le_rfl
  refine Finset.sum_nbij b (fun a ha => by simpa using hb a (by simpa using ha))
    (fun x hx y hy e => hinj x (by simpa using hx) y (by simpa using hy) e) (fun z hz => ?_)
    (fun _ _ => rfl)
  obtain ⟨a, ha, e⟩ := hsurj z hz
  exact ⟨a, ha, e.symm⟩

theorem mkey_eq (hn : szOK n w = true) {hi cw nl : Nat} {L : Nat → Nat} {g gi g' a b : Nat}
    (hm : n ≤ 64 * hi) (hg : permOK n w (mask w) (n * w) g gi = true) (hg' : ∀ y < n, pg w (mask w) g' y < n)
    (ha : LPerm n w L a) (hb : LPerm n w L b)
    (h : ∀ y < n, pg w (mask w) gi (pg w (mask w) a (pg w (mask w) g' y)) = pg w (mask w) b y) :
    mkeyK n w hi cw nl L g' = mkeyK n w hi cw nl L g := by
  have hs := perm_spec hg
  unfold mkeyK
  rw [CFSG.KS.Fi22LH.sumBelow_eq _ _ _ hm, CFSG.KS.Fi22LH.sumBelow_eq _ _ _ hm]
  have e : ∀ y ∈ Finset.range n,
      Nat.shiftLeft 1 (Nat.mul cw (Nat.add (Nat.mul nl (L (pg w (mask w) g' y))) (L y))) =
      (fun z => Nat.shiftLeft 1 (Nat.mul cw (Nat.add (Nat.mul nl (L (pg w (mask w) g z))) (L z))))
        (pg w (mask w) b y) := fun y hy => by
    have hy' : y < n := by simpa using hy
    have e1 : pg w (mask w) a (pg w (mask w) g' y) = pg w (mask w) g (pg w (mask w) b y) := by
      rw [← h y hy', (hs.2 _ (ha.1 _ (hg' y hy'))).2]
    have e2 : L (pg w (mask w) g' y) = L (pg w (mask w) g (pg w (mask w) b y)) := by
      rw [← e1, ha.2.2 _ (hg' y hy')]
    simp only []
    rw [e2, hb.2.2 y hy']
  rw [Finset.sum_congr rfl e]
  exact sum_bij_range (F := fun z =>
    Nat.shiftLeft 1 (Nat.mul cw (Nat.add (Nat.mul nl (L (pg w (mask w) g z))) (L z)))) hb.1 hb.2.1

end

end CFSG.KS.MaxD2

end
