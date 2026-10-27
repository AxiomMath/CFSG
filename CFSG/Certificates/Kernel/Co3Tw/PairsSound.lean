module

public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Certificates.Data.Kernel.Co3Tw.Pairs

public section

namespace CFSG.KC.Co3Tw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem sB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bA_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bI_eq (c t e : Bool) : bIf(c, t, e) = (if c = true then t else e) := by cases c <;> rfl

section Base

variable {n w BP nb : Nat} {H : Subgroup (Equiv.Perm (Fin n))}

@[expose] def SepB (n w BP nb : Nat) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∀ t < nb, pg w (mask w) BP t < n) ∧
    ∀ g ∈ H, (∀ t < nb, ∀ hb : pg w (mask w) BP t < n, g ⟨_, hb⟩ = ⟨_, hb⟩) → g = 1

theorem SepB.eq (hS : SepB n w BP nb H) {g g' : Equiv.Perm (Fin n)} (hg : g ∈ H) (hg' : g' ∈ H)
    (h : ∀ t < nb, ∀ hb : pg w (mask w) BP t < n, ((g ⟨_, hb⟩ : Fin n) : Nat) = g' ⟨_, hb⟩) :
    g = g' := by
  have h1 := hS.2 (g'⁻¹ * g) (H.mul_mem (H.inv_mem hg') hg) fun t ht hb => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h t ht hb)
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem prep_at {P b : Nat} {g : Equiv.Perm (Fin n)} (hP : Orb.PRep n w P g) (hb : b < n) :
    pg w (mask w) P b = g ⟨b, hb⟩ :=
  hP ⟨b, hb⟩

theorem baseT {f : Nat → Bool} (h : allN nb (fun t => strictB (pg w (mask w) BP t) f) = true)
    {t : Nat} (ht : t < nb) : f (pg w (mask w) BP t) = true := by
  have e := Orb.allN_iff.1 h t ht
  rwa [sB_eq] at e

theorem eqB_sound (hS : SepB n w BP nb H) {p q r s : Nat} {P Q R S : Equiv.Perm (Fin n)}
    (hp : Orb.PRep n w p P) (hq : Orb.PRep n w q Q) (hr : Orb.PRep n w r R)
    (hs : Orb.PRep n w s S) (hP : P ∈ H) (hQ : Q ∈ H) (hR : R ∈ H) (hSm : S ∈ H)
    (h : eqB w (mask w) BP nb p q r s = true) : P * Q = R * S := by
  refine hS.eq (H.mul_mem hP hQ) (H.mul_mem hR hSm) fun t ht hb => ?_
  have e := Nat.eq_of_beq_eq_true (baseT h ht)
  rw [prep_at hq hb, hp, prep_at hs hb, hr] at e
  exact e

theorem idB_sound (hS : SepB n w BP nb H) {p : Nat} {P : Equiv.Perm (Fin n)}
    (hp : Orb.PRep n w p P) (hP : P ∈ H) (h : idB w (mask w) BP nb p = true) : P = 1 := by
  refine hS.eq hP H.one_mem fun t ht hb => ?_
  have e := Nat.eq_of_beq_eq_true (baseT h ht)
  rw [prep_at hp hb] at e
  exact e

theorem eq1B_sound (hS : SepB n w BP nb H) {p q : Nat} {P Q : Equiv.Perm (Fin n)}
    (hp : Orb.PRep n w p P) (hq : Orb.PRep n w q Q) (hP : P ∈ H) (hQ : Q ∈ H)
    (h : eq1B w (mask w) BP nb p q = true) : P = Q := by
  refine hS.eq hP hQ fun t ht hb => ?_
  have e := Nat.eq_of_beq_eq_true (baseT h ht)
  rw [prep_at hp hb, prep_at hq hb] at e
  exact e

theorem sqB_sound (hS : SepB n w BP nb H) {p q : Nat} {P Q : Equiv.Perm (Fin n)}
    (hp : Orb.PRep n w p P) (hq : Orb.PRep n w q Q) (hP : P ∈ H) (hQ : Q ∈ H)
    (h : sqB w (mask w) BP nb p q = true) : P = Q * Q := by
  refine hS.eq hP (H.mul_mem hQ hQ) fun t ht hb => ?_
  have e := Nat.eq_of_beq_eq_true (baseT h ht)
  rw [prep_at hp hb, prep_at hq hb, hq] at e
  exact e

theorem cubeB_of_pow (hb : ∀ t < nb, pg w (mask w) BP t < n) {p : Nat} {P : Equiv.Perm (Fin n)}
    (hp : Orb.PRep n w p P) (h3 : P ^ 3 = 1) : cubeB w (mask w) BP nb p = true := by
  refine Orb.allN_iff.2 fun t ht => ?_
  rw [sB_eq, Nat.beq_eq]
  have hbt := hb t ht
  rw [prep_at hp hbt, hp, hp]
  have e := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨_, hbt⟩ : Fin n) : Nat)) h3
  simpa [pow_succ, Equiv.Perm.mul_apply] using e

theorem conjB_sound (hS : SepB n w BP nb H) {cg tp x d : Nat} {CG TP X D : Equiv.Perm (Fin n)}
    (hc : Orb.PRep n w cg CG) (ht : Orb.PRep n w tp TP) (hx : Orb.PRep n w x X)
    (hd : Orb.PRep n w d D) (hC : CG ∈ H) (hT : TP ∈ H) (hX : X ∈ H) (hD : D ∈ H)
    (h : conjB w (mask w) BP nb cg tp x d = true) : CG * TP * X = D * (CG * TP) := by
  refine hS.eq (H.mul_mem (H.mul_mem hC hT) hX) (H.mul_mem hD (H.mul_mem hC hT))
    fun t ht' hb => ?_
  have e := Nat.eq_of_beq_eq_true (baseT h ht')
  rw [prep_at hx hb, ht, hc, prep_at ht hb, hc, hd] at e
  exact e

end Base

@[expose] def jOf (d : Nat) : Nat := Nat.land d 4095

theorem crChk_cons (w m BP nb N NR RP : Nat) (T : Nat → Nat) (d : Nat) (L : List Nat) (lo : Nat) :
    crChk w m BP nb N NR RP T (d :: L) lo =
      (crOK w m BP nb N NR RP T lo d && crChk w m BP nb N NR RP T L (Nat.succ (jOf d))) := by
  rw [← bA_eq]
  rfl

theorem pairwise_of_lo {L : List Nat} {d : Nat} (h : ∀ e ∈ L, Nat.succ (jOf d) ≤ jOf e)
    (hL : List.Pairwise (· < ·) (L.map jOf)) : List.Pairwise (· < ·) ((d :: L).map jOf) := by
  rw [List.map_cons, List.pairwise_cons]
  refine ⟨fun a ha => ?_, hL⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
  exact h e he

variable {n w BP nb : Nat} {H : Subgroup (Equiv.Perm (Fin n))}

theorem crChk_sound (hS : SepB n w BP nb H) {N NR RP : Nat} {T : Nat → Nat}
    {Tp : Nat → Equiv.Perm (Fin n)} (hT : ∀ i < N, Orb.PRep n w (T i) (Tp i) ∧ Tp i ∈ H)
    (hRP : ∀ r < NR, f12 RP r < N) :
    ∀ (L : List Nat) (lo : Nat), crChk w (mask w) BP nb N NR RP T L lo = true →
      List.Pairwise (· < ·) (L.map jOf) ∧ ∀ d ∈ L, lo ≤ jOf d ∧ jOf d < N ∧
        fld(d, 12, 4095) < NR ∧ Nat.shiftRight d 24 < N ∧
        Tp (Nat.shiftRight d 24) * Tp (jOf d) =
          Tp (f12 RP (fld(d, 12, 4095))) * Tp (Nat.shiftRight d 24)
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | d :: L, lo, h => by
    rw [crChk_cons, Bool.and_eq_true] at h
    obtain ⟨hd, hL⟩ := h
    obtain ⟨ihp, ihm⟩ := crChk_sound hS hT hRP L _ hL
    unfold crOK at hd
    simp only [sB_eq, bA_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hd
    obtain ⟨⟨hlo, hjN⟩, ⟨hr, htN⟩, he⟩ := hd
    have hdd : lo ≤ jOf d ∧ jOf d < N ∧ fld(d, 12, 4095) < NR ∧ Nat.shiftRight d 24 < N ∧
        Tp (Nat.shiftRight d 24) * Tp (jOf d) =
          Tp (f12 RP (fld(d, 12, 4095))) * Tp (Nat.shiftRight d 24) :=
      ⟨hlo, hjN, hr, htN, eqB_sound hS (hT _ htN).1 (hT _ hjN).1 (hT _ (hRP _ hr)).1 (hT _ htN).1
        (hT _ htN).2 (hT _ hjN).2 (hT _ (hRP _ hr)).2 (hT _ htN).2 he⟩
    refine ⟨pairwise_of_lo (fun e he => (ihm e he).1) ihp, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hdd
    · obtain ⟨h1, h2⟩ := ihm e he
      exact ⟨by omega, h2⟩

theorem prChk_cons (n w m BP nb N NC CC : Nat) (DPk T : Nat → Nat) (x e : Nat) (L : List Nat)
    (lo : Nat) :
    prChk n w m BP nb N NC CC DPk T x (e :: L) lo =
      (prOK n w m BP nb N NC CC DPk T x lo e && prChk n w m BP nb N NC CC DPk T x L
        (Nat.succ (jOf e))) := by
  rw [← bA_eq]
  rfl

@[expose] noncomputable def fNW (n w P i : Nat) : Nat := fld(P, Nat.mul (Nat.mul n w) i, mask (Nat.mul n w))

@[expose] def PairFact {n : Nat} (Tp CG : Nat → Equiv.Perm (Fin n))
    (Dk : Nat → Nat → Equiv.Perm (Fin n)) (NC N : Nat) (X Y : Equiv.Perm (Fin n)) : Prop :=
  X * Y = Y * X ∧ ((Y = 1 ∨ Y = X ∨ Y = X * X ∨ Y ^ 3 ≠ 1) ∨
    ∃ k < 7, ∃ c < NC, ∃ p < N, ∃ d1 < 8, ∃ d2 < 8,
      CG c * Tp p * X = Dk k d1 * (CG c * Tp p) ∧ CG c * Tp p * Y = Dk k d2 * (CG c * Tp p))

theorem rec_true {f t b : Bool} (h : Bool.rec (motive := fun _ => Bool) f t b = true) :
    (b = false ∧ f = true) ∨ (b = true ∧ t = true) := by
  cases b
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

theorem fld3_lt (e s : Nat) : fld(e, s, 7) < 8 :=
  Nat.lt_succ_of_le (Nat.and_le_right)

theorem prChk_sound (hS : SepB n w BP nb H) {N NC CC : Nat} {DPk T : Nat → Nat}
    {Tp CG : Nat → Equiv.Perm (Fin n)} {Dk : Nat → Nat → Equiv.Perm (Fin n)}
    (hT : ∀ i < N, Orb.PRep n w (T i) (Tp i) ∧ Tp i ∈ H)
    (hC : ∀ c < NC, Orb.PRep n w (fNW n w CC c) (CG c) ∧ CG c ∈ H)
    (hD : ∀ k < 7, ∀ d < 8, Orb.PRep n w (fNW n w (DPk k) d) (Dk k d) ∧ Dk k d ∈ H)
    {x : Nat} {X : Equiv.Perm (Fin n)} (hx : Orb.PRep n w x X) (hX : X ∈ H) :
    ∀ (L : List Nat) (lo : Nat), prChk n w (mask w) BP nb N NC CC DPk T x L lo = true →
      List.Pairwise (· < ·) (L.map jOf) ∧ ∀ e ∈ L, lo ≤ jOf e ∧ jOf e < N ∧
        PairFact Tp CG Dk NC N X (Tp (jOf e))
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => absurd h List.not_mem_nil⟩
  | e :: L, lo, h => by
    rw [prChk_cons, Bool.and_eq_true] at h
    obtain ⟨he, hL⟩ := h
    obtain ⟨ihp, ihm⟩ := prChk_sound hS hT hC hD hx hX L _ hL
    have hee : lo ≤ jOf e ∧ jOf e < N ∧ PairFact Tp CG Dk NC N X (Tp (jOf e)) := by
      unfold prOK at he
      simp only [sB_eq, bA_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at he
      obtain ⟨⟨hlo, hjN⟩, hxy, hk⟩ := he
      obtain ⟨hy, hY⟩ := hT _ hjN
      refine ⟨hlo, hjN, eqB_sound hS hx hy hy hx hX hY hY hX hxy, ?_⟩
      rcases rec_true hk with ⟨-, hk⟩ | ⟨-, hk⟩
      · left
        rcases rec_true hk with ⟨-, hk⟩ | ⟨h1, -⟩
        swap
        · exact Or.inl (idB_sound hS hy hY h1)
        rcases rec_true hk with ⟨-, hk⟩ | ⟨h2, -⟩
        swap
        · exact Or.inr (Or.inl (eq1B_sound hS hy hx hY hX h2))
        rcases rec_true hk with ⟨-, hk⟩ | ⟨h3, -⟩
        swap
        · exact Or.inr (Or.inr (Or.inl (sqB_sound hS hy hx hY hX h3)))
        refine Or.inr (Or.inr (Or.inr fun h3' => ?_))
        have hc := cubeB_of_pow hS.1 hy h3'
        rw [hc] at hk
        exact absurd hk (by decide)
      · right
        simp only [sB_eq, bA_eq, Bool.and_eq_true, Nat.blt_eq] at hk
        obtain ⟨⟨hk7, hcN, hpN⟩, h1, h2⟩ := hk
        obtain ⟨hc, hCm⟩ := hC _ hcN
        obtain ⟨hp, hPm⟩ := hT _ hpN
        obtain ⟨hd1, hD1⟩ := hD _ hk7 _ (fld3_lt e 36)
        obtain ⟨hd2, hD2⟩ := hD _ hk7 _ (fld3_lt e 39)
        exact ⟨_, hk7, _, hcN, _, hpN, _, fld3_lt e 36, _, fld3_lt e 39,
          conjB_sound hS hc hp hx hd1 hCm hPm hX hD1 h1,
          conjB_sound hS hc hp hy hd2 hCm hPm hY hD2 h2⟩
    refine ⟨pairwise_of_lo (fun e' he' => (ihm e' he').1) ihp, fun e' he' => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hee
    · obtain ⟨h1, h2⟩ := ihm e' he'
      exact ⟨by omega, h2⟩

end CFSG.KC.Co3Tw

end
