module

public import CFSG.Certificates.Kernel.Enum.ZChk
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w : Nat}

theorem beq_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, by
  rintro rfl; exact Nat.beq_refl a⟩

theorem bIf_ft {c : Bool} (h : Bool.rec (motive := fun _ => Bool) true false c = true) :
    c = false := by
  cases c
  · rfl
  · exact absurd h Bool.false_ne_true

theorem bIf_true {c t e : Bool} (hc : c = true)
    (h : Bool.rec (motive := fun _ => Bool) e t c = true) : t = true := by
  subst hc
  exact h

theorem bIf_false {c t e : Bool} (hc : c = false)
    (h : Bool.rec (motive := fun _ => Bool) e t c = true) : e = true := by
  subst hc
  exact h

theorem eq2_iff {m r p q : Nat} :
    eq2 n w m r p q = true ↔ ∀ i < n, pg w m r i = pg w m p (pg w m q i) := by
  unfold eq2
  simp only [PK.allN_iff, beq_iff]

theorem eq3_iff {m r p q s : Nat} :
    eq3 n w m r p q s = true ↔ ∀ i < n, pg w m r i = pg w m p (pg w m q (pg w m s i)) := by
  unfold eq3
  simp only [PK.allN_iff, beq_iff]

theorem invoOK_sound {m nw x : Nat} (h : invoOK n w m nw x = true) :
    Nat.shiftRight x nw = 0 ∧ ∀ i < n, pg w m x i < n ∧ pg w m x (pg w m x i) = i := by
  unfold invoOK at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, PK.strictB_eq, Nat.blt_eq,
    beq_iff] at h
  exact h

theorem permOK_sound {m nw p q : Nat} (h : permOK n w m nw p q = true) :
    Nat.shiftRight p nw = 0 ∧ Nat.shiftRight q nw = 0 ∧
      ∀ i < n, pg w m p i < n ∧ pg w m q (pg w m p i) = i := by
  unfold permOK at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, PK.strictB_eq, Nat.blt_eq,
    beq_iff] at h
  exact h

theorem prep_unique {P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g) (hh : PRep n w P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_one {P : Nat} (h : ∀ i < n, pg w (mask w) P i = i) : PRep n w P 1 :=
  fun x => h x x.2

theorem eq2_prep {r p q : Nat} {gp gq : Equiv.Perm (Fin n)} (h : eq2 n w (mask w) r p q = true)
    (hp : PRep n w p gp) (hq : PRep n w q gq) : PRep n w r (gp * gq) := fun x => by
  rw [eq2_iff.1 h x x.2, hq x, hp (gq x)]
  rfl

theorem eq3_prep {r p q s : Nat} {gp gq gs : Equiv.Perm (Fin n)}
    (h : eq3 n w (mask w) r p q s = true) (hp : PRep n w p gp) (hq : PRep n w q gq)
    (hs : PRep n w s gs) : PRep n w r (gp * gq * gs) := fun x => by
  rw [eq3_iff.1 h x x.2, hs x, hq (gs x), hp (gq (gs x))]
  rfl

theorem invoOK_perm {nw x : Nat} (h : invoOK n w (mask w) nw x = true) :
    ∃ u : Equiv.Perm (Fin n), PRep n w x u ∧ u * u = 1 := by
  obtain ⟨-, h⟩ := invoOK_sound h
  let f : Fin n → Fin n := fun i => ⟨pg w (mask w) x i, (h i i.2).1⟩
  have hf : Function.Involutive f := fun i => Fin.ext (h i i.2).2
  exact ⟨hf.toPerm f, fun _ => rfl, Equiv.ext fun i => hf i⟩

theorem permOK_perm {nw p q : Nat} (h : permOK n w (mask w) nw p q = true) :
    ∃ g : Equiv.Perm (Fin n), PRep n w p g ∧ PRep n w q g⁻¹ := by
  obtain ⟨-, -, h⟩ := permOK_sound h
  let f : Fin n → Fin n := fun i => ⟨pg w (mask w) p i, (h i i.2).1⟩
  have hinj : Function.Injective f := fun i j e => by
    have e' : pg w (mask w) p i = pg w (mask w) p j := congrArg Fin.val e
    exact Fin.ext (by rw [← (h i i.2).2, ← (h j j.2).2, e'])
  let g := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  refine ⟨g, fun _ => rfl, fun y => ?_⟩
  have hy : (y : Nat) = pg w (mask w) p (g⁻¹ y) := by
    have := congrArg Fin.val (g.apply_symm_apply y)
    exact this.symm
  rw [hy, (h _ (g⁻¹ y).2).2]

theorem prep_at {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) {i : Nat} (hi : i < n) :
    pg w (mask w) P i = g ⟨i, hi⟩ :=
  hP ⟨i, hi⟩

theorem lChk_sound {T : Nat → Nat} {sh lm rb rm m nw pm iw im nL a ai b bi i : Nat}
    (h : lChk T sh lm rb rm n w m nw pm iw im nL a ai b bi i = true) :
    invoOK n w m nw (rperm T sh lm rb rm pm i) = true ∧
      (∃ ca < nL, eq3 n w m (rperm T sh lm rb rm pm ca) a (rperm T sh lm rb rm pm i) ai = true) ∧
      ∃ cb < nL, eq3 n w m (rperm T sh lm rb rm pm cb) b (rperm T sh lm rb rm pm i) bi = true := by
  unfold lChk at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.strictB_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, ⟨_, h2, h4⟩, ⟨_, h3, h5⟩⟩

theorem lRange_iff {T : Nat → Nat} {sh lm rb rm m nw pm iw im nL a ai b bi lo cnt : Nat} :
    lRange T sh lm rb rm n w m nw pm iw im nL a ai b bi lo cnt = true ↔
      ∀ k < cnt, lChk T sh lm rb rm n w m nw pm iw im nL a ai b bi (lo + k) = true := by
  unfold lRange
  exact PK.allN_iff

theorem lList_prep {T : Nat → Nat} {sh lm rb rm nw pm iw im nL a ai b bi : Nat}
    {ga gb : Equiv.Perm (Fin n)}
    (hL : ∀ i < nL, lChk T sh lm rb rm n w (mask w) nw pm iw im nL a ai b bi i = true)
    (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) :
    ∃ U : Nat → Equiv.Perm (Fin n),
      (∀ i < nL, PRep n w (rperm T sh lm rb rm pm i) (U i) ∧ U i * U i = 1) ∧
      ∀ i < nL, (∃ j < nL, U j = ga * U i * ga⁻¹) ∧ ∃ j < nL, U j = gb * U i * gb⁻¹ := by
  classical
  have hu : ∀ i, ∃ u : Equiv.Perm (Fin n), i < nL →
      PRep n w (rperm T sh lm rb rm pm i) u ∧ u * u = 1 := fun i => by
    by_cases hi : i < nL
    · obtain ⟨u, hu⟩ := invoOK_perm (lChk_sound (hL i hi)).1
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose U hU using hu
  refine ⟨U, fun i hi => hU i hi, fun i hi => ?_⟩
  obtain ⟨-, ⟨ca, hca, e1⟩, ⟨cb, hcb, e2⟩⟩ := lChk_sound (hL i hi)
  exact ⟨⟨ca, hca, prep_unique (hU ca hca).1 (eq3_prep e1 ha (hU i hi).1 hai)⟩,
    ⟨cb, hcb, prep_unique (hU cb hcb).1 (eq3_prep e2 hb (hU i hi).1 hbi)⟩⟩

theorem zPowOK_sound {m nw z nZ : Nat} {Z Zi : Nat → Nat} (h : zPowOK n w m nw z Z Zi nZ = true) :
    (∀ p < n, pg w m (Z 0) p = p) ∧ ∀ e < nZ, permOK n w m nw (Z e) (Zi e) = true ∧
      (e + 1 < nZ → eq2 n w m (Z (e + 1)) (Z e) z = true) := by
  unfold zPowOK at h
  simp only [PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [PK.allN_iff] at h1 h2
  refine ⟨fun p hp => (beq_iff _ _).1 (h1 p hp), fun e he => ?_⟩
  have h3 := h2 e he
  rw [Bool.and_eq_true] at h3
  refine ⟨h3.1, fun hs => ?_⟩
  have hb : Nat.blt (Nat.succ e) nZ = true := by
    rw [Nat.blt_eq]
    exact hs
  exact bIf_true hb h3.2

theorem zPowOK_prep {nw z nZ : Nat} {Z Zi : Nat → Nat} {gz : Equiv.Perm (Fin n)}
    (h : zPowOK n w (mask w) nw z Z Zi nZ = true) (hz : PRep n w z gz) :
    ∀ e < nZ, PRep n w (Z e) (gz ^ e) ∧ PRep n w (Zi e) (gz ^ e)⁻¹ := by
  obtain ⟨h0, hs⟩ := zPowOK_sound h
  have hZ : ∀ e < nZ, PRep n w (Z e) (gz ^ e) := by
    intro e
    induction e with
    | zero => exact fun _ => by rw [pow_zero]; exact prep_one h0
    | succ e ih =>
      intro he
      rw [pow_succ]
      exact eq2_prep ((hs e (by omega)).2 he) (ih (by omega)) hz
  intro e he
  refine ⟨hZ e he, fun y => ?_⟩
  obtain ⟨-, -, hp⟩ := permOK_sound (hs e he).1
  have hy : (y : Nat) = pg w (mask w) (Z e) ((gz ^ e)⁻¹ y) := by
    have e1 := congrArg (fun g : Equiv.Perm (Fin n) => g y) (mul_inv_cancel (gz ^ e))
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e1
    rw [hZ e he, e1]
  rw [hy, (hp _ ((gz ^ e)⁻¹ y).2).2]

theorem zChk_sound {T : Nat → Nat} {sh lm rb rm m nw pm iw im nL nZ i : Nat} {Z Zi : Nat → Nat}
    (h : zChk T sh lm rb rm n w m nw pm iw im nL Z Zi nZ i = true) :
    ∃ e, 0 < e ∧ e < nZ ∧ ∃ j < nL, ∃ p < n,
      eq3 n w m (rperm T sh lm rb rm pm j) (Z e) (rperm T sh lm rb rm pm i) (Zi e) = true ∧
      pg w m (rperm T sh lm rb rm pm i) (pg w m (rperm T sh lm rb rm pm j) p) ≠
        pg w m (rperm T sh lm rb rm pm j) (pg w m (rperm T sh lm rb rm pm i) p) := by
  unfold zChk at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.strictB_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨_, h1, h2, _, h3, _, h4, h5, Nat.ne_of_beq_eq_false (bIf_ft h6)⟩

theorem zRange_iff {T : Nat → Nat} {sh lm rb rm m nw pm iw im nL nZ lo cnt : Nat}
    {Z Zi : Nat → Nat} :
    zRange T sh lm rb rm n w m nw pm iw im nL Z Zi nZ lo cnt = true ↔
      ∀ k < cnt, zChk T sh lm rb rm n w m nw pm iw im nL Z Zi nZ (lo + k) = true := by
  unfold zRange
  exact PK.allN_iff

theorem zChk_prep {T : Nat → Nat} {sh lm rb rm nw pm iw im nL nZ i : Nat} {Z Zi : Nat → Nat}
    {gz : Equiv.Perm (Fin n)} {U : Nat → Equiv.Perm (Fin n)}
    (h : zChk T sh lm rb rm n w (mask w) nw pm iw im nL Z Zi nZ i = true)
    (hU : ∀ j < nL, PRep n w (rperm T sh lm rb rm pm j) (U j)) (hi : i < nL)
    (hZ : ∀ e < nZ, PRep n w (Z e) (gz ^ e) ∧ PRep n w (Zi e) (gz ^ e)⁻¹) :
    ∃ e, 0 < e ∧ e < nZ ∧ ∃ j < nL, U j = gz ^ e * U i * (gz ^ e)⁻¹ ∧
      U i * U j ≠ U j * U i := by
  obtain ⟨e, he0, he, j, hj, p, hp, h3, hne⟩ := zChk_sound h
  refine ⟨e, he0, he, j, hj,
    prep_unique (hU j hj) (eq3_prep h3 (hZ e he).1 (hU i hi) (hZ e he).2), fun hc => hne ?_⟩
  have e1 := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨p, hp⟩ : Fin n) : Nat)) hc
  simp only [Equiv.Perm.mul_apply] at e1
  rw [prep_at (hU j hj) hp, hU i hi, prep_at (hU i hi) hp, hU j hj]
  exact e1

end CFSG.KC.EnumSound

end
