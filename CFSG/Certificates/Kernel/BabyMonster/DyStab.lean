module

public import CFSG.Certificates.Kernel.BabyMonster.PktSound
public import CFSG.Certificates.Kernel.BenesSound
public import CFSG.Certificates.Kernel.BabyMonster.DyStabDefs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.BM.Dy

open CFSG.KC.BM CFSG.KC.BM.Lat CFSG.KC.YModel CFSG.KC.BM.Pkt

@[expose] noncomputable def stOK (Bs : List (List Nat)) (F R : Nat → Nat) (s : Nat) : Bool :=
  Nat.beq (dyElim (nat_lit 256) Bs (nat_lit 0) (F s)) (R s)

theorem stOK_of {Bs : List (List Nat)} {F R : Nat → Nat} {s V W : Nat}
    (h : Nat.beq (dyElim (nat_lit 256) Bs (nat_lit 0) V) W = true) (hV : V = F s)
    (hW : W = R s) : stOK Bs F R s = true := by
  subst hV hW
  exact h

@[expose] noncomputable def monoF (Bs : List (List Nat)) (Ms : List Nat) (NM i : Nat) : Nat :=
  monoImg Ms dyDs NM i (recOf Bs i)

@[expose] noncomputable def colF (Bs : List (List Nat)) (Cs : List (List Nat)) (i : Nat) : Nat :=
  colorRed (colorImg Cs dyDs (Nat.shiftLeft (recOf Bs i) (Nat.mul (nat_lit 16) i)))

@[expose] noncomputable def netOK (Ms : List Nat) (T NM : Nat) : Bool :=
  andB (andB (benesOK Ms dyDs T NM) (negMaskOK NM)) (Nat.beq (lenL Ms) (nat_lit 25))

theorem rowsNe_sound {C : List (List Nat)} {X : Nat} : ∀ {n : Nat}, rowsNe C X n = true →
    ∀ i < n, Nat.blt (recOf C i) dyFail = true ∧ Nat.beq (recOf C i) X = false
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have e : rowsNe C X (n + 1) = andB (rowsNe C X n)
        (andB (Nat.blt (recOf C n) dyFail) (notB (Nat.beq (recOf C n) X))) := rfl
    obtain ⟨h1, h2⟩ := andB_true (e ▸ h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact rowsNe_sound h1 i hi
    · obtain ⟨h3, h4⟩ := andB_true h2
      refine ⟨h3, ?_⟩
      cases hb : Nat.beq (recOf C i) X
      · rfl
      · rw [hb] at h4
        exact absurd h4 Bool.false_ne_true

@[expose] def RowStab (Bs : List (List Nat)) (N : ℕ → ℕ → ℤ) (r i : ℕ) : Prop :=
  ∃ q : ℕ → ℤ, (∀ j < 4371, q j % 2 = if r.testBit j then 1 else 0) ∧
    ∀ u < 4371, ∃ w : ℤ, ∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * N t u =
      8 * (∑ j ∈ Finset.range 4371, q j * (ent Bs j u : ℤ) + 256 * w)

@[expose] noncomputable def colV (Cs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun C _ ih => andB (stagesOK (dropN (nat_lit 6) C) dyDs) ih) Cs

theorem stagesOK_neg : stagesOK [2 ^ 32 - 1] [16] = false := by decide +kernel

theorem fld_aligned {M : Nat} {c : Nat} (h : Nat.mul (Nat.land M (rep (nat_lit 1) (nat_lit 16) c))
    (nat_lit 65535) = M) (f : Nat) : fld M f = 0 ∨ fld M f = 65535 := by
  have hle : ∀ t, fld (M &&& rep 1 16 c) t ≤ 1 := fun t => by
    rw [fld_land, fld_rep (by decide)]
    split
    · exact Nat.and_le_right
    · rw [Nat.and_zero]
      decide
  have e : fld M f = 65535 * fld (M &&& rep 1 16 c) f := by
    conv_lhs => rw [← h]
    change fld ((M &&& rep 1 16 c) * 65535) f = _
    rw [Nat.mul_comm, fld_mul f (fun t => by have := hle t; omega)]
  have := hle f
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h0 | h1
  · left
    rw [e, h0]
  · right
    rw [e, h1]

theorem testBit_65535 : ∀ i < 16, (65535 : Nat).testBit i = true := by decide

theorem aligned_bit {M : Nat} (h : alignedM M = true) (f i : Nat) (hi : i < 16) :
    M.testBit (16 * f + i) = M.testBit (16 * f) := by
  have hf := fld_aligned (Nat.eq_of_beq_eq_true h) f
  rw [testBit_of_fld M (16 * f + i), testBit_of_fld M (16 * f),
    show (16 * f + i) / 16 = f by omega, show (16 * f + i) % 16 = i by omega,
    show 16 * f / 16 = f by omega, show 16 * f % 16 = 0 by omega]
  rcases hf with h0 | h1
  · rw [h0, Nat.zero_testBit, Nat.zero_testBit]
  · rw [h1, testBit_65535 i hi, testBit_65535 0 (by decide)]

@[expose] def tauF (d M f : Nat) : Nat :=
  if M.testBit (16 * f) = true then f + d
  else if d ≤ f ∧ M.testBit (16 * (f - d)) = true then f - d else f

theorem swp_aligned {d M : Nat} (hal : alignedM M = true) (f : Nat) {i : Nat} (hi : i < 16) :
    CFSG.KC.Benes.swp (16 * d) M (16 * f + i) = 16 * tauF d M f + i := by
  have hA := aligned_bit hal f i hi
  have hB : d ≤ f → M.testBit (16 * f + i - 16 * d) = M.testBit (16 * (f - d)) := fun hd => by
    rw [show 16 * f + i - 16 * d = 16 * (f - d) + i by omega, aligned_bit hal _ i hi]
  unfold CFSG.KC.Benes.swp tauF
  rw [hA]
  by_cases h1 : M.testBit (16 * f) = true
  · rw [ite_eq_left h1, ite_eq_left h1]
    omega
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases hd : d ≤ f
    · rw [hB hd]
      by_cases h3 : M.testBit (16 * (f - d)) = true
      · rw [ite_eq_left ⟨by omega, h3⟩, ite_eq_left ⟨hd, h3⟩]
        omega
      · rw [ite_eq_right (fun h => h3 h.2), ite_eq_right (fun h => h3 h.2)]
    · rw [ite_eq_right (fun h => hd (by omega)), ite_eq_right (fun h => hd h.1)]

theorem validIn_of_dswValid {D M : Nat}
    (hv : CFSG.KC.MonsterConv.Perm.dswValid (nat_lit 131072) D M = true) :
    CFSG.KC.Benes.ValidIn 131072 D M := by
  obtain ⟨h1, h2⟩ := andB_true hv
  exact CFSG.KC.Benes.validIn_of_dsw (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)

theorem fld_dsw {d M : Nat} (hal : alignedM M = true)
    (hv : CFSG.KC.MonsterConv.Perm.dswValid (nat_lit 131072) (16 * d) M = true) (x f : Nat) :
    fld (CFSG.KC.MonsterConv.Perm.dsw (16 * d) M x) f = fld x (tauF d M f) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [fld_testBit, fld_testBit]
  by_cases hi : i < 16
  · rw [CFSG.KC.Benes.testBit_dsw (CFSG.KC.Benes.validIn_disj (validIn_of_dswValid hv)),
      swp_aligned hal f hi]
  · simp [hi]

theorem tauF_tauF {d M : Nat} (hal : alignedM M = true)
    (hv : CFSG.KC.MonsterConv.Perm.dswValid (nat_lit 131072) (16 * d) M = true) (f : Nat) :
    tauF d M (tauF d M f) = f := by
  have h := CFSG.KC.Benes.swp_swp (CFSG.KC.Benes.validIn_disj (validIn_of_dswValid hv)) (16 * f)
  have e1 := swp_aligned (d := d) hal f (i := 0) (by decide)
  have e2 := swp_aligned (d := d) hal (tauF d M f) (i := 0) (by decide)
  simp only [Nat.add_zero] at e1 e2
  rw [e1, e2] at h
  omega

theorem tauF_lt {d M : Nat}
    (hv : CFSG.KC.MonsterConv.Perm.dswValid (nat_lit 131072) (16 * d) M = true) {f : Nat}
    (hf : f < 8192) : tauF d M f < 8192 := by
  have hV := validIn_of_dswValid hv
  unfold tauF
  split
  · rename_i h
    have := (hV _ h).1
    omega
  · split <;> omega

theorem tauF_hi {d M : Nat}
    (hv : CFSG.KC.MonsterConv.Perm.dswValid (nat_lit 131072) (16 * d) M = true) {f : Nat}
    (hf : 8192 ≤ f) : tauF d M f = f := by
  have hV := validIn_of_dswValid hv
  unfold tauF
  split
  · rename_i h
    have := (hV _ h).1
    omega
  · split
    · rename_i h
      obtain ⟨hd, h3⟩ := h
      have := (hV _ h3).1
      omega
    · rfl

theorem benes_cons (M D : Nat) (Ms Ds : List Nat) (x : Nat) :
    benes (M :: Ms) (D :: Ds) x = benes Ms Ds (CFSG.KC.MonsterConv.Perm.dsw D M x) := by
  show forceB (Nat.land (Nat.xor (Nat.shiftRight x D) x) M) (fun t =>
    forceB (Nat.xor x (Nat.xor t (Nat.shiftLeft t D))) (fun x' => benes Ms Ds x')) = _
  rw [forceB_apply, forceB_apply]
  rfl

theorem benes_fld : ∀ (Ms Ds : List Nat), allAligned Ms = true → shifts16 Ds = true →
    stagesOK Ms Ds = true → ∃ P Pi : Nat → Nat, (∀ x f, fld (benes Ms Ds x) f = fld x (P f)) ∧
      (∀ f, P (Pi f) = f) ∧ (∀ f, Pi (P f) = f) ∧ (∀ f, f < 8192 → P f < 8192) ∧
      (∀ f, 8192 ≤ f → P f = f)
  | [], _, _, _, _ => ⟨id, id, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h,
      fun _ _ => rfl⟩
  | _ :: _, [], _, _, _ => ⟨id, id, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ h => h,
      fun _ _ => rfl⟩
  | M :: Ms, D :: Ds, hal, hs, hst => by
    obtain ⟨hM, hal'⟩ := andB_true hal
    obtain ⟨hD, hs'⟩ := andB_true hs
    obtain ⟨hv, hst'⟩ := andB_true hst
    obtain ⟨d, rfl⟩ : ∃ d, D = 16 * d := ⟨D / 16, by
      have := Nat.eq_of_beq_eq_true hD
      change D % 16 = 0 at this
      omega⟩
    obtain ⟨P, Pi, hP, h1, h2, h3, h4⟩ := benes_fld Ms Ds hal' hs' hst'
    refine ⟨fun f => tauF d M (P f), fun f => Pi (tauF d M f), fun x f => ?_, fun f => ?_,
      fun f => ?_, fun f hf => tauF_lt hv (h3 f hf), fun f hf => ?_⟩
    · rw [benes_cons, hP, fld_dsw hM hv]
    · simp only
      rw [h1, tauF_tauF hM hv]
    · simp only
      rw [tauF_tauF hM hv, h2]
    · simp only
      rw [h4 f hf, tauF_hi hv hf]

theorem le_of_fld : ∀ (a : Nat) {b : Nat}, (∀ f, fld b f ≤ fld a f) → b ≤ a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : b = 0 := eq_zero_of_fld fun f => by
      have := h f
      rw [show fld 0 f = 0 by simp [fld]] at this
      omega
    omega
  · have h1 : b / 65536 ≤ a / 65536 := ih (a / 65536) (by omega) fun f => by
      have := h (f + 1)
      rwa [fld_succ, fld_succ] at this
    have h0 := h 0
    rw [fld_zero, fld_zero] at h0
    omega

theorem fld_sub : ∀ (t : Nat) {a b : Nat}, (∀ f, fld b f ≤ fld a f) →
    fld (a - b) t = fld a t - fld b t
  | 0, a, b, h => by
    have hba := le_of_fld a h
    have h0 := h 0
    simp only [fld_zero] at h0 ⊢
    omega
  | t + 1, a, b, h => by
    have hba := le_of_fld a h
    have h0 := h 0
    simp only [fld_zero] at h0
    have e : (a - b) / 65536 = a / 65536 - b / 65536 := by omega
    rw [fld_succ, fld_succ, fld_succ, e, fld_sub t (fun f => by
      have := h (f + 1)
      rwa [fld_succ, fld_succ] at this)]

theorem fld_land_dyMask' {m e : Nat} (hm : m = 2 ^ e) (he : e ≤ 16) (y t : Nat) :
    fld (y &&& dyMask m) t = if t < 4371 then fld y t % 2 ^ e else 0 := by
  subst hm
  exact fld_land_dyMask he y t

theorem negMask_facts {NM : Nat} (hN : negMaskOK NM = true) :
    (∀ f, fld NM f = 0 ∨ fld NM f = 65535) ∧ ∀ f, 4371 ≤ f → fld NM f = 0 := by
  obtain ⟨hN1, hN2⟩ := andB_true hN
  refine ⟨fld_aligned (Nat.eq_of_beq_eq_true hN2), fun f hf => ?_⟩
  have e := congrArg (fun x => fld x f) (Nat.eq_of_beq_eq_true hN1)
  simp only at e
  change fld (NM &&& dyMask 65536) f = fld NM f at e
  rw [fld_land_dyMask' (m := 65536) (e := 16) rfl le_rfl, ite_eq_right (by omega)] at e
  exact e.symm

theorem fld_negF {NM v : Nat} (hN : negMaskOK NM = true) (hv : ∀ f, fld v f ≤ 128) (f : Nat) :
    fld (negF NM v) f = if fld NM f = 65535 then (256 - fld v f) % 256 else fld v f := by
  obtain ⟨hNal, hNhi⟩ := negMask_facts hN
  have hw : ∀ f, fld (v &&& NM) f = if fld NM f = 65535 then fld v f else 0 := fun f => by
    rw [fld_land]
    rcases hNal f with h0 | h1
    · rw [h0, Nat.and_zero, ite_eq_right (by decide)]
    · rw [h1, ite_eq_left rfl, show (65535 : Nat) = 2 ^ 16 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by have := hv f; omega)]
  have hA : ∀ f, fld (NM &&& rep 256 16 4371) f = if fld NM f = 65535 then 256 else 0 := fun f => by
    rw [fld_land, fld_rep (by decide)]
    rcases hNal f with h0 | h1
    · rw [h0, Nat.zero_and, ite_eq_right (by decide)]
    · rw [h1, ite_eq_left rfl, ite_eq_left]
      · decide
      · by_contra hc
        rw [hNhi f (by omega)] at h1
        exact absurd h1 (by decide)
  have hwv : ∀ f, fld (v &&& NM) f ≤ fld v f := fun f => by
    rw [hw]
    split <;> omega
  have hwA : ∀ f, fld (v &&& NM) f ≤ fld (NM &&& rep 256 16 4371) f := fun f => by
    rw [hw, hA]
    split
    · have := hv f
      omega
    · exact le_rfl
  have h1 : ∀ f, fld (v - (v &&& NM)) f = if fld NM f = 65535 then 0 else fld v f := fun f => by
    rw [fld_sub f hwv, hw]
    split <;> omega
  have h2 : ∀ f, fld ((NM &&& rep 256 16 4371) - (v &&& NM) &&& dyMask 256) f =
      if fld NM f = 65535 then (256 - fld v f) % 256 else 0 := fun f => by
    rw [fld_land_dyMask' (m := 256) (e := 8) rfl (by decide), fld_sub f hwA, hA, hw]
    by_cases hNf : fld NM f = 65535
    · have ht : f < 4371 := by
        by_contra hc
        rw [hNhi f (by omega)] at hNf
        exact absurd hNf (by decide)
      simp [hNf, ht]
    · simp [hNf]
  change fld ((v - (v &&& NM)) + ((NM &&& rep 256 16 4371) - (v &&& NM) &&& dyMask 256)) f = _
  rw [fld_add f (fun f => by
    rw [h1, h2]
    have := hv f
    split <;> omega), h1, h2]
  split <;> omega

theorem tfield_eq (T t : Nat) : tfield T t = fld T t := by
  unfold tfield
  rw [land65535, fld_zero, fld]
  change T >>> (16 * t) % 65536 = _
  rw [Nat.shiftRight_eq_div_pow]

@[expose] noncomputable def labLoX (a : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun b ih => andB ih (Nat.beq (fld (labels 0 8192) (64 * a + b)) (64 * a + b))) (nat_lit 64)

theorem labels_lo_ok : Nat.rec (motive := fun _ => Bool) true
    (fun a ih => andB ih (labLoX a)) (nat_lit 128) = true := by
  decide +kernel

theorem labels_lo {u : Nat} (hu : u < 8192) : fld (labels 0 8192) u = u := by
  have ha := @recAnd_sound labLoX (nat_lit 128) labels_lo_ok (u / 64) (by change u / 64 < 128; omega)
  unfold labLoX at ha
  have hb := @recAnd_sound (fun b => Nat.beq (fld (labels 0 8192) (64 * (u / 64) + b))
    (64 * (u / 64) + b)) (nat_lit 64) ha (u % 64) (Nat.mod_lt _ (by decide))
  have e := Nat.eq_of_beq_eq_true hb
  rwa [Nat.div_add_mod] at e

theorem labels_hi_ok : labels 4371 8192 % 2 ^ (16 * 4371) = 0 := by
  decide +kernel

theorem fld_mod_pow {y n t : Nat} (ht : t < n) : fld (y % 2 ^ (16 * n)) t = fld y t := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [fld_testBit, fld_testBit, Nat.testBit_mod_two_pow]
  by_cases hr : r < 16
  · rw [decide_eq_true hr, Bool.true_and, Bool.true_and, decide_eq_true (by omega), Bool.true_and]
  · rw [decide_eq_false hr, Bool.false_and, Bool.false_and]

theorem fld_add_hi {a L n t : Nat} (hL : L % 2 ^ (16 * n) = 0) (ht : t < n) :
    fld (a + L) t = fld a t := by
  rw [← fld_mod_pow (y := a + L) ht, Nat.add_mod, hL, Nat.add_zero, Nat.mod_mod, fld_mod_pow ht]

theorem mono_net {Ms : List Nat} {T NM : Nat} (hs : shifts16 dyDs = true)
    (hal : allAligned Ms = true) (hn : netOK Ms T NM = true) (hv : netV Ms T = true) :
    ∃ P Pi : Nat → Nat, (∀ x f, fld (benes Ms dyDs x) f = fld x (P f)) ∧
      (∀ f, P (Pi f) = f) ∧ (∀ f, Pi (P f) = f) ∧
      (∀ t < 4371, Pi t < 4371 ∧ fld T t % 8192 = Pi t ∧
        fld T t / 8192 = if fld NM (Pi t) = 65535 then 1 else 0) ∧
      (∀ f, 4371 ≤ f → 4371 ≤ P f) := by
  obtain ⟨hst, htab⟩ := andB_true hv
  obtain ⟨hn, -⟩ := andB_true hn
  obtain ⟨hb, hN⟩ := andB_true hn
  obtain ⟨P, Pi, hP, h1, h2, h3, h4⟩ := benes_fld Ms dyDs hal hs hst
  have hz : benes Ms dyDs (T + labels 4371 8192) = labels 0 8192 + (NM &&& rep 8192 16 4371) :=
    Nat.eq_of_beq_eq_true hb
  obtain ⟨hNal, hNhi⟩ := negMask_facts hN
  have hlab : ∀ u < 8192, fld (labels 0 8192) u = u := fun u hu => labels_lo hu
  have hNr : ∀ u, fld (NM &&& rep 8192 16 4371) u = if fld NM u = 65535 then 8192 else 0 := by
    intro u
    rw [fld_land, fld_rep (by decide)]
    rcases hNal u with h0 | h1
    · rw [h0, Nat.zero_and, ite_eq_right (by decide)]
    · rw [h1, ite_eq_left rfl, ite_eq_left]
      · decide
      · by_contra hc
        rw [hNhi u (by omega)] at h1
        exact absurd h1 (by decide)
  have hzf : ∀ u < 8192, fld (labels 0 8192 + (NM &&& rep 8192 16 4371)) u =
      u + if fld NM u = 65535 then 8192 else 0 := by
    intro u hu
    rw [fld_add u (fun f => by
      rw [hNr]
      have := fld_lt (labels 0 8192) f
      split
      · rename_i h
        have hf : f < 4371 := by
          by_contra hc
          rw [hNhi f (by omega)] at h
          exact absurd h (by decide)
        rw [hlab f (by omega)]
        omega
      · omega), hlab u hu, hNr]
  have hy : ∀ t < 4371, fld (T + labels 4371 8192) t = fld T t := fun t ht =>
    fld_add_hi labels_hi_ok ht
  have hPi : ∀ f < 8192, Pi f < 8192 := fun f hf => by
    by_contra hc
    have := h4 (Pi f) (by omega)
    rw [h1] at this
    omega
  have htab' : ∀ t < 4371, fld T t % 8192 < 4371 := fun t ht => by
    unfold tabOK at htab
    have := (andB_true (@recAnd_sound (fun t => andB (Nat.blt (Nat.mod (tfield T t) (nat_lit 8192)) (nat_lit 4371))
      (Nat.blt (tfield T t) (nat_lit 16384))) (nat_lit 4371) htab t ht)).1
    have h' := Nat.le_of_ble_eq_true this
    rw [tfield_eq] at h'
    exact h'
  have key : ∀ t < 4371, fld T t = Pi t + if fld NM (Pi t) = 65535 then 8192 else 0 := by
    intro t ht
    have e := congrArg (fun x => fld x (Pi t)) hz
    rw [hP, h1, hy t ht, hzf _ (hPi t (by omega))] at e
    exact e
  refine ⟨P, Pi, hP, h1, h2, fun t ht => ?_, fun f hf => ?_⟩
  · have hk := key t ht
    have hlt := htab' t ht
    have hPt := hPi t (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hk] at hlt
      split at hlt <;> omega
    · rw [hk]
      split <;> omega
    · rw [hk]
      split <;> omega
  · by_contra hc
    have hPf : P f < 4371 := by omega
    have hf8 : f < 8192 := by
      by_contra hc'
      rw [h4 f (by omega)] at hPf
      omega
    have := (key _ hPf)
    rw [h2] at this
    have hlt := htab' _ hPf
    rw [this] at hlt
    split at hlt <;> omega

theorem mono_row {Bs : List (List Nat)} {Ms : List Nat} {T NM : Nat}
    (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK (nat_lit 4371) j (recOf Bs j) = true)
    (hs : shifts16 dyDs = true) (hal : allAligned Ms = true) (hn : netOK Ms T NM = true)
    (hv : netV Ms T = true) {i : Nat} (hi : i < 4371)
    (hne : dyElim (2 ^ 8) Bs 0 (monoF Bs Ms NM i) ≠ dyFail) :
    ∃ Q : ℕ → ℕ, (∀ j', (dyElim (2 ^ 8) Bs 0 (monoF Bs Ms NM i)).testBit j' =
        decide (Q j' % 2 = 1)) ∧
      ∀ u < 4371, ∃ w : ℤ, ∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * kNumMono T t u =
        8 * (∑ j ∈ Finset.range 4371, (Q j : ℤ) * (ent Bs j u : ℤ) + 256 * w) := by
  obtain ⟨P, Pi, hP, h1, h2, hT, hhi⟩ := mono_net hs hal hn hv
  obtain ⟨⟨e', he', hp⟩, hb, hbf⟩ := dyRowOK_facts (by decide) (hr i hi)
  have hb : recOf Bs i < 2 ^ (16 * (4371 - i)) := hb
  have hN := (andB_true (andB_true hn).1).2
  have hent : ∀ c, ent Bs i c ≤ 128 := fun c => by
    unfold ent
    split
    · omega
    · rcases Nat.eq_zero_or_pos (c - i) with h0 | h0
      · rw [h0, hp]
        exact Nat.pow_le_pow_right (by decide) he'
      · exact (hbf _ h0).le
  have hent0 : ∀ c, 4371 ≤ c → ent Bs i c = 0 := fun c hc => by
    unfold ent
    split
    · rfl
    · exact fld_of_lt hb (by omega)
  set x := Nat.shiftLeft (recOf Bs i) (Nat.mul 16 i) with hx
  have hxf : ∀ c, fld x c = ent Bs i c := fun c => by
    rw [hx]
    exact fld_shl16 _ _ _
  set y := benes Ms dyDs x with hy
  have hyf : ∀ u, fld y u = ent Bs i (P u) := fun u => by rw [hy, hP, hxf]
  have hyle : ∀ u, fld y u ≤ 128 := fun u => by rw [hyf]; exact hent _
  have hv0 : monoF Bs Ms NM i = negF NM y := rfl
  have hv0f : ∀ u, fld (monoF Bs Ms NM i) u =
      if fld NM u = 65535 then (256 - ent Bs i (P u)) % 256 else ent Bs i (P u) := fun u => by
    rw [hv0, fld_negF hN hyle, hyf]
  have hNhi := (negMask_facts hN).2
  have hlt : monoF Bs Ms NM i < 2 ^ (16 * (4371 - 0)) := by
    apply lt_of_fld
    intro u hu
    rw [hv0f, hNhi u (by omega), ite_eq_right (by decide), hent0 _ (hhi u (by omega))]
  have hf : ∀ u, fld (monoF Bs Ms NM i) u < 2 ^ 8 := fun u => by
    rw [hv0f]
    have := hent (P u)
    split
    · exact Nat.mod_lt _ (by decide)
    · exact lt_of_le_of_lt this (by decide)
  obtain ⟨Q, -, hQo, hres⟩ := dyElim_sound (by decide) hB hr (by decide) hlt hf hne
  refine ⟨Q, hQo, fun u hu => ?_⟩
  ·
    set s : ℤ := if fld NM u = 65535 then -1 else 1 with hsdef
    have hk : ∀ t, kNumMono T t u =
        if u = fld T t % 8192 then (if fld T t / 8192 = 1 then (-8 : ℤ) else 8) else 0 :=
      fun t => rfl
    have hsum : ∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * kNumMono T t u =
        8 * (s * (ent Bs i (P u) : ℤ)) := by
      have hz : ∀ t < 4371, t ≠ P u → kNumMono T t u = 0 := by
        intro t ht htu
        obtain ⟨-, hm, -⟩ := hT t ht
        rw [hk, ite_eq_right]
        rw [hm]
        intro hu'
        apply htu
        rw [hu', h1]
      by_cases hPu : P u < 4371
      · rw [Finset.sum_eq_single (P u)]
        · obtain ⟨-, hm, hd⟩ := hT (P u) hPu
          rw [h2] at hm hd
          rw [hk, ite_eq_left hm.symm, hd, hsdef]
          split <;> simp <;> ring
        · intro t ht htu
          rw [hz t (Finset.mem_range.1 ht) htu, mul_zero]
        · intro hn'
          exact absurd (Finset.mem_range.2 hPu) hn'
      · rw [hent0 _ (by omega), Nat.cast_zero, mul_zero, mul_zero]
        apply Finset.sum_eq_zero
        intro t ht
        have ht' := Finset.mem_range.1 ht
        rw [hz t ht' (fun e => hPu (e ▸ ht')), mul_zero]
    have hc := hres u (Nat.zero_le u) hu
    rw [Nat.sub_zero, hv0f, comb_eq] at hc
    have hmod : ((if fld NM u = 65535 then (256 - ent Bs i (P u)) % 256 else ent Bs i (P u) : ℕ)
        : ℤ) ≡ s * (ent Bs i (P u) : ℤ) [ZMOD 256] := by
      rw [hsdef]
      split
      · have hle := hent (P u)
        rw [Int.natCast_emod]
        refine (Int.mod_modEq _ _).trans ?_
        rw [Int.modEq_iff_dvd]
        refine ⟨-1, ?_⟩
        push_cast [Nat.cast_sub (show ent Bs i (P u) ≤ 256 by omega)]
        ring
      · rw [one_mul]
    obtain ⟨w, hw⟩ := (Int.modEq_iff_dvd.1 (hmod.symm.trans hc))
    refine ⟨-w, ?_⟩
    rw [hsum]
    have : s * (ent Bs i (P u) : ℤ) = ∑ j ∈ Finset.range 4371, (Q j : ℤ) * (ent Bs j u : ℤ) -
        256 * w := by
      linarith
    rw [this]
    ring

theorem stMono_sound {Bs : List (List Nat)} {Ms : List Nat} {T NM : Nat} {R : Nat → Nat}
    (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK (nat_lit 4371) j (recOf Bs j) = true)
    (hs : shifts16 dyDs = true) (hal : allAligned Ms = true) (hn : netOK Ms T NM = true)
    (hv : netV Ms T = true)
    {i : Nat} (hi : i < 4371) (h : stOK Bs (monoF Bs Ms NM) R i = true)
    (hR : Nat.blt (R i) dyFail = true) :
    RowStab Bs (kNumMono T) (R i) i := by
  have hRi : dyElim (2 ^ 8) Bs 0 (monoF Bs Ms NM i) = R i := Nat.eq_of_beq_eq_true h
  have hne : dyElim (2 ^ 8) Bs 0 (monoF Bs Ms NM i) ≠ dyFail := by
    intro e
    rw [e] at hRi
    rw [← hRi] at hR
    exact absurd (Nat.le_of_ble_eq_true hR) (Nat.not_succ_le_self _)
  obtain ⟨Q, hQo, hrow⟩ := mono_row hB hr hs hal hn hv hi hne
  rw [hRi] at hQo
  refine ⟨fun j => (Q j : ℤ), fun j _ => ?_, hrow⟩
  simp only
  rw [hQo]
  split <;> rename_i hq <;> simp only [decide_eq_true_eq] at hq <;> omega

theorem nthN_eq : ∀ (L : List Nat) (i : Nat), nthN L i = L.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    change nthN L i = _
    rw [nthN_eq L i, List.getD_cons_succ]

theorem takeN_eq : ∀ (k : Nat) (L : List Nat), takeN k L = L.take k
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: L => by
    change x :: takeN k L = _
    rw [takeN_eq k L, List.take_succ_cons]

theorem dropN_eq : ∀ (k : Nat) (L : List Nat), dropN k L = L.drop k
  | 0, _ => rfl
  | k + 1, [] => by
    change dropN k [] = _
    rw [dropN_eq k []]
    simp
  | k + 1, x :: L => by
    change dropN k L = _
    rw [dropN_eq k L, List.drop_succ_cons]

theorem allAligned_mem : ∀ {L : List Nat}, allAligned L = true → ∀ M ∈ L, alignedM M = true
  | [], _, M, hM => absurd hM (by simp)
  | x :: L, h, M, hM => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hM with rfl | hM
    · exact h1
    · exact allAligned_mem h2 M hM

theorem allAligned_of : ∀ {L : List Nat}, (∀ M ∈ L, alignedM M = true) → allAligned L = true
  | [], _ => rfl
  | x :: L, h => by
    change andB (alignedM x) (allAligned L) = true
    rw [h x (by simp), allAligned_of (fun M hM => h M (List.mem_cons_of_mem _ hM))]
    rfl

theorem allAlignedL_mem : ∀ {Cs : List (List Nat)}, allAlignedL Cs = true →
    ∀ C ∈ Cs, allAligned C = true
  | [], _, C, hC => absurd hC (by simp)
  | x :: L, h, C, hC => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hC with rfl | hC
    · exact h1
    · exact allAlignedL_mem h2 C hC

theorem selDisj_mem : ∀ {Cs : List (List Nat)}, selDisj Cs = true →
    ∀ C ∈ Cs, pairDisj (takeN 6 C) = true
  | [], _, C, hC => absurd hC (by simp)
  | x :: L, h, C, hC => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hC with rfl | hC
    · exact h1
    · exact selDisj_mem h2 C hC

theorem colV_mem : ∀ {Cs : List (List Nat)}, colV Cs = true →
    ∀ C ∈ Cs, stagesOK (dropN 6 C) dyDs = true
  | [], _, C, hC => absurd hC (by simp)
  | x :: L, h, C, hC => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hC with rfl | hC
    · exact h1
    · exact colV_mem h2 C hC

theorem disjFrom_mem : ∀ {x : Nat} {L : List Nat}, disjFrom x L = true → ∀ y ∈ L, x &&& y = 0
  | _, [], _, y, hy => absurd hy (by simp)
  | x, z :: L, h, y, hy => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Nat.eq_of_beq_eq_true h1
    · exact disjFrom_mem h2 y hy

theorem pairDisj_getD : ∀ {L : List Nat}, pairDisj L = true →
    ∀ a b, a < b → L.getD a 0 &&& L.getD b 0 = 0
  | [], _, a, b, _ => by simp
  | x :: L, h, a, b, hab => by
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rcases a with _ | a
    · rw [List.getD_cons_zero, List.getD_cons_succ]
      by_cases hb : b < L.length
      · rw [getD_lt _ _ hb]
        exact disjFrom_mem h1 _ (List.getElem_mem hb)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        simp
    · rw [List.getD_cons_succ, List.getD_cons_succ]
      exact pairDisj_getD h2 a b (by omega)

theorem alignedM_zero : alignedM 0 = true := by decide +kernel

theorem nthN_aligned {C : List Nat} (hal : allAligned C = true) (k : Nat) :
    alignedM (nthN C k) = true := by
  rw [nthN_eq]
  by_cases hk : k < C.length
  · rw [getD_lt _ _ hk]
    exact allAligned_mem hal _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact alignedM_zero

theorem fld_alignedM {M : Nat} (h : alignedM M = true) (f : Nat) :
    fld M f = 0 ∨ fld M f = 65535 :=
  fld_aligned (Nat.eq_of_beq_eq_true h) f

@[expose] def fs (S f : Nat) : Nat := if fld S f = 65535 then 1 else 0

theorem fs_le (S f : Nat) : fs S f ≤ 1 := by
  unfold fs
  split <;> omega

theorem fld_land_sel {S z : Nat} (hS : alignedM S = true) (f : Nat) :
    fld (z &&& S) f = fs S f * fld z f := by
  rw [fld_land, fs]
  rcases fld_alignedM hS f with h | h
  · rw [h, Nat.and_zero, ite_eq_right (by decide), Nat.zero_mul]
  · rw [h, ite_eq_left rfl, Nat.one_mul, show (65535 : Nat) = 2 ^ 16 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (fld_lt z f)]

theorem fld_oneF {S : Nat} (hS : alignedM S = true) (f : Nat) :
    fld (oneF S) f = if f < 4371 then fs S f else 0 := by
  change fld (S &&& rep 1 16 4371) f = _
  rw [fld_land, fld_rep (by decide)]
  unfold fs
  by_cases hf : f < 4371
  · rw [ite_eq_left hf, ite_eq_left hf]
    rcases fld_alignedM hS f with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  · rw [ite_eq_right hf, ite_eq_right hf, Nat.and_zero]

theorem nth_take {C : List Nat} {a : Nat} (ha : a < 6) : (takeN 6 C).getD a 0 = nthN C a := by
  rw [takeN_eq, nthN_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, ite_eq_left ha]

theorem fs_disj {C : List Nat} (hal : allAligned C = true) (hd : pairDisj (takeN 6 C) = true)
    {a b : Nat} (hab : a < b) (hb : b < 6) (f : Nat) : fs (nthN C a) f + fs (nthN C b) f ≤ 1 := by
  have e := pairDisj_getD hd a b hab
  rw [nth_take (by omega), nth_take hb] at e
  have e2 := congrArg (fun x => fld x f) e
  try simp only at e2
  rw [fld_land, show fld 0 f = 0 by simp [fld]] at e2
  unfold fs
  rcases fld_alignedM (nthN_aligned hal a) f with h1 | h1
  · rw [h1, ite_eq_right (show ¬ ((0 : Nat) = 65535) by decide)]
    split <;> omega
  · rcases fld_alignedM (nthN_aligned hal b) f with h2 | h2
    · rw [h2, ite_eq_right (show ¬ ((0 : Nat) = 65535) by decide)]
      split <;> omega
    · rw [h1, h2] at e2
      exact absurd e2 (by decide)

theorem fld_add2 {a b X Y : Nat} (ha : ∀ t, fld a t ≤ X) (hb : ∀ t, fld b t ≤ Y)
    (h : X + Y < 65536) (t : Nat) : fld (a + b) t = fld a t + fld b t :=
  fld_add t (fun t => by
    have := ha t
    have := hb t
    omega)

theorem fld_add6 {a0 a1 a2 b3 b4 b5 : Nat} (h0 : ∀ t, fld a0 t ≤ 2048)
    (h1 : ∀ t, fld a1 t ≤ 2048) (h2 : ∀ t, fld a2 t ≤ 2048) (h3 : ∀ t, fld b3 t ≤ 2048)
    (h4 : ∀ t, fld b4 t ≤ 2048) (h5 : ∀ t, fld b5 t ≤ 2048) (t : Nat) :
    fld (a0 + a1 + a2 + (b3 + b4 + b5)) t =
      fld a0 t + fld a1 t + fld a2 t + (fld b3 t + fld b4 t + fld b5 t) := by
  have e01 := fld_add2 h0 h1 (by decide)
  have e012 := fld_add2 (X := 4096) (fun t => by
    rw [e01]
    have := h0 t
    have := h1 t
    omega) h2 (by decide)
  have e34 := fld_add2 h3 h4 (by decide)
  have e345 := fld_add2 (X := 4096) (fun t => by
    rw [e34]
    have := h3 t
    have := h4 t
    omega) h5 (by decide)
  rw [fld_add2 (X := 6144) (Y := 6144) (fun t => by
    rw [e012, e01]
    have := h0 t
    have := h1 t
    have := h2 t
    omega) (fun t => by
    rw [e345, e34]
    have := h3 t
    have := h4 t
    have := h5 t
    omega) (by decide), e012, e01, e345, e34]

@[expose] noncomputable def yC (C : List Nat) (z : Nat) : Nat :=
  2 * (z &&& nthN C 0) + 4 * (z &&& nthN C 1) + 8 * (z &&& nthN C 2) +
    ((2048 * oneF (nthN C 3) - 2 * (z &&& nthN C 3)) +
      (2048 * oneF (nthN C 4) - 4 * (z &&& nthN C 4)) +
      (2048 * oneF (nthN C 5) - 8 * (z &&& nthN C 5)))

@[expose] noncomputable def aC (C : List Nat) (f : Nat) : ℤ :=
  2 * (fs (nthN C 0) f : ℤ) + 4 * (fs (nthN C 1) f : ℤ) + 8 * (fs (nthN C 2) f : ℤ) -
    2 * (fs (nthN C 3) f : ℤ) - 4 * (fs (nthN C 4) f : ℤ) - 8 * (fs (nthN C 5) f : ℤ)

theorem colorStep_eq (C : List Nat) (z : Nat) :
    colorStep C dyDs z = benes (dropN 6 C) dyDs (yC C z) := rfl

theorem yC_fld {C : List Nat} (hal : allAligned C = true) (hd : pairDisj (takeN 6 C) = true)
    {z : Nat} (hz : ∀ f, fld z f ≤ 128) (hz0 : ∀ f, 4371 ≤ f → fld z f = 0) (f : Nat) :
    fld (yC C z) f ≤ 2048 ∧ (fld (yC C z) f : ℤ) ≡ aC C f * (fld z f : ℤ) [ZMOD 2048] := by
  have hA : ∀ k, alignedM (nthN C k) = true := nthN_aligned hal
  have hp : ∀ k t, fld (z &&& nthN C k) t = fs (nthN C k) t * fld z t :=
    fun k t => fld_land_sel (hA k) t
  have hpl : ∀ k t, fld (z &&& nthN C k) t ≤ 128 := fun k t => by
    rw [fld_land]
    exact le_trans Nat.and_le_left (hz t)
  have hol : ∀ k t, fld (oneF (nthN C k)) t ≤ 1 := fun k t => by
    rw [fld_oneF (hA k)]
    have := fs_le (nthN C k) t
    split <;> omega
  have hm : ∀ c, c ≤ 8 → ∀ k t, fld (c * (z &&& nthN C k)) t = c * fld (z &&& nthN C k) t :=
    fun c hc k t => fld_mul t (fun t => by
      have := Nat.mul_le_mul hc (hpl k t)
      omega)
  have ho : ∀ k t, fld (2048 * oneF (nthN C k)) t = 2048 * fld (oneF (nthN C k)) t :=
    fun k t => fld_mul t (fun t => by
      have := hol k t
      omega)
  have hle : ∀ c, c ≤ 8 → ∀ k t, c * fld (z &&& nthN C k) t ≤ 2048 * fld (oneF (nthN C k)) t := by
    intro c hc k t
    rw [fld_oneF (hA k), hp]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (fs_le (nthN C k) t) with h | h <;> rw [h]
    · simp
    · split
      · rw [Nat.one_mul]
        have := Nat.mul_le_mul hc (hz t)
        omega
      · rw [hz0 t (by omega)]
        simp
  have hs : ∀ c, c ≤ 8 → ∀ k t, fld (2048 * oneF (nthN C k) - c * (z &&& nthN C k)) t =
      2048 * fld (oneF (nthN C k)) t - c * fld (z &&& nthN C k) t := by
    intro c hc k t
    rw [fld_sub t (fun t => by rw [ho, hm c hc]; exact hle c hc k t), ho, hm c hc]
  have bA : ∀ c, c ≤ 8 → ∀ k t, fld (c * (z &&& nthN C k)) t ≤ 2048 := fun c hc k t => by
    rw [hm c hc]
    have := Nat.mul_le_mul hc (hpl k t)
    omega
  have bB : ∀ c, c ≤ 8 → ∀ k t,
      fld (2048 * oneF (nthN C k) - c * (z &&& nthN C k)) t ≤ 2048 := fun c hc k t => by
    rw [hs c hc]
    have := hol k t
    omega
  have hpe : ∀ k, fld (z &&& nthN C k) f ≤ 128 * fs (nthN C k) f := fun k => by
    rw [hp]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (fs_le (nthN C k) f) with h | h <;> rw [h]
    · simp
    · have := hz f
      omega
  have hoe : ∀ k, fld (oneF (nthN C k)) f ≤ fs (nthN C k) f := fun k => by
    rw [fld_oneF (hA k)]
    split <;> omega
  unfold yC
  rw [fld_add6 (bA 2 (by decide) 0) (bA 4 (by decide) 1) (bA 8 le_rfl 2) (bB 2 (by decide) 3)
    (bB 4 (by decide) 4) (bB 8 le_rfl 5), hm 2 (by decide) 0 f, hm 4 (by decide) 1 f,
    hm 8 le_rfl 2 f, hs 2 (by decide) 3 f, hs 4 (by decide) 4 f, hs 8 le_rfl 5 f]
  have l3 := hle 2 (by decide) 3 f
  have l4 := hle 4 (by decide) 4 f
  have l5 := hle 8 le_rfl 5 f
  constructor
  · have := hpe 0
    have := hpe 1
    have := hpe 2
    have := hpe 3
    have := hpe 4
    have := hpe 5
    have := hoe 3
    have := hoe 4
    have := hoe 5
    have := fs_disj hal hd (a := 0) (b := 1) (by decide) (by decide) f
    have := fs_disj hal hd (a := 0) (b := 2) (by decide) (by decide) f
    have := fs_disj hal hd (a := 0) (b := 3) (by decide) (by decide) f
    have := fs_disj hal hd (a := 0) (b := 4) (by decide) (by decide) f
    have := fs_disj hal hd (a := 0) (b := 5) (by decide) (by decide) f
    have := fs_disj hal hd (a := 1) (b := 2) (by decide) (by decide) f
    have := fs_disj hal hd (a := 1) (b := 3) (by decide) (by decide) f
    have := fs_disj hal hd (a := 1) (b := 4) (by decide) (by decide) f
    have := fs_disj hal hd (a := 1) (b := 5) (by decide) (by decide) f
    have := fs_disj hal hd (a := 2) (b := 3) (by decide) (by decide) f
    have := fs_disj hal hd (a := 2) (b := 4) (by decide) (by decide) f
    have := fs_disj hal hd (a := 2) (b := 5) (by decide) (by decide) f
    have := fs_disj hal hd (a := 3) (b := 4) (by decide) (by decide) f
    have := fs_disj hal hd (a := 3) (b := 5) (by decide) (by decide) f
    have := fs_disj hal hd (a := 4) (b := 5) (by decide) (by decide) f
    omega
  · have hy : ((2 * fld (z &&& nthN C 0) f + 4 * fld (z &&& nthN C 1) f +
        8 * fld (z &&& nthN C 2) f +
        ((2048 * fld (oneF (nthN C 3)) f - 2 * fld (z &&& nthN C 3) f) +
          (2048 * fld (oneF (nthN C 4)) f - 4 * fld (z &&& nthN C 4) f) +
          (2048 * fld (oneF (nthN C 5)) f - 8 * fld (z &&& nthN C 5) f)) : ℕ) : ℤ) =
        2 * (fld (z &&& nthN C 0) f : ℤ) + 4 * (fld (z &&& nthN C 1) f : ℤ) +
          8 * (fld (z &&& nthN C 2) f : ℤ) - 2 * (fld (z &&& nthN C 3) f : ℤ) -
          4 * (fld (z &&& nthN C 4) f : ℤ) - 8 * (fld (z &&& nthN C 5) f : ℤ) +
          2048 * ((fld (oneF (nthN C 3)) f : ℤ) + (fld (oneF (nthN C 4)) f : ℤ) +
            (fld (oneF (nthN C 5)) f : ℤ)) := by
      omega
    rw [hy, hp 0, hp 1, hp 2, hp 3, hp 4, hp 5]
    refine Int.modEq_iff_dvd.2 ⟨-((fld (oneF (nthN C 3)) f : ℤ) + (fld (oneF (nthN C 4)) f : ℤ) +
      (fld (oneF (nthN C 5)) f : ℤ)), ?_⟩
    unfold aC
    push_cast
    ring

theorem class_fld {C : List Nat} (hs : shifts16 dyDs = true) (hal : allAligned C = true)
    (hst : stagesOK (dropN 6 C) dyDs = true) :
    ∃ P : Nat → Nat, ∀ z u, fld (colorStep C dyDs z) u = fld (yC C z) (P u) := by
  have had : allAligned (dropN 6 C) = true := by
    rw [dropN_eq]
    exact allAligned_of (fun M hM => allAligned_mem hal M (List.mem_of_mem_drop hM))
  obtain ⟨P, -, hP, -⟩ := benes_fld (dropN 6 C) dyDs had hs hst
  exact ⟨P, fun z u => by rw [colorStep_eq, hP]⟩

theorem fld_unit (t f : Nat) :
    fld (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t)) f = if f = t then 1 else 0 := by
  change fld (1 <<< (16 * t)) f = _
  rw [fld_shl16, fld_small (by decide)]
  by_cases h1 : f < t
  · rw [ite_eq_left h1, ite_eq_right (by omega)]
  · rw [ite_eq_right h1]
    by_cases h2 : f = t
    · rw [ite_eq_left (by omega), ite_eq_left h2]
    · rw [ite_eq_right (by omega), ite_eq_right h2]

theorem modEq_sum {s : Finset ℕ} {n : ℤ} {g g' : ℕ → ℤ} (h : ∀ i ∈ s, g i ≡ g' i [ZMOD n]) :
    ∑ i ∈ s, g i ≡ ∑ i ∈ s, g' i [ZMOD n] := by
  unfold Int.ModEq
  rw [Finset.sum_int_mod, Finset.sum_congr rfl (fun i hi => h i hi), ← Finset.sum_int_mod]

theorem class_lin {C : List Nat} (hs : shifts16 dyDs = true) (hal : allAligned C = true)
    (hd : pairDisj (takeN 6 C) = true) (hst : stagesOK (dropN 6 C) dyDs = true) {x : Nat}
    (hx : ∀ f, fld x f ≤ 128) (hx0 : ∀ f, 4371 ≤ f → fld x f = 0) (u : Nat) :
    (fld (colorStep C dyDs x) u : ℤ) ≡ ∑ t ∈ Finset.range 4371, (fld x t : ℤ) *
      (fld (colorStep C dyDs (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t))) u : ℤ)
      [ZMOD 2048] := by
  obtain ⟨P, hP⟩ := class_fld hs hal hst
  rw [hP]
  have hu : ∀ t ∈ Finset.range 4371, (fld x t : ℤ) *
      (fld (colorStep C dyDs (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t))) u : ℤ) ≡
        if P u = t then (fld x t : ℤ) * aC C (P u) else 0 [ZMOD 2048] := by
    intro t ht
    rw [hP]
    have hm := Finset.mem_range.1 ht
    have h1 := (yC_fld hal hd (z := Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t))
      (fun f => by rw [fld_unit]; split <;> omega)
      (fun f hf => by rw [fld_unit, ite_eq_right (by omega)]) (P u)).2
    rw [fld_unit] at h1
    refine (h1.mul_left _).trans ?_
    split_ifs with he
    · simp
    · simp
  refine ((yC_fld hal hd hx hx0 (P u)).2).trans (Int.ModEq.trans ?_ (modEq_sum hu).symm)
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · simp [mul_comm]
  · rw [hx0 _ (by simpa using hm)]
    simp

@[expose] noncomputable def imgAcc (Cs : List (List Nat)) (Ds : List Nat) (x : Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun C _ ih acc => forceB (Nat.add acc (colorStep C Ds x)) (fun a => ih a)) Cs

theorem imgAcc_eq (Ds : List Nat) (x : Nat) : ∀ (Cs : List (List Nat)) (acc : Nat),
    imgAcc Cs Ds x acc = acc + (Cs.map (fun C => colorStep C Ds x)).sum
  | [], acc => rfl
  | C :: Cs, acc => by
    change forceB (Nat.add acc (colorStep C Ds x)) (fun a => imgAcc Cs Ds x a) = _
    rw [forceB_apply, imgAcc_eq Ds x Cs, List.map_cons, List.sum_cons]
    change acc + colorStep C Ds x + _ = _
    rw [Nat.add_assoc]

theorem colorImg_eq (Cs : List (List Nat)) (Ds : List Nat) (x : Nat) :
    colorImg Cs Ds x = (Cs.map (fun C => colorStep C Ds x)).sum := by
  change imgAcc Cs Ds x 0 = _
  rw [imgAcc_eq, Nat.zero_add]

theorem fld_sum_map {g : List Nat → Nat} : ∀ (L : List (List Nat)),
    (∀ C ∈ L, ∀ t, fld (g C) t ≤ 2048) → L.length ≤ 16 → ∀ t,
      fld (L.map g).sum t = (L.map (fun C => fld (g C) t)).sum ∧
        (L.map (fun C => fld (g C) t)).sum ≤ 2048 * L.length
  | [], _, _, t => by simp [fld]
  | C :: L, hg, hl, t => by
    have ih := fld_sum_map L (fun C' hC' => hg C' (List.mem_cons_of_mem _ hC'))
      (by simp at hl; omega)
    have hC := hg C (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [fld_add t (fun t' => by
      have := hC t'
      have := (ih t').1
      have := (ih t').2
      simp at hl
      have : 2048 * L.length ≤ 2048 * 15 := Nat.mul_le_mul_left _ (by omega)
      omega), (ih t).1]
    have := hC t
    have := (ih t).2
    constructor
    · rfl
    · rw [Nat.mul_succ]
      omega

theorem sum_list_lin : ∀ (L : List (List Nat)) {x : Nat} {F : List Nat → Nat → Nat}
    {G : List Nat → Nat → Nat → Nat},
    (∀ C ∈ L, ∀ u, (F C u : ℤ) ≡ ∑ t ∈ Finset.range 4371, (fld x t : ℤ) * (G C t u : ℤ)
      [ZMOD 2048]) → ∀ u,
    ((L.map (fun C => F C u)).sum : ℤ) ≡
      ∑ t ∈ Finset.range 4371, (fld x t : ℤ) * ((L.map (fun C => G C t u)).sum : ℤ) [ZMOD 2048]
  | [], _, _, _, _, u => by simp
  | C :: L, x, F, G, h, u => by
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    exact (h C (by simp) u).add
      (sum_list_lin L (fun C' hC' u' => h C' (List.mem_cons_of_mem _ hC') u') u)

@[expose] noncomputable def rowsRec (Cs : List (List Nat)) (Ds : List Nat) :
    List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ ok => ok)
    (fun r _ ih j ok => forceB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) ok
        (Nat.beq (Nat.land (colorImg Cs Ds (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) j)))
          (rep (nat_lit 2047) (nat_lit 16) (nat_lit 4371))) r))
      (fun ok' => forceB (Nat.succ j) (fun j' => ih j' ok')))

theorem rowsRec_zero (Cs : List (List Nat)) (Ds : List Nat) :
    ∀ (L : List Nat) (j : Nat), rowsRec Cs Ds L j 0 = 0
  | [], _ => rfl
  | r :: L, j => by
    change forceB (Bool.rec (motive := fun _ => Nat) 0 0
        (Nat.beq (Nat.land (colorImg Cs Ds (Nat.shiftLeft 1 (Nat.mul 16 j)))
          (rep 2047 16 4371)) r))
      (fun ok' => forceB (Nat.succ j) (fun j' => rowsRec Cs Ds L j' ok')) = 0
    rw [forceB_apply, forceB_apply]
    cases Nat.beq (Nat.land (colorImg Cs Ds (Nat.shiftLeft 1 (Nat.mul 16 j)))
      (rep 2047 16 4371)) r <;> exact rowsRec_zero Cs Ds L _

theorem rowsRec_sound (Cs : List (List Nat)) (Ds : List Nat) : ∀ (L : List Nat) (j ok : Nat),
    0 < rowsRec Cs Ds L j ok → ∀ idx < L.length,
      colorImg Cs Ds (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) (j + idx))) &&&
        rep 2047 16 4371 = L.getD idx 0
  | [], _, _, _, idx, h => absurd h (Nat.not_lt_zero _)
  | r :: L, j, ok, h, idx, hidx => by
    change 0 < forceB (Bool.rec (motive := fun _ => Nat) 0 ok
        (Nat.beq (Nat.land (colorImg Cs Ds (Nat.shiftLeft 1 (Nat.mul 16 j)))
          (rep 2047 16 4371)) r))
      (fun ok' => forceB (Nat.succ j) (fun j' => rowsRec Cs Ds L j' ok')) at h
    rw [forceB_apply, forceB_apply] at h
    cases hb : Nat.beq (Nat.land (colorImg Cs Ds (Nat.shiftLeft 1 (Nat.mul 16 j)))
      (rep 2047 16 4371)) r
    · rw [hb, rowsRec_zero] at h
      exact absurd h (Nat.lt_irrefl 0)
    · rw [hb] at h
      rcases idx with _ | idx
      · rw [List.getD_cons_zero]
        exact Nat.eq_of_beq_eq_true hb
      · rw [List.getD_cons_succ, show j + (idx + 1) = Nat.succ j + idx by omega]
        exact rowsRec_sound Cs Ds L (Nat.succ j) ok h idx (by simp at hidx; omega)

theorem blocks_len {Bs : List (List Nat)} (hB : blocksOK Bs = true) :
    ∀ s < 69, (Bs.getD s []).length = rowsSn 4371 s := by
  obtain ⟨-, h2⟩ := andB_true hB
  generalize hn : nat_lit 69 = n at h2
  intro s hs
  have := Nat.eq_of_beq_eq_true (recAnd_sound h2 s (hn ▸ hs))
  rwa [dyLenL_eq, dyLgetL_eq] at this

theorem rowsSn_68 : rowsSn 4371 68 = 19 := by decide

theorem sg_rows {Cs SG : List (List Nat)} (hSG : blocksOK SG = true)
    (hc : ∀ m < 274, colorRowsL Cs dyDs (64 * (m / 4) + 16 * (m % 4))
      (takeN 16 (dropN (16 * (m % 4)) (lgetL SG (m / 4)))) = true) {t : Nat} (ht : t < 4371) :
    colorImg Cs dyDs (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t)) &&&
      rep 2047 16 4371 = recOf SG t := by
  have h0 : 0 < rowsRec Cs dyDs (takeN 16 (dropN (16 * (t / 16 % 4)) (lgetL SG (t / 16 / 4))))
      (64 * (t / 16 / 4) + 16 * (t / 16 % 4)) 1 :=
    Nat.le_of_ble_eq_true (hc (t / 16) (by omega))
  have hlen := blocks_len hSG (t / 64) (by omega)
  have hrow : t % 64 < rowsSn 4371 (t / 64) := by
    by_cases h68 : t / 64 < 68
    · rw [rowsSn_64 _ h68]
      omega
    · rw [show t / 64 = 68 by omega, rowsSn_68]
      omega
  have e1 : t / 16 / 4 = t / 64 := by omega
  have e2 : 16 * (t / 16 % 4) + t % 16 = t % 64 := by omega
  rw [takeN_eq, dropN_eq, dyLgetL_eq, e1] at h0
  have := rowsRec_sound Cs dyDs _ _ 1 h0 (t % 16) (by
    rw [List.length_take, List.length_drop, hlen]
    omega)
  rw [show 64 * (t / 64) + 16 * (t / 16 % 4) + t % 16 = t by omega] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
    List.getElem?_drop, e2, dyRecOf_eq, List.getD_eq_getElem?_getD]
  exact List.getD_eq_getElem?_getD.symm

theorem fld_shr3 {w : Nat} (h : ∀ f, fld w f % 8 = 0) (f : Nat) :
    fld (w >>> 3) f = fld w f / 8 := by
  have h1 := h (f + 1)
  rw [fld_succ] at h1
  unfold fld at h1 ⊢
  have e1 : w >>> 3 / 2 ^ (16 * f) = w / 2 ^ (16 * f) / 8 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have e2 : w / 65536 / 2 ^ (16 * f) = w / 2 ^ (16 * f) / 65536 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [e1]
  rw [e2] at h1
  generalize w / 2 ^ (16 * f) = W at h1 ⊢
  omega

theorem stSparse_sound {Bs Cs SG : List (List Nat)} {R : Nat → Nat}
    (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK (nat_lit 4371) j (recOf Bs j) = true)
    (hs : shifts16 dyDs = true) (hal : allAlignedL Cs = true) (hd : selDisj Cs = true)
    (hcv : colV Cs = true)
    (hnc : Nat.beq (lenLL Cs) (nat_lit 16) = true) (hSG : blocksOK SG = true)
    (hc : ∀ m < 274, colorRowsL Cs dyDs (64 * (m / 4) + 16 * (m % 4))
      (takeN 16 (dropN (16 * (m % 4)) (lgetL SG (m / 4)))) = true)
    {i : Nat} (hi : i < 4371) (h : stOK Bs (colF Bs Cs) R i = true)
    (hR : Nat.blt (R i) dyFail = true)
    (hR0 : Nat.beq (R i) (dyElim (nat_lit 256) Bs (nat_lit 0) dyFail) = false) :
    RowStab Bs (kNumSparse SG) (R i) i := by
  have hcl : ∀ C ∈ Cs, allAligned C = true ∧ pairDisj (takeN 6 C) = true ∧
      stagesOK (dropN 6 C) dyDs = true :=
    fun C hC => ⟨allAlignedL_mem hal C hC, selDisj_mem hd C hC, colV_mem hcv C hC⟩
  have hlen : Cs.length = 16 := by
    rw [← dyLenLL_eq]
    exact Nat.eq_of_beq_eq_true hnc
  have himg : ∀ z, (∀ f, fld z f ≤ 128) → (∀ f, 4371 ≤ f → fld z f = 0) → ∀ u,
      fld (colorImg Cs dyDs z) u = (Cs.map (fun C => fld (colorStep C dyDs z) u)).sum := by
    intro z hz hz0 u
    rw [colorImg_eq]
    refine (fld_sum_map (g := fun C => colorStep C dyDs z) Cs (fun C hC t => ?_)
      (by omega) u).1
    obtain ⟨hC1, hC2, hC3⟩ := hcl C hC
    obtain ⟨P, hP⟩ := class_fld hs hC1 hC3
    rw [hP]
    exact (yC_fld hC1 hC2 hz hz0 (P t)).1
  have hunit : ∀ t < 4371,
      (∀ f, fld (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t)) f ≤ 128) ∧
        ∀ f, 4371 ≤ f → fld (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t)) f = 0 :=
    fun t ht => ⟨fun f => by rw [fld_unit]; split <;> omega,
      fun f hf => by rw [fld_unit, ite_eq_right (by omega)]⟩
  have hN : ∀ t u, t < 4371 → u < 4371 → kNumSparse SG t u ≡
      (fld (colorImg Cs dyDs (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t))) u : ℤ)
        [ZMOD 2048] := by
    intro t u ht hu
    have e : kNumSparse SG t u =
        (fun x : Nat => if 1024 ≤ x then (x : ℤ) - 2048 else (x : ℤ)) (fld (recOf SG t) u) := rfl
    rw [e, ← sg_rows hSG hc ht, fld_land, fld_rep (by decide), ite_eq_left hu,
      show (2047 : Nat) = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only
    unfold Int.ModEq
    split <;> omega
  obtain ⟨⟨e', he', hp⟩, hb, hbf⟩ := dyRowOK_facts (by decide) (hr i hi)
  have hb : recOf Bs i < 2 ^ (16 * (4371 - i)) := hb
  have hent : ∀ c, ent Bs i c ≤ 128 := fun c => by
    unfold ent
    split
    · omega
    · rcases Nat.eq_zero_or_pos (c - i) with h0 | h0
      · rw [h0, hp]
        exact Nat.pow_le_pow_right (by decide) he'
      · exact (hbf _ h0).le
  have hent0 : ∀ c, 4371 ≤ c → ent Bs i c = 0 := fun c hc => by
    unfold ent
    split
    · rfl
    · exact fld_of_lt hb (by omega)
  set x := Nat.shiftLeft (recOf Bs i) (Nat.mul 16 i) with hx
  have hxf : ∀ c, fld x c = ent Bs i c := fun c => by
    rw [hx]
    exact fld_shl16 _ _ _
  have hxl : ∀ f, fld x f ≤ 128 := fun f => by rw [hxf]; exact hent f
  have hx0 : ∀ f, 4371 ≤ f → fld x f = 0 := fun f hf => by rw [hxf]; exact hent0 f hf
  set V := colorImg Cs dyDs x with hV
  set W := V &&& rep 2047 16 4371 with hW
  have hred : colF Bs Cs i = Bool.rec (motive := fun _ => Nat) dyFail (W >>> 3)
      (Nat.beq (W &&& rep 7 16 4371) 0) := rfl
  have hRi : dyElim (2 ^ 8) Bs 0 (colF Bs Cs i) = R i := Nat.eq_of_beq_eq_true h
  cases hok : Nat.beq (W &&& rep 7 16 4371) 0
  · rw [hred, hok] at hRi
    have e1 : R i = dyElim 256 Bs 0 dyFail := hRi.symm
    rw [e1, Nat.beq_refl] at hR0
    exact absurd hR0 (by decide)
  rw [hred, hok] at hRi
  change dyElim (2 ^ 8) Bs 0 (W >>> 3) = R i at hRi
  have hWf : ∀ f, fld W f = if f < 4371 then fld V f % 2048 else 0 := fun f => by
    rw [hW, fld_land, fld_rep (by decide)]
    split
    · rw [show (2047 : Nat) = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    · rw [Nat.and_zero]
  have hW8 : ∀ f, fld W f % 8 = 0 := fun f => by
    have e := congrArg (fun y => fld y f) (Nat.eq_of_beq_eq_true hok)
    try simp only at e
    rw [fld_land, fld_rep (by decide), show fld 0 f = 0 by simp [fld]] at e
    split at e
    · rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at e
      exact e
    · rw [hWf, ite_eq_right (by assumption)]
  have hvf : ∀ f, fld (W >>> 3) f = fld W f / 8 := fld_shr3 hW8
  have hlt : W >>> 3 < 2 ^ (16 * (4371 - 0)) := by
    apply lt_of_fld
    intro t ht
    rw [hvf, hWf, ite_eq_right (by omega)]
  have hf : ∀ t, fld (W >>> 3) t < 2 ^ 8 := fun t => by
    rw [hvf, hWf]
    split
    · have := Nat.mod_lt (fld V t) (show 2048 > 0 by decide)
      change _ < 256
      omega
    · decide
  have hne : dyElim (2 ^ 8) Bs 0 (W >>> 3) ≠ dyFail := by
    intro e
    rw [e] at hRi
    rw [← hRi] at hR
    exact absurd (Nat.le_of_ble_eq_true hR) (Nat.not_succ_le_self _)
  obtain ⟨Q, -, hQo, hres⟩ := dyElim_sound (by decide) hB hr (by decide) hlt hf hne
  rw [hRi] at hQo
  refine ⟨fun j => (Q j : ℤ), fun j _ => ?_, fun u hu => ?_⟩
  · simp only
    rw [hQo]
    split <;> rename_i hq <;> simp only [decide_eq_true_eq] at hq <;> omega
  ·
    have h1 : ∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * kNumSparse SG t u ≡
        ∑ t ∈ Finset.range 4371, (fld x t : ℤ) * ((Cs.map (fun C => fld (colorStep C dyDs
          (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t))) u)).sum : ℤ) [ZMOD 2048] := by
      refine modEq_sum (fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hxf, ← himg _ (hunit t ht').1 (hunit t ht').2]
      exact (hN t u ht' hu).mul_left _
    have h2 := sum_list_lin Cs (x := x) (F := fun C u => fld (colorStep C dyDs x) u)
      (G := fun C t u => fld (colorStep C dyDs
        (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) t))) u)
      (fun C hC u => by
        obtain ⟨hC1, hC2, hC3⟩ := hcl C hC
        exact class_lin hs hC1 hC2 hC3 hxl hx0 u) u
    have hS : ∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * kNumSparse SG t u ≡
        (fld V u : ℤ) [ZMOD 2048] := by
      have e := himg x hxl hx0 u
      rw [← hV] at e
      rw [e]
      exact h1.trans h2.symm
    have h3 := hres u (Nat.zero_le u) hu
    rw [Nat.sub_zero, comb_eq] at h3
    have h3' : (fld (W >>> 3) u : ℤ) % 256 =
        (∑ j ∈ Finset.range 4371, (Q j : ℤ) * (ent Bs j u : ℤ)) % 256 := h3
    have h4 := hWf u
    rw [ite_eq_left hu] at h4
    have h5 := hW8 u
    have h6 := hvf u
    unfold Int.ModEq at hS
    refine ⟨((∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * kNumSparse SG t u) -
      8 * ∑ j ∈ Finset.range 4371, (Q j : ℤ) * (ent Bs j u : ℤ)) / 2048, ?_⟩
    try dsimp only
    generalize (∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * kNumSparse SG t u) = S at hS ⊢
    generalize (∑ j ∈ Finset.range 4371, (Q j : ℤ) * (ent Bs j u : ℤ)) = Cb at h3' ⊢
    omega

end CFSG.KC.BM.Dy

end
