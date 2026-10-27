module

public import CFSG.Certificates.Kernel.FrameE78.Decode
public import CFSG.Certificates.Kernel.OrbRow.Sound
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.FrameE78.Refl Matrix

@[expose] def AlwP (n t d : ℕ) : Prop :=
  (n = 7 ∧ (t = 21 ∧ d = 10 ∨ t = 30 ∧ d = 16 ∨ t = 36 ∧ d = 20)) ∨
    (n = 8 ∧ (t = 36 ∧ d = 14 ∨ t = 42 ∧ d = 20 ∨ t = 63 ∧ d = 32))

@[expose] noncomputable def Rv (n RP : ℕ) (a : ℕ) : Fin n → ZMod 3 := dec n (rc RP a)

private theorem dot3_lt (n u v : ℕ) : dot3 n u v < 3 := by
  rw [dot3_eq]
  exact Nat.mod_lt _ (by decide)

private theorem cast_eq_zero_iff {k : ℕ} (hk : k < 3) : (k : ZMod 3) = 0 ↔ k = 0 := by
  interval_cases k <;> decide

theorem dot3_zero_iff (n u v : ℕ) : dot3 n u v = 0 ↔ dec n u ⬝ᵥ dec n v = 0 := by
  rw [← dot3_cast, cast_eq_zero_iff (dot3_lt n u v)]

theorem rootData_of {n C m RP CL PT : ℕ} (hn : n ≤ 8) (hnm : n ≤ m)
    (h1 : rootOK n C m RP = true) (h2 : simpleOK n RP = true) (h3 : closOK n m RP CL = true)
    (h4 : parOK n m CL PT = true) (h5 : distOK m RP = true) :
    RootData (Cm n C) m (Rv n RP) := by
  have hr := rootOK_sound hn h1
  have hrC : ∀ a < m, dec n (rC RP a) = Cm n C *ᵥ Rv n RP a := fun a ha => by
    rw [(hr a ha).2.1, dec_cvec]
    rfl
  have hcl : ∀ a < m, ∀ i : Fin n, clget CL a i < m ∧
      (sR (Cm n C) i (Rv n RP a) = Rv n RP (clget CL a i) ∨
        sR (Cm n C) i (Rv n RP a) = -Rv n RP (clget CL a i)) := by
    intro a ha i
    obtain ⟨hb, e⟩ := closOK_sound h3 a ha i i.isLt
    have hb' := (hr _ hb).1
    refine ⟨hb, ?_⟩
    have e2 : sR (Cm n C) i (Rv n RP a) = dec n (sRt (rc RP a) (rC RP a) i) := by
      rw [(hr a ha).2.1, dec_sRt]
      rfl
    rw [e2]
    rcases e with e | e
    · exact Or.inl (by rw [e]; rfl)
    · exact Or.inr (by rw [e, dec_negL hn hb'.2]; rfl)
  refine ⟨fun a ha => ?_, fun i => ⟨by omega, ?_⟩, fun a ha i => ?_, fun a ha hna => ?_,
    fun a ha b hb => ?_⟩
  · have e := (hr a ha).2.2
    have e2 : ((dot3 n (rc RP a) (cvec n C (rc RP a)) : ℕ) : ZMod 3) = 2 := by rw [e]; rfl
    rw [dot3_cast, dec_cvec] at e2
    exact e2
  · change dec n (rc RP i) = ev i
    rw [simpleOK_sound h2 i i.isLt, dec_shl_one]
  · obtain ⟨hb, e⟩ := hcl a ha i
    exact ⟨_, hb, e⟩
  · obtain ⟨p, hp, i, hi, e⟩ := parOK_sound h4 a hna ha
    obtain ⟨-, e2⟩ := hcl p (by omega) ⟨i, hi⟩
    rw [e] at e2
    exact ⟨p, hp, ⟨i, hi⟩, e2⟩
  · obtain ⟨e1, e2⟩ := distOK_sound h5 a ha b hb
    have ha' := (hr a ha).1
    have hb' := (hr b (by omega)).1
    refine ⟨fun e => e1 (dec_inj ha' hb' e), fun e => e2 (dec_inj ha' (VOK_negL hn hb') ?_)⟩
    rw [dec_negL hn hb'.2]
    exact e

inductive SReach (n C a : ℕ) : ℕ → Prop
  | root : SReach n C a a
  | step {y : ℕ} (j : Fin n) : SReach n C a y → SReach n C a (sV n C j y)

private theorem sV_negL {n C y : ℕ} (hn : n ≤ 8) (hy : VOK n y) (j : Fin n) :
    sV n C j (negL y) = negL (sV n C j y) :=
  dec_inj (VOK_sV (VOK_negL hn hy)) (VOK_negL hn (VOK_sV hy)) (by
    rw [dec_sV (VOK_negL hn hy).2, dec_negL hn hy.2, dec_negL hn (VOK_sV hy).2, dec_sV hy.2,
      mulVec_neg])

private theorem negL_negL {n y : ℕ} (hn : n ≤ 8) (hy : VOK n y) : negL (negL y) = y :=
  dec_inj (VOK_negL hn (VOK_negL hn hy)) hy (by
    rw [dec_negL hn (VOK_negL hn hy).2, dec_negL hn hy.2, neg_neg])

private theorem ln_zero_nat (q : ℕ) : ln 0 q = 0 := by
  rw [ln_eq, Nat.zero_div]

private theorem VOK_zero_vec (n : ℕ) : VOK n 0 :=
  ⟨Nat.pow_pos (by decide : 0 < 4), fun q _ => by rw [ln_zero_nat]; decide⟩

private theorem normV_lead {n x : ℕ} (hn : n ≤ 8) (hx : VOK n x) (hx0 : x ≠ 0) :
    VOK n (normV n x) ∧ lead n (normV n x) = 1 := by
  rcases lead_spec n x with ⟨-, h0⟩ | ⟨q0, hq0, hl, hne, hbelow⟩
  · exact absurd (VOK_ext hx (VOK_zero_vec n) fun q hq => by rw [h0 q hq, ln_zero_nat]) hx0
  · have hle := hx.2 q0 hq0
    rw [normV_ite]
    by_cases h2 : lead n x = 2
    · rw [if_pos h2]
      refine ⟨VOK_negL hn hx, ?_⟩
      have hneg : ∀ q < n, (ln (negL x) q = 0 ↔ ln x q = 0) := fun q hq => by
        rw [ln_negL (by omega) (hx.2 q hq)]
        have := hx.2 q hq
        omega
      rcases lead_spec n (negL x) with ⟨-, h0⟩ | ⟨q1, hq1, hl1, hne1, hbelow1⟩
      · exact absurd ((hneg q0 hq0).1 (h0 q0 hq0)) hne
      · rcases lt_trichotomy q1 q0 with h | rfl | h
        · exact absurd ((hneg q1 hq1).2 (hbelow q1 h)) hne1
        · rw [hl1, ln_negL (by omega) hle, ← hl, h2]
        · exact absurd ((hneg q0 hq0).1 (hbelow1 q0 h)) hne
    · rw [if_neg h2]
      refine ⟨hx, ?_⟩
      rw [hl] at h2 ⊢
      omega

theorem cover_reach {n C N V k lv : ℕ} {S D bs cs : List ℕ} {RR : List (List ℕ)} (hn : n ≤ 8)
    (hp : ptsOK n N V = true) (hg : ∀ j < n, genJ n C N S V j = true)
    (ht : ∀ t < k, getS bs t < N ∧
      rowsK N 12 4095 S n lv (getS D t) (getS bs t) (getS cs t) (getLs RR t) = true)
    (hc : coverOK N k D = true) {x : ℕ} (hx : VOK n x) (hx0 : x ≠ 0) :
    ∃ t < k, ∃ y, VOK n y ∧ SReach n C (vget V (getS bs t)) y ∧ (x = y ∨ x = negL y) := by
  have hs := (ptsOK_sound hn hp).2
  obtain ⟨hzv, hzl⟩ := normV_lead hn hx hx0
  obtain ⟨p, hpN, hpz⟩ := ptsOK_complete hn hp hzv hzl
  obtain ⟨t, htk, hd⟩ := coverOK_sound hc p hpN
  obtain ⟨hb, hrows⟩ := ht t htk
  have hreach := (rowsK_depth hrows).2 p hpN hd
  have key : ∀ q, OrbReach (fun j y => pg 12 4095 (getS S j) y) (lvOk n lv) (getS bs t) q →
      q < N ∧ ∃ y, VOK n y ∧ SReach n C (vget V (getS bs t)) y ∧
        (vget V q = y ∨ vget V q = negL y) := by
    intro q hq
    induction hq with
    | root => exact ⟨hb, _, (hs _ hb).1, SReach.root, Or.inl rfl⟩
    | @step q j _ hj ih =>
      obtain ⟨hqN, y, hy, hyr, hyq⟩ := ih
      have hjn : j < n := (lvOk_iff.1 hj).1
      obtain ⟨hrN, hr⟩ := genJ_sound (hg j hjn) q hqN
      refine ⟨hrN, sV n C j y, VOK_sV hy, SReach.step ⟨j, hjn⟩ hyr, ?_⟩
      rw [hr]
      have e : sV n C j (vget V q) = sV n C j y ∨ sV n C j (vget V q) = negL (sV n C j y) := by
        rcases hyq with e | e
        · exact Or.inl (by rw [e])
        · exact Or.inr (by rw [e]; exact sV_negL hn hy ⟨j, hjn⟩)
      rcases e with e | e <;> rcases normV_eq n (sV n C j (vget V q)) with f | f <;> rw [f, e]
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (negL_negL hn (VOK_sV hy))
  obtain ⟨-, y, hy, hyr, hyp⟩ := key p hreach
  refine ⟨t, htk, y, hy, hyr, ?_⟩
  rw [hpz] at hyp
  rcases normV_eq n x with e | e <;> rw [e] at hyp
  · exact hyp
  · rcases hyp with f | f
    · right
      rw [← f, negL_negL hn hx]
    · left
      rw [← negL_negL hn hx, f, negL_negL hn hy]

theorem dich_reach {n C a m : ℕ} {R : ℕ → Fin n → ZMod 3} {A : ℕ → ℕ → Prop}
    (hR : RootData (Cm n C) m R) (ha : VOK n a)
    (hd : Dich A (fixSet (Cm n C) (dec n a))) {y : ℕ} (hy : SReach n C a y) :
    VOK n y ∧ Dich A (fixSet (Cm n C) (dec n y)) := by
  induction hy with
  | root => exact ⟨ha, hd⟩
  | @step y j _ ih =>
    refine ⟨VOK_sV ih.1, ?_⟩
    rw [dec_sV ih.1.2, fixSet_smul hR]
    exact dich_image _ ih.2

private theorem exists_bit {P : ℕ} (h : P ≠ 0) : ∃ i, P.testBit i = true := by
  by_contra hc
  push Not at hc
  exact h (Nat.eq_of_testBit_eq fun i => by
    rw [Nat.zero_testBit]
    simpa using hc i)

private theorem bit_lt {Tm m i : ℕ} (hT : Tm < 2 ^ m) (h : Tm.testBit i = true) : i < m := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) (by omega)))]
    at h
  exact Bool.false_ne_true h

theorem dich_rep {n C m RP V b : ℕ} {Q : List ℕ} (hC : (Cm n C).IsSymm) (hn : n ≤ 8)
    (hR : RootData (Cm n C) m (Rv n RP)) (h1 : rootOK n C m RP = true)
    (hrep : repK n m RP V b Q = true) :
    Dich (AlwP n) (fixSet (Cm n C) (dec n (vget V b))) := by
  have hr := rootOK_sound hn h1
  have hbf : ∀ a < m, ∀ c < m, (bf n RP a c = 0 ↔ Refl.bf (Cm n C) (Rv n RP a) (Rv n RP c) = 0) := by
    intro a _ c hc
    change dot3 n (rc RP a) (rC RP c) = 0 ↔ _
    rw [dot3_zero_iff, (hr c hc).2.1, dec_cvec]
    rfl
  obtain ⟨htx, hk⟩ := repK_sound hrep
  obtain ⟨hTm, hT⟩ := txOK_sound htx
  have hT' : ∀ a < m, ((getS Q 0).testBit a = true ↔ Rv n RP a ⬝ᵥ dec n (vget V b) = 0) :=
    fun a ha => (hT a ha).trans (dot3_zero_iff _ _ _)
  rcases hk with ⟨-, hal, hun⟩ | ⟨-, hsp⟩
  · obtain ⟨hcnt, hdeg⟩ := unifK_sound hun
    refine dich_unif hC hR (t := getS Q 2) (d := getS Q 3) ?_ (fun a ha hax => ?_)
      (alwK_sound hal)
    · rw [← hcnt]
      congr 1
      exact Finset.filter_congr fun a ha => (hT' a (Finset.mem_range.1 ha)).symm
    · rw [← hdeg a ha ((hT' a ha).2 hax)]
      congr 1
      refine Finset.filter_congr fun c hc => ?_
      have hc' := Finset.mem_range.1 hc
      rw [hT' c hc']
      simp only [ne_eq]
      rw [hbf a ha c hc']
  · obtain ⟨hsub, hP0, hPT, hPQ⟩ := splitK_sound hsp
    refine dich_split hC hR (fun a => (getS Q 2).testBit a = true) ?_ ?_ ?_
    · obtain ⟨i, hi⟩ := exists_bit hP0
      have hiT := hsub i hi
      have him := bit_lt hTm hiT
      exact ⟨i, him, (hT' i him).1 hiT, hi⟩
    · have hne : ∃ i, (getS Q 0).testBit i = true ∧ (getS Q 2).testBit i = false := by
        by_contra hc
        push Not at hc
        refine hPT (Nat.eq_of_testBit_eq fun i => ?_)
        cases hq : (getS Q 2).testBit i
        · cases hq2 : (getS Q 0).testBit i
          · rfl
          · exact absurd hq (hc i hq2)
        · exact (hsub i hq).symm
      obtain ⟨i, hiT, hiP⟩ := hne
      have him := bit_lt hTm hiT
      exact ⟨i, him, (hT' i him).1 hiT, by rw [hiP]; exact Bool.false_ne_true⟩
    · intro a ha c hc _ hcx hPa hPc
      exact (hbf a ha c hc).1 (hPQ a ha c hc hPa ((hT' c hc).2 hcx)
        (Bool.eq_false_iff.2 hPc))

theorem frame_facts {n C N V k lv m RP CL PT : ℕ} {S D bs cs : List ℕ} {RR Q : List (List ℕ)}
    (hn : n ≤ 8) (hnm : n ≤ m) (hC : (Cm n C).IsSymm)
    (h1 : rootOK n C m RP = true) (h2 : simpleOK n RP = true) (h3 : closOK n m RP CL = true)
    (h4 : parOK n m CL PT = true) (h5 : distOK m RP = true)
    (hp : ptsOK n N V = true) (hg : ∀ j < n, genJ n C N S V j = true)
    (ht : ∀ t < k, getS bs t < N ∧
      rowsK N 12 4095 S n lv (getS D t) (getS bs t) (getS cs t) (getLs RR t) = true)
    (hc : coverOK N k D = true) (hrep : ∀ t < k, repK n m RP V (getS bs t) (getLs Q t) = true) :
    (∀ r t, ConjDer (sS (Cm n C)) r → ConjDer (sS (Cm n C)) t →
      r = t ∨ r * t = t * r ∨ r * t * r = t * r * t) ∧
    ∀ x : Fin n → ZMod 3, x ≠ 0 → Dich (AlwP n) (fixSet (Cm n C) x) := by
  have hR := rootData_of hn hnm h1 h2 h3 h4 h5
  refine ⟨fun r t hr ht' => conjDer_braid hC hR hr ht', fun x hx => ?_⟩
  have hX := VOK_enc n x
  have hX0 : enc n x ≠ 0 := fun e => hx (by
    rw [← dec_enc n x, e]
    funext q
    rw [dec_apply, ln_zero_nat, Nat.cast_zero]
    rfl)
  obtain ⟨t, htk, y, hy, hyr, hxy⟩ := cover_reach hn hp hg ht hc hX hX0
  have hb := (ht t htk).1
  have hd0 := dich_rep hC hn hR h1 (hrep t htk)
  have hvb := ((ptsOK_sound hn hp).2 _ hb).1
  obtain ⟨-, hdy⟩ := dich_reach hR hvb hd0 hyr
  rw [← dec_enc n x]
  rcases hxy with e | e
  · rw [e]
    exact hdy
  · rw [e, dec_negL hn hy.2, fixSet_neg]
    exact hdy

end CFSG.KC.FrameE78

end
