module

public import CFSG.Certificates.Kernel.Fi22Rk.Side
public import CFSG.Sporadic.FischerOddCore.ClosureSearchSpec
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KC.Fi22RkS

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.Sporadic.FischerOddCore.SearchSpec (forIn_range_yield)

abbrev St := Array (Array Nat) × Array Nat × Array Nat × Nat

abbrev St3 := Array (Array Nat) × Array Nat × Array Nat

@[expose] def iStep (mus : Array (Array Nat)) (q : Nat) : Nat → St3 → Id (ForInStep St3) :=
  fun l __s =>
    have L := __s.fst
    have __s := __s.snd
    have par := __s.fst
    have lab := __s.snd
    have x := compA 243 L[q]! mus[l]!
    if (!L.any fun y => eqA 243 x y) = true then
      have L := L.push x
      have par := par.push q
      have lab := lab.push l
      pure (ForInStep.yield (L, par, lab))
    else pure (ForInStep.yield (L, par, lab))

@[expose] def oStep (mus : Array (Array Nat)) : Nat → St → Id (ForInStep St) := fun _ __s =>
  have L := __s.fst
  have __s := __s.snd
  have par := __s.fst
  have __s := __s.snd
  have lab := __s.fst
  have q := __s.snd
  if q < L.size then do
    let __s ← forIn [:mus.size] (L, par, lab) (iStep mus q)
    have L : Array (Array Nat) := __s.fst
    have __s : Array Nat × Array Nat := __s.snd
    have par : Array Nat := __s.fst
    have lab : Array Nat := __s.snd
    have q : Nat := q + 1
    pure (ForInStep.yield (L, par, lab, q))
  else pure (ForInStep.yield (L, par, lab, q))

theorem pbBFS_eq_forIn (mus : Array (Array Nat)) : pbBFS mus =
    (fun s : St => (s.1, s.2.1, s.2.2.1))
      (forIn (m := Id) [:243] (#[idA 243], #[0], #[0], 0) (oStep mus)) := rfl

@[expose] def ofN {α : Type} (c : Nat) (f : Nat → α) : Array α := Array.ofFn (n := c) fun k => f k.val

theorem ofN_size {α : Type} (c : Nat) (f : Nat → α) : (ofN c f).size = c := Array.size_ofFn

theorem ofN_get {α : Type} [Inhabited α] {c : Nat} (f : Nat → α) {k : Nat} (hk : k < c) :
    (ofN c f)[k]! = f k := by
  rw [getElem!_pos _ k (by rw [ofN_size]; exact hk)]
  unfold ofN
  rw [Array.getElem_ofFn]

theorem ofN_getElem {α : Type} [Inhabited α] {c : Nat} (f : Nat → α) {k : Nat}
    (hk : k < (ofN c f).size) : (ofN c f)[k] = f k := by
  rw [← getElem!_pos (ofN c f) k hk, ofN_get f (by rwa [ofN_size] at hk)]

theorem ofN_push {α : Type} (c : Nat) (f : Nat → α) : (ofN c f).push (f c) = ofN (c + 1) f := by
  unfold ofN
  rw [Array.ofFn_succ]
  rfl

theorem ofN_one {α : Type} (f : Nat → α) : ofN 1 f = #[f 0] := by
  rw [← ofN_push 0 f]
  rfl

variable {MUK LK EK PLK SL : Nat → Nat}

theorem pbStep_zero (q l : Nat) : pbStep MUK LK EK PLK q l 0 = 0 := rfl

theorem pbStep_cases {q l c : Nat} (h : pbStep MUK LK EK PLK q l c ≠ 0) :
    c ≠ 0 ∧ q < c ∧ ((edge EK q l < c ∧ LK (edge EK q l) = ps (LK q) (MUK l) ∧
        pbStep MUK LK EK PLK q l c = c) ∨
      (edge EK q l = c ∧ LK c = ps (LK q) (MUK l) ∧ parP PLK c = q ∧ labP PLK c = l ∧
        pbStep MUK LK EK PLK q l c = c + 1)) := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact h rfl
  have hc' : Nat.beq c 0 = false := by
    cases c with
    | zero => exact absurd rfl hc
    | succ c => rfl
  have hq : Nat.blt q c = true := by
    cases hq : Nat.blt q c
    · exfalso
      apply h
      unfold pbStep
      rw [hc', hq]
    · rfl
  refine ⟨hc, Nat.blt_eq.mp hq, ?_⟩
  have e1 : pbStep MUK LK EK PLK q l c =
      nIf(Nat.blt (edge EK q l) c, nIf(Nat.beq (LK (edge EK q l)) (ps (LK q) (MUK l)), c, 0),
        nIf(bAnd(Nat.beq (edge EK q l) c, bAnd(Nat.beq (LK c) (ps (LK q) (MUK l)),
          bAnd(Nat.beq (parP PLK c) q, Nat.beq (labP PLK c) l))), c + 1, 0)) := by
    unfold pbStep
    rw [hc', hq, strictN_eq, strictN_eq]
  rw [e1] at h ⊢
  cases hj : Nat.blt (edge EK q l) c
  · rw [hj] at h
    right
    cases hb : bAnd(Nat.beq (edge EK q l) c, bAnd(Nat.beq (LK c) (ps (LK q) (MUK l)),
      bAnd(Nat.beq (parP PLK c) q, Nat.beq (labP PLK c) l)))
    · rw [hb] at h
      exact absurd rfl h
    · have hb' := hb
      simp only [bAnd_iff] at hb'
      obtain ⟨h1, h2, h3, h4⟩ := hb'
      exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
        Nat.eq_of_beq_eq_true h4, rfl⟩
  · rw [hj] at h
    left
    cases he : Nat.beq (LK (edge EK q l)) (ps (LK q) (MUK l))
    · rw [he] at h
      exact absurd rfl h
    · exact ⟨Nat.blt_eq.mp hj, Nat.eq_of_beq_eq_true he, rfl⟩

noncomputable abbrev R (MUK LK EK PLK : Nat → Nat) (q : Nat) : Nat := pbRun MUK LK EK PLK q

theorem R_zero : R MUK LK EK PLK 0 = 1 := rfl

theorem R_succ (q : Nat) : R MUK LK EK PLK (q + 1) =
    pbStep MUK LK EK PLK q 1 (pbStep MUK LK EK PLK q 0 (R MUK LK EK PLK q)) := by
  change strictN (pbStep MUK LK EK PLK q 0 (R MUK LK EK PLK q)) (pbStep MUK LK EK PLK q 1) = _
  rw [strictN_eq]

theorem pbStep_ge {q l c : Nat} (h : pbStep MUK LK EK PLK q l c ≠ 0) :
    c ≤ pbStep MUK LK EK PLK q l c ∧ pbStep MUK LK EK PLK q l c ≤ c + 1 := by
  obtain ⟨-, -, h1 | h1⟩ := pbStep_cases h
  · rw [h1.2.2]
    omega
  · rw [h1.2.2.2.2]
    omega

theorem R_ne (h81 : R MUK LK EK PLK 81 = 81) : ∀ q ≤ 81, R MUK LK EK PLK q ≠ 0 := by
  have key : ∀ d ≤ 81, R MUK LK EK PLK (81 - d) ≠ 0 := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, h81]
      decide
    | succ d ih =>
      intro hd e
      apply ih (by omega)
      have e2 : 81 - d = (81 - (d + 1)) + 1 := by omega
      rw [e2, R_succ, e, pbStep_zero, pbStep_zero]
  intro q hq
  have := key (81 - q) (by omega)
  rwa [show 81 - (81 - q) = q by omega] at this

theorem R_le (h81 : R MUK LK EK PLK 81 = 81) : ∀ q ≤ 81, R MUK LK EK PLK q ≤ 81 := by
  have key : ∀ d ≤ 81, R MUK LK EK PLK (81 - d) ≤ 81 := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, h81]
    | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      have e2 : 81 - d = (81 - (d + 1)) + 1 := by omega
      rw [e2] at ih'
      have hne := R_ne h81 ((81 - (d + 1)) + 1) (by omega)
      rw [R_succ] at hne ih'
      have h0 : pbStep MUK LK EK PLK (81 - (d + 1)) 0 (R MUK LK EK PLK (81 - (d + 1))) ≠ 0 :=
        fun e => by
          rw [e, pbStep_zero] at hne
          exact hne rfl
      have a := (pbStep_ge h0).1
      have b := (pbStep_ge hne).1
      omega
  intro q hq
  have := key (81 - q) (by omega)
  rwa [show 81 - (81 - q) = q by omega] at this

variable {mus : Array (Array Nat)}

noncomputable abbrev st3 (LK PLK : Nat → Nat) (c : Nat) : St3 :=
  (ofN c fun k => unpack 243 8 (LK k), ofN c (parP PLK), ofN c (labP PLK))

theorem any_iff {c x : Nat} (hc : ∀ k < c, canonK 243 8 (mask 8) (243 * 8) (LK k) = true)
    (hx : canonK 243 8 (mask 8) (243 * 8) x = true) :
    ((ofN c fun k => unpack 243 8 (LK k)).any fun y => eqA 243 (unpack 243 8 x) y) = true ↔
      ∃ j < c, LK j = x := by
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨j, hj, e⟩
    have hj' : j < c := by rwa [ofN_size] at hj
    refine ⟨j, hj', ?_⟩
    rw [ofN_getElem (fun k => unpack 243 8 (LK k)) hj, eqA_unpack hx (hc j hj')] at e
    exact (Nat.eq_of_beq_eq_true e).symm
  · rintro ⟨j, hj, e⟩
    have hj' : j < (ofN c fun k => unpack 243 8 (LK k)).size := by rw [ofN_size]; exact hj
    refine ⟨j, hj', ?_⟩
    rw [ofN_getElem (fun k => unpack 243 8 (LK k)) hj', e, eqA_unpack hx hx]
    exact Nat.beq_refl x

variable (hMs : mus.size = 2) (hM : ∀ l < 2, mus[l]! = unpack 243 8 (MUK l))
  (hMc : ∀ l < 2, canonK 243 8 (mask 8) (243 * 8) (MUK l) = true)
  (h : pbRunK MUK LK EK PLK SL = true)

include h in
theorem run_facts : LK 0 = pidn 243 8 ∧ PLK 0 = 0 ∧
    (∀ k < 81, permOK 243 8 255 1944 (LK k) (pinvS 243 8 255 (LK k)) = true) ∧
    (∀ a < 81, ∀ b < 81, LK a = LK b → a = b) ∧ R MUK LK EK PLK 81 = 81 := by
  unfold pbRunK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun k hk => ?_,
    distinctK_inj h4, Nat.eq_of_beq_eq_true h5⟩
  have := allN_spec h3 k hk
  rwa [strictB_eq] at this

include h in
theorem PP_L {k : Nat} (hk : k < 81) : PP 243 8 (LK k) :=
  PP_of_permOK (by decide) ((run_facts h).2.2.1 k hk)

include h in
theorem canon_L {k : Nat} (hk : k < 81) : canonK 243 8 (mask 8) (243 * 8) (LK k) = true :=
  (PP_L h hk).1

noncomputable abbrev cl (MUK LK EK PLK : Nat → Nat) (q l : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (R MUK LK EK PLK q) (fun l c => pbStep MUK LK EK PLK q l c) l

include hM hMc h in
theorem inner {q : Nat} (hq : q < 81) :
    forIn (m := Id) [:2] (st3 LK PLK (R MUK LK EK PLK q)) (iStep mus q) =
      st3 LK PLK (R MUK LK EK PLK (q + 1)) := by
  obtain ⟨-, -, -, hinj, h81⟩ := run_facts h
  have hne := R_ne h81 (q + 1) (by omega)
  have hle := R_le h81 (q + 1) (by omega)
  rw [R_succ] at hne hle
  have h0 : pbStep MUK LK EK PLK q 0 (R MUK LK EK PLK q) ≠ 0 := fun e => by
    rw [e, pbStep_zero] at hne
    exact hne rfl
  have b1 := (pbStep_ge h0).1
  have hcl2 : cl MUK LK EK PLK q 2 =
      pbStep MUK LK EK PLK q 1 (pbStep MUK LK EK PLK q 0 (R MUK LK EK PLK q)) := rfl
  have hne' : ∀ l < 2, pbStep MUK LK EK PLK q l (cl MUK LK EK PLK q l) ≠ 0 := by
    intro l hl
    interval_cases l
    · exact h0
    · exact hne
  have hle' : ∀ l < 2, pbStep MUK LK EK PLK q l (cl MUK LK EK PLK q l) ≤ 81 := by
    intro l hl
    interval_cases l
    · exact le_trans (pbStep_ge hne).1 hle
    · exact hle
  rw [R_succ, ← hcl2]
  refine forIn_range_yield (fun l s => s = st3 LK PLK (cl MUK LK EK PLK q l)) (iStep mus q) 2 _
    (fun l s hl hs => ?_) rfl
  subst hs
  obtain ⟨-, hqc, hcase⟩ := pbStep_cases (hne' l hl)
  have hx : compA 243 (ofN (cl MUK LK EK PLK q l) fun k => unpack 243 8 (LK k))[q]! mus[l]! =
      unpack 243 8 (ps (LK q) (MUK l)) := by
    rw [ofN_get _ hqc, hM l hl]
    exact compA_unpack (canon_L h hq) (hMc l hl)
  have hcx : canonK 243 8 (mask 8) (243 * 8) (ps (LK q) (MUK l)) = true :=
    canonK_pcomp (canon_L h hq) (hMc l hl)
  have hlt := hle' l hl
  have hge := (pbStep_ge (hne' l hl)).1
  have hcL : ∀ k < cl MUK LK EK PLK q l, canonK 243 8 (mask 8) (243 * 8) (LK k) = true :=
    fun k hk => canon_L h (by omega)
  simp only [iStep, st3]
  rcases hcase with ⟨hj, he, hs⟩ | ⟨hj, he, hp, hb, hs⟩
  · refine ⟨st3 LK PLK (cl MUK LK EK PLK q l), ?_, ?_⟩
    · split
      · next hc =>
        exfalso
        rw [hx, Bool.not_eq_true'] at hc
        have := (any_iff hcL hcx).2 ⟨_, hj, he⟩
        rw [hc] at this
        exact absurd this (by decide)
      · rfl
    · change st3 LK PLK (cl MUK LK EK PLK q l) =
        st3 LK PLK (pbStep MUK LK EK PLK q l (cl MUK LK EK PLK q l))
      rw [hs]
  · refine ⟨st3 LK PLK (cl MUK LK EK PLK q l + 1), ?_, ?_⟩
    · split
      · rw [hx, ← he]
        simp only [st3]
        rw [← ofN_push _ (fun k => unpack 243 8 (LK k)), ← ofN_push _ (parP PLK),
          ← ofN_push _ (labP PLK), hp, hb]
        rfl
      · next hc =>
        exfalso
        apply hc
        rw [hx, Bool.not_eq_true']
        cases e : ((ofN (cl MUK LK EK PLK q l) fun k => unpack 243 8 (LK k)).any fun y =>
            eqA 243 (unpack 243 8 (ps (LK q) (MUK l))) y)
        · rfl
        · obtain ⟨j, hj', ej⟩ := (any_iff hcL hcx).1 e
          have := hinj j (by omega) _ (by omega) (ej.trans he.symm)
          omega
    · change st3 LK PLK (cl MUK LK EK PLK q l + 1) =
        st3 LK PLK (pbStep MUK LK EK PLK q l (cl MUK LK EK PLK q l))
      rw [hs]

noncomputable abbrev ost (MUK LK EK PLK : Nat → Nat) (s : Nat) : St :=
  ((st3 LK PLK (R MUK LK EK PLK (min s 81))).1, (st3 LK PLK (R MUK LK EK PLK (min s 81))).2.1,
    (st3 LK PLK (R MUK LK EK PLK (min s 81))).2.2, min s 81)

include hMs hM hMc h in
theorem outer : forIn (m := Id) [:243] (#[idA 243], #[0], #[0], 0) (oStep mus) =
    ost MUK LK EK PLK 243 := by
  obtain ⟨hL0, hP0, -, -, h81⟩ := run_facts h
  refine forIn_range_yield (fun s st => st = ost MUK LK EK PLK s) (oStep mus) 243 _
    (fun s st hs hst => ?_) ?_
  · subst hst
    by_cases hq : min s 81 < 81
    · have hqc : min s 81 < R MUK LK EK PLK (min s 81) := by
        have hne := R_ne h81 (min s 81 + 1) (by omega)
        rw [R_succ] at hne
        have h0 : pbStep MUK LK EK PLK (min s 81) 0 (R MUK LK EK PLK (min s 81)) ≠ 0 :=
          fun e => by rw [e, pbStep_zero] at hne; exact hne rfl
        exact (pbStep_cases h0).2.1
      have hin := inner hM hMc h hq
      refine ⟨ost MUK LK EK PLK (s + 1), ?_, rfl⟩
      simp only [oStep, ost, st3]
      rw [if_pos (by rw [ofN_size]; exact hqc), hMs]
      simp only [st3] at hin
      rw [hin]
      have e : min (s + 1) 81 = min s 81 + 1 := by omega
      rw [e]
      rfl
    · have e1 : min s 81 = 81 := by omega
      have e2 : min (s + 1) 81 = 81 := by omega
      refine ⟨ost MUK LK EK PLK (s + 1), ?_, rfl⟩
      simp only [oStep, ost, st3]
      rw [if_neg (by rw [ofN_size, e1, h81]; exact lt_irrefl 81), e1, e2]
      rfl
  · have hid : idA 243 = unpack 243 8 (LK 0) := by rw [hL0]; exact idA_eq (by decide)
    simp only [ost, st3]
    rw [show min 0 81 = 0 from rfl, R_zero, ofN_one, ofN_one, ofN_one, ← hid]
    have e0 : parP PLK 0 = 0 := by unfold parP; rw [hP0]; rfl
    have e1 : labP PLK 0 = 0 := by unfold labP; rw [hP0]; rfl
    rw [e0, e1]

include hMs hM hMc h in
theorem pbBFS_eq : pbBFS mus =
    (ofN 81 fun k => unpack 243 8 (LK k), ofN 81 (parP PLK), ofN 81 (labP PLK)) := by
  have h81 := (run_facts h).2.2.2.2
  rw [pbBFS_eq_forIn, outer hMs hM hMc h]
  simp only [ost, st3]
  rw [show min 243 81 = 81 from rfl, h81]

end CFSG.KC.Fi22RkS

end
