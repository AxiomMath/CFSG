module

public import CFSG.Certificates.Kernel.Fi22Rk.Pb
public import Certificates.Data.Kernel.Fi22Rk.DefsN
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KC.Fi22RkS

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.Sporadic.FischerOddCore.SearchSpec (forIn_range_yield)

variable {N : Nat} {MUK LK EK PLK SL : Nat → Nat}

theorem R_neN (hN : R MUK LK EK PLK N = N) (hN1 : 1 ≤ N) :
    ∀ q ≤ N, R MUK LK EK PLK q ≠ 0 := by
  have key : ∀ d ≤ N, R MUK LK EK PLK (N - d) ≠ 0 := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, hN]
      omega
    | succ d ih =>
      intro hd e
      apply ih (by omega)
      have e2 : N - d = (N - (d + 1)) + 1 := by omega
      rw [e2, R_succ, e, pbStep_zero, pbStep_zero]
  intro q hq
  have := key (N - q) (by omega)
  rwa [show N - (N - q) = q by omega] at this

theorem R_leN (hN : R MUK LK EK PLK N = N) (hN1 : 1 ≤ N) :
    ∀ q ≤ N, R MUK LK EK PLK q ≤ N := by
  have key : ∀ d ≤ N, R MUK LK EK PLK (N - d) ≤ N := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, hN]
    | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      have e2 : N - d = (N - (d + 1)) + 1 := by omega
      rw [e2] at ih'
      have hne := R_neN hN hN1 ((N - (d + 1)) + 1) (by omega)
      rw [R_succ] at hne ih'
      have h0 : pbStep MUK LK EK PLK (N - (d + 1)) 0 (R MUK LK EK PLK (N - (d + 1))) ≠ 0 :=
        fun e => by
          rw [e, pbStep_zero] at hne
          exact hne rfl
      have a := (pbStep_ge h0).1
      have b := (pbStep_ge hne).1
      omega
  intro q hq
  have := key (N - q) (by omega)
  rwa [show N - (N - q) = q by omega] at this

variable {mus : Array (Array Nat)}

variable (hMs : mus.size = 2) (hM : ∀ l < 2, mus[l]! = unpack 243 8 (MUK l))
  (hMc : ∀ l < 2, canonK 243 8 (mask 8) (243 * 8) (MUK l) = true)
  (h : pbRunKN N MUK LK EK PLK SL = true)

include h in
theorem run_factsN : LK 0 = pidn 243 8 ∧ PLK 0 = 0 ∧
    (∀ k < N, permOK 243 8 255 1944 (LK k) (pinvS 243 8 255 (LK k)) = true) ∧
    (∀ a < N, ∀ b < N, LK a = LK b → a = b) ∧ R MUK LK EK PLK N = N := by
  unfold pbRunKN at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun k hk => ?_,
    distinctK_inj h4, Nat.eq_of_beq_eq_true h5⟩
  have := allN_spec h3 k hk
  rwa [strictB_eq] at this

include h in
theorem PP_LN {k : Nat} (hk : k < N) : PP 243 8 (LK k) :=
  PP_of_permOK (by decide) ((run_factsN h).2.2.1 k hk)

include h in
theorem canon_LN {k : Nat} (hk : k < N) : canonK 243 8 (mask 8) (243 * 8) (LK k) = true :=
  (PP_LN h hk).1

include hM hMc h in
theorem innerN (hN1 : 1 ≤ N) {q : Nat} (hq : q < N) :
    forIn (m := Id) [:2] (st3 LK PLK (R MUK LK EK PLK q)) (iStep mus q) =
      st3 LK PLK (R MUK LK EK PLK (q + 1)) := by
  obtain ⟨-, -, -, hinj, hRN⟩ := run_factsN h
  have hne := R_neN hRN hN1 (q + 1) (by omega)
  have hle := R_leN hRN hN1 (q + 1) (by omega)
  rw [R_succ] at hne hle
  have h0 : pbStep MUK LK EK PLK q 0 (R MUK LK EK PLK q) ≠ 0 := fun e => by
    rw [e, pbStep_zero] at hne
    exact hne rfl
  have hcl2 : cl MUK LK EK PLK q 2 =
      pbStep MUK LK EK PLK q 1 (pbStep MUK LK EK PLK q 0 (R MUK LK EK PLK q)) := rfl
  have hne' : ∀ l < 2, pbStep MUK LK EK PLK q l (cl MUK LK EK PLK q l) ≠ 0 := by
    intro l hl
    interval_cases l
    · exact h0
    · exact hne
  have hle' : ∀ l < 2, pbStep MUK LK EK PLK q l (cl MUK LK EK PLK q l) ≤ N := by
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
    exact compA_unpack (canon_LN h hq) (hMc l hl)
  have hcx : canonK 243 8 (mask 8) (243 * 8) (ps (LK q) (MUK l)) = true :=
    canonK_pcomp (canon_LN h hq) (hMc l hl)
  have hlt := hle' l hl
  have hge := (pbStep_ge (hne' l hl)).1
  have hcL : ∀ k < cl MUK LK EK PLK q l, canonK 243 8 (mask 8) (243 * 8) (LK k) = true :=
    fun k hk => canon_LN h (by omega)
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

noncomputable abbrev ostN (N : Nat) (MUK LK EK PLK : Nat → Nat) (s : Nat) : St :=
  ((st3 LK PLK (R MUK LK EK PLK (min s N))).1, (st3 LK PLK (R MUK LK EK PLK (min s N))).2.1,
    (st3 LK PLK (R MUK LK EK PLK (min s N))).2.2, min s N)

include hMs hM hMc h in
theorem outerN (hN1 : 1 ≤ N) : forIn (m := Id) [:243] (#[idA 243], #[0], #[0], 0) (oStep mus) =
    ostN N MUK LK EK PLK 243 := by
  obtain ⟨hL0, hP0, -, -, hRN⟩ := run_factsN h
  refine forIn_range_yield (fun s st => st = ostN N MUK LK EK PLK s) (oStep mus) 243 _
    (fun s st hs hst => ?_) ?_
  · subst hst
    by_cases hq : min s N < N
    · have hqc : min s N < R MUK LK EK PLK (min s N) := by
        have hne := R_neN hRN hN1 (min s N + 1) (by omega)
        rw [R_succ] at hne
        have h0 : pbStep MUK LK EK PLK (min s N) 0 (R MUK LK EK PLK (min s N)) ≠ 0 :=
          fun e => by rw [e, pbStep_zero] at hne; exact hne rfl
        exact (pbStep_cases h0).2.1
      have hin := innerN hM hMc h hN1 hq
      refine ⟨ostN N MUK LK EK PLK (s + 1), ?_, rfl⟩
      simp only [oStep, ostN, st3]
      rw [if_pos (by rw [ofN_size]; exact hqc), hMs]
      simp only [st3] at hin
      rw [hin]
      have e : min (s + 1) N = min s N + 1 := by omega
      rw [e]
      rfl
    · have e1 : min s N = N := by omega
      have e2 : min (s + 1) N = N := by omega
      refine ⟨ostN N MUK LK EK PLK (s + 1), ?_, rfl⟩
      simp only [oStep, ostN, st3]
      rw [if_neg (by rw [ofN_size, e1, hRN]; exact lt_irrefl N), e1, e2]
      rfl
  · have hid : idA 243 = unpack 243 8 (LK 0) := by rw [hL0]; exact idA_eq (by decide)
    simp only [ostN, st3]
    rw [show min 0 N = 0 from Nat.zero_min N, R_zero, ofN_one, ofN_one, ofN_one, ← hid]
    have e0 : parP PLK 0 = 0 := by unfold parP; rw [hP0]; rfl
    have e1 : labP PLK 0 = 0 := by unfold labP; rw [hP0]; rfl
    rw [e0, e1]

include hMs hM hMc h in
theorem pbBFS_eqN (hN1 : 1 ≤ N) (hN2 : N ≤ 243) : pbBFS mus =
    (ofN N fun k => unpack 243 8 (LK k), ofN N (parP PLK), ofN N (labP PLK)) := by
  have hRN := (run_factsN h).2.2.2.2
  rw [pbBFS_eq_forIn, outerN hMs hM hMc h hN1]
  simp only [ostN, st3]
  rw [show min 243 N = N from Nat.min_eq_right hN2, hRN]

end CFSG.KC.Fi22RkS

end
