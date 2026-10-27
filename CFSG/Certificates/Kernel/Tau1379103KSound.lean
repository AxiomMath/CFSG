module

public import Certificates.Data.SuzTwoAExtension
public import CFSG.Certificates.Kernel.B0SuzKSound
import CFSG.Certificates.Kernel.B0SuzK.Glue

public section

namespace CFSG.KC.B0SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

@[expose] def tauCheckG (τ tT : Array Nat) (qA : Nat → Array Nat) : Bool :=
  CFSG.Monster.B.Co2.Native.lettersOK 3 tauWord && permOK 1782 τ && commutesA τ tT &&
    (allBelow 6 fun i =>
      eqA 1782 (compA 1782 (compA 1782 τ (qA i)) (invCand 1782 τ))
        (compA 1782 (qProdsG qA)[(tauAct i).1]! (tPowG tT (tauAct i).2))) &&
    notInOK matEnum.tabs (tauMatTab ())

theorem tauCheck_eq : tauCheck () = tauCheckG (tauArr ()) tTab qArr := rfl

private theorem tauAct_lt : ∀ i < 6, (tauAct i).1 < 64 := by decide +kernel

private theorem tauLetters : CFSG.Monster.B.Co2.Native.lettersOK 3 tauWord = true := by decide +kernel

open CFSG.KC.BfsPin in
private theorem qProdsG_facts' {T : Nat} {Q QP QE : Nat → Nat} {qA : Nat → Array Nat}
    (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i)) (hB : baseK T Q QP QE = true) :
    ∀ v < 64, PP 1782 11 (QP v) ∧ (qProdsG qA)[v]! = unpack 1782 11 (QP v) := by
  obtain ⟨-, -, -, hQ, hQP, -⟩ := baseK_facts hB
  intro v hv
  have hP : ∀ i < 6, PP 1782 11 (Q i) := fun i hi => (hQ i hi).1
  rw [hQP v hv]
  refine ⟨(qProdK_spec hP hq v).1, ?_⟩
  unfold qProdsG
  rw [getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn]
  exact (qProdK_spec hP hq v).2

theorem tauK_sound {τ tT : Array Nat} {qA : Nat → Array Nat} {TAU T TM NM : Nat}
    {Q QP QE TMs : Nat → Nat}
    (hτ : τ = unpack 1782 11 TAU) (ht : tT = unpack 1782 11 T)
    (hq : ∀ i < 6, qA i = unpack 1782 11 (Q i))
    (hB : baseK T Q QP QE = true) (hK : q0K T TAU Q QP tauAct NM TMs TM = true)
    (hc : Nat.beq (mul 1782 11 TAU T) (mul 1782 11 T TAU) = true)
    (hM : matEnum.tabs = Array.ofFn (n := NM) fun j => unpack 64 7 (TMs j.val))
    (hcM : ∀ j < NM, canonK 64 7 (mask 7) (64 * 7) (TMs j) = true)
    (hTM : tauMatTab () = unpack 64 7 TM) (hcTM : canonK 64 7 (mask 7) (64 * 7) TM = true) :
    tauCheckG τ tT qA = true := by
  open CFSG.KC.BfsPin in
  obtain ⟨hT, -, -, hQ, -, -⟩ := baseK_facts hB
  obtain ⟨hO, hact, hTMs⟩ := q0K_facts hK
  have hPQP : ∀ v < 64, PP 1782 11 (QP v) := fun v hv => (qProdsG_facts' hq hB v hv).1
  have hqs : ∀ v < 64, (qProdsG qA)[v]! = unpack 1782 11 (QP v) := fun v hv =>
    (qProdsG_facts' hq hB v hv).2
  have htp : ∀ b, tPowG tT b = unpack 1782 11 (tPowK T b) := tPow_unpack ht
  unfold tauCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨tauLetters, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hτ]
    exact permOK_unpack hO
  · rw [hτ, ht, commutesA_unpack hO hT]
    exact hc
  · refine allBelow_iff.2 fun i hi => ?_
    have ha : (tauAct i).1 < 64 := tauAct_lt i hi
    rw [hτ, hq i hi, conj_unpack hO (hQ i hi).1, hqs _ ha, htp,
      compA_PP (hPQP _ ha) (PP_tPowK hT _),
      eqA_PP (hO.conjK (hQ i hi).1) ((hPQP _ ha).mul (PP_tPowK hT _))]
    exact hact i hi
  · unfold notInOK
    rw [hM, Array.size_ofFn]
    refine allBelow_iff.2 fun j hj => ?_
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, hTM]
    have hne : (unpack 64 7 (TMs j) == unpack 64 7 TM) = false := by
      cases h : (unpack 64 7 (TMs j) == unpack 64 7 TM)
      · rfl
      · have heq : unpack 64 7 (TMs j) = unpack 64 7 TM := beq_iff_eq.1 h
        have := eqA_unpack (hcM j hj) hcTM
        rw [heq, eqA_self, hTMs j hj] at this
        exact absurd this (by decide)
    dsimp only
    rw [hne]
    rfl

end CFSG.KC.B0SuzK

end
