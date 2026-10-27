module

public import Certificates.Data.Kernel.HeSylQEK
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowQETests
import CFSG.Certificates.Kernel.HeSylKSound

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] def heSylowQECheckG (e16 f16 q16 x16 : List (Array Nat)) (z16 : Array Nat)
    (e32 f32 q32 x32 : List (Array Nat)) (z32 : Array Nat) : Bool :=
  interCountN 16 e16 q16 16 48 && interCountN 16 f16 q16 16 48 && centQN 16 x16 q16 z16 &&
    interCountN 32 e32 q32 16 48 && interCountN 32 f32 q32 16 48 && centQN 32 x32 q32 z32

theorem heSylowQECheck_eq : heSylowQECheck = heSylowQECheckG heSylE16 heSylF16 heSylQ16 heSyl16
    heSylZ16 heAutE32 heAutF32 heAutQ32 hfT0Tabs32.toList heAutZ32 := rfl

variable {n w : Nat}

theorem szOK_of_pin {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs g G N T E S) : szOK n w = true := by
  have h := p.ok
  unfold bfsK at h
  simp only [bAnd_iff] at h
  exact h.1

theorem interCountN_of {es qs : List (Array Nat)} {cE cQ NE NQ k l : Nat}
    {GE TE EE SE GQ TQ EQ SQ : Nat → Nat}
    (pE : Pin n w es cE GE NE TE EE SE) (pQ : Pin n w qs cQ GQ NQ TQ EQ SQ)
    (h : interK NE TE NQ TQ k l = true) : interCountN n es qs k l = true := by
  have sE := PP_pts pE.ok pE.perm
  have sQ := PP_pts pQ.ok pQ.perm
  unfold interK at h
  rw [andB_eq, Bool.and_eq_true, cntR_eq, cntR_eq] at h
  obtain ⟨h1, h2⟩ := h
  unfold interCountN
  rw [eltsN_eq pE.size pE.bind pE.ok pE.fuel, eltsN_eq pQ.size pQ.bind pQ.ok pQ.fuel,
    List.filter_map, List.filter_map, List.length_map, List.length_map, Bool.and_eq_true,
    beq_iff_eq, beq_iff_eq, ← Nat.eq_of_beq_eq_true h1, ← Nat.eq_of_beq_eq_true h2]
  constructor
  · congr 1
    refine List.filter_congr fun i hi => ?_
    rw [Function.comp_apply, inLN_eq (sE i (List.mem_range.1 hi)) sQ]
  · congr 1
    refine List.filter_congr fun i hi => ?_
    rw [Function.comp_apply, inLN_eq (sE i (List.mem_range.1 hi)) sQ, notB_eq]

theorem centQN_of {gs qs : List (Array Nat)} {cX cQ NX NQ P : Nat}
    {GX TX EX SX GQ TQ EQ SQ : Nat → Nat}
    (pX : Pin n w gs cX GX NX TX EX SX) (pQ : Pin n w qs cQ GQ NQ TQ EQ SQ)
    (hp : permOK n w (mask w) (n * w) P (pinvS n w (mask w) P) = true)
    (h : centK n w NX TX cQ GQ P = true) : centQN n gs qs (unpack n w P) = true := by
  have sX := PP_pts pX.ok pX.perm
  have qQ := PP_gen pQ.ok pQ.perm
  have pz : PP n w P := PP_of_permOK (szOK_of_pin pX) hp
  unfold centQN
  unfold centK at h
  rw [eltsN_eq pX.size pX.bind pX.ok pX.fuel, gens_eq pQ.size pQ.bind, List.all_map,
    List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have pi := sX i hi'
  have h1 := allN_spec h i hi'
  rw [strictB_eq', orB_eq, notB_eq, allN_eq'] at h1
  rw [Function.comp_apply, all_map_congr (p := commN n (unpack n w (TX i)))
    fun k hk => commN_PP pi (qQ k (List.mem_range.1 hk)), inZN_PP pz pi]
  exact h1

theorem heSylowQEK_sound {v w : Nat} {e16 f16 q16 x16 e32 f32 q32 x32 : List (Array Nat)}
    {z16 z32 : Array Nat} {P16 P32 : Nat}
    {cE cF cQ cX cE' cF' cQ' cX' NE NF NQ NX NE' NF' NQ' NX' : Nat}
    {GE GF GQ GX TE TF TQ TX EE EF EQ EX SE SF SQ SX : Nat → Nat}
    {GE' GF' GQ' GX' TE' TF' TQ' TX' EE' EF' EQ' EX' SE' SF' SQ' SX' : Nat → Nat}
    (pE : Pin 16 v e16 cE GE NE TE EE SE) (pF : Pin 16 v f16 cF GF NF TF EF SF)
    (pQ : Pin 16 v q16 cQ GQ NQ TQ EQ SQ) (pX : Pin 16 v x16 cX GX NX TX EX SX)
    (pE' : Pin 32 w e32 cE' GE' NE' TE' EE' SE') (pF' : Pin 32 w f32 cF' GF' NF' TF' EF' SF')
    (pQ' : Pin 32 w q32 cQ' GQ' NQ' TQ' EQ' SQ') (pX' : Pin 32 w x32 cX' GX' NX' TX' EX' SX')
    (hz16 : z16 = unpack 16 v P16) (hz32 : z32 = unpack 32 w P32)
    (hp16 : permOK 16 v (mask v) (16 * v) P16 (pinvS 16 v (mask v) P16) = true)
    (hp32 : permOK 32 w (mask w) (32 * w) P32 (pinvS 32 w (mask w) P32) = true)
    (h16 : (interK NE TE NQ TQ 16 48 && interK NF TF NQ TQ 16 48 &&
      centK 16 v NX TX cQ GQ P16) = true)
    (h32 : (interK NE' TE' NQ' TQ' 16 48 && interK NF' TF' NQ' TQ' 16 48 &&
      centK 32 w NX' TX' cQ' GQ' P32) = true) :
    heSylowQECheckG e16 f16 q16 x16 z16 e32 f32 q32 x32 z32 = true := by
  subst hz16 hz32
  simp only [Bool.and_eq_true] at h16 h32
  unfold heSylowQECheckG
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨interCountN_of pE pQ h16.1.1, interCountN_of pF pQ h16.1.2⟩,
    centQN_of pX pQ hp16 h16.2⟩, interCountN_of pE' pQ' h32.1.1⟩,
    interCountN_of pF' pQ' h32.1.2⟩, centQN_of pX' pQ' hp32 h32.2⟩

end CFSG.KC.HeAutK

end
