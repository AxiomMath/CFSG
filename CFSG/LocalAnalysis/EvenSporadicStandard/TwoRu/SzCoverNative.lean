module

public import CFSG.Quasithin.Vol2.KGFactC31RuCoverNative
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzInputs

public section

namespace CFSG.EvenSporadicStandard.TwoRu.SzCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover
  CFSG.EvenSporadicStandard.Induction.RuSz

@[expose] def szInvOK (n : ℕ) (t : Array ℕ) : Bool := isInvA n t (invCand n t)

@[expose] def szM1A (n : ℕ) (t0 t1 : Array ℕ) : Array ℕ := (slotRunA n ruMProg t0 t1).1

@[expose] def szM2A (n : ℕ) (t0 t1 : Array ℕ) : Array ℕ := (slotRunA n ruMProg t0 t1).2.1

@[expose] def szMWordA (n : ℕ) (t0 t1 : Array ℕ) (w : List ℤ) : Array ℕ :=
  wordA n #[szM1A n t0 t1, szM2A n t0 t1] #[invCand n (szM1A n t0 t1), invCand n (szM2A n t0 t1)] w

@[expose] def szWA (n : ℕ) (t0 t1 : Array ℕ) : Array ℕ :=
  wordA n #[t0, t1] #[invCand n t0, invCand n t1] ruAlignmentSeedWord

@[expose] def szUA (n : ℕ) (t0 t1 : Array ℕ) : Array ℕ :=
  compA n (compA n (compA n (szWA n t0 t1) (szMWordA n t0 t1 ruRMWord)) (invCand n (szWA n t0 t1))) t0

@[expose] def szHA (n : ℕ) (t0 t1 : Array ℕ) : Array ℕ :=
  compA n (powA n (szUA n t0 t1) 7) (szWA n t0 t1)

@[expose] def szLA (n : ℕ) (t0 t1 : Array ℕ) (i : ℕ) : Array ℕ :=
  compA n (compA n (szHA n t0 t1) (szMWordA n t0 t1 (ruLMWords.getD i []))) (invCand n (szHA n t0 t1))

@[expose] def szLArr (n : ℕ) (t0 t1 : Array ℕ) : Array (Array ℕ) :=
  #[szLA n t0 t1 0, szLA n t0 t1 1, szLA n t0 t1 2]

@[expose] def szLWordA (n : ℕ) (t0 t1 : Array ℕ) (w : List ℤ) : Array ℕ :=
  wordA n (szLArr n t0 t1) ((szLArr n t0 t1).map (invCand n)) w

@[expose] def szSA (n : ℕ) (t0 t1 : Array ℕ) : Array ℕ := szLWordA n t0 t1 sWord

@[expose] def szTA (n : ℕ) (t0 t1 : Array ℕ) : Array ℕ :=
  compA n (szLWordA n t0 t1 tWord) (compA n t0 t0)

@[expose] def szPwordA (n : ℕ) (S Sinv T Tinv : Array ℕ) : List (ℕ × Bool) → Array ℕ
  | [] => idA n
  | l :: w => compA n (if l.1 = 0 then (if l.2 then S else Sinv) else (if l.2 then T else Tinv))
      (szPwordA n S Sinv T Tinv w)

@[expose] def szRelsOK (n : ℕ) (t0 t1 : Array ℕ) : Bool :=
  szRels.all fun v => eqA n (szPwordA n (szSA n t0 t1) (invCand n (szSA n t0 t1)) (szTA n t0 t1)
    (invCand n (szTA n t0 t1)) v) (idA n)

@[expose] def szCoverChk (_ : Unit := ()) : Bool :=
  let n := 16240
  let t0 := p0A ()
  let t1 := p1A ()
  lettersOK gc (zword ruP0) && lettersOK gc (zword ruP1) &&
    szInvOK n t0 && szInvOK n t1 && (slotRunA n ruMProg t0 t1).2.2 &&
    szInvOK n (szM1A n t0 t1) && szInvOK n (szM2A n t0 t1) && szInvOK n (szWA n t0 t1) &&
    szInvOK n (szHA n t0 t1) && szInvOK n (szLA n t0 t1 0) && szInvOK n (szLA n t0 t1 1) &&
    szInvOK n (szLA n t0 t1 2) && szInvOK n (szSA n t0 t1) && szInvOK n (szTA n t0 t1) &&
    szRelsOK n t0 t1

end CFSG.EvenSporadicStandard.TwoRu.SzCover
