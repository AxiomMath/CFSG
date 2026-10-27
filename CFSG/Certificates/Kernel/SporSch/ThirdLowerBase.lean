
module

public import CFSG.Sporadic.Co2Schreier.ThirdEBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

abbrev ECheckH : Prop :=
  eCheck co2PosTable witRec (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr uArr = true

theorem eFactsH (h : ECheckH) : EFacts := by
  have h' : eCheck co2PosTable witRec (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr
      uArr = true := h
  simp only [eCheck, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h'
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

variable (h : ECheckH)
include h

theorem gA_sizeH : gA.size = 15 := beq_iff_eq.1 (eFactsH h).size

theorem gFactsH {i : ℕ} (hi : i < 15) :
    isInvA 2300 gA[i]! (invCand 2300 gA[i]!) = true ∧
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 gA[i]! = true ∧
      eqA 2300 (compA 2300 gA[i]! uArr) (compA 2300 uArr gA[i]!) = true := by
  have h1 := allLt_iff.1 (eFactsH h).gens i hi
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨h2, _⟩, h3⟩, h4⟩ := h1
  exact ⟨h2, h3, h4⟩

theorem rep_gPermH {i : ℕ} (hi : i < 15) : Rep 2300 gA[i]! (gPerm i) :=
  (rep_permOfArr (gFactsH h hi).1).1

theorem repTuple_gH : RepTuple 2300 gA gTuple := by
  refine ⟨by rw [gA_sizeH h, gTuple_length], fun i hi => ?_⟩
  rw [gTuple_length] at hi
  rw [gTuple_getD hi]
  exact rep_gPermH h hi

theorem eRec_shapeH : ChainShape eRec 2300 15 26 witRec.third.baseIndices :=
  chainShape_of (eFactsH h).eShape

end CFSG.Sporadic.Co2Schreier
