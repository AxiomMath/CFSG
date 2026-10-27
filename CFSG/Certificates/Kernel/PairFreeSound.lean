module

public import Certificates.Data.Kernel.PairFreeK
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.RankThree.PartOne.K133Spor.HSPairInputs

public section

namespace CFSG.KC.PairFree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartOne.K133Spor

variable {n w : Nat}

theorem inv_eq (hw : szOK n w = true) {p : Nat} (hp : PP n w p) :
    (eqA n (compA n (unpack n w p) (unpack n w p)) (idA n) && !eqA n (unpack n w p) (idA n)) =
      invK n w p := by
  rw [compA_PP hp hp, idA_eq hw, eqA_PP (hp.mul hp) (PP.id hw), eqA_PP hp (PP.id hw)]
  rfl

theorem five_eq (hw : szOK n w = true) {p : Nat} (hp : PP n w p) :
    (eqA n (powA5 n (unpack n w p)) (idA n) && !eqA n (unpack n w p) (idA n)) = fiveK n w p := by
  have h2 := hp.mul hp
  have h3 := hp.mul h2
  have h4 := hp.mul h3
  rw [powA5, compA_PP hp hp, compA_PP hp h2, compA_PP hp h3, compA_PP hp h4, idA_eq hw,
    eqA_PP (hp.mul h4) (PP.id hw), eqA_PP hp (PP.id hw)]
  rfl

theorem line_eq (hw : szOK n w = true) {X p : Nat} (hX : PP n w X) (hp : PP n w p) :
    memLineA n (unpack n w X) (unpack n w p) = lineK n w X p := by
  have h2 := hX.mul hX
  have h3 := hX.mul h2
  have h4 := hX.mul h3
  rw [memLineA, compA_PP hX hX, compA_PP hX h2, compA_PP hX h3, idA_eq hw,
    eqA_PP hp (PP.id hw), eqA_PP hp hX, eqA_PP hp h2, eqA_PP hp h3, eqA_PP hp h4]
  rfl

theorem comm_eq {p q : Nat} (hp : PP n w p) (hq : PP n w q) :
    eqA n (compA n (unpack n w p) (unpack n w q)) (compA n (unpack n w q) (unpack n w p)) =
      Nat.beq (cmK n w p q) (cmK n w q p) := by
  rw [compA_PP hp hq, compA_PP hq hp, eqA_PP (hp.mul hq) (hq.mul hp)]
  rfl

theorem pairFreeK_sound {N : Nat} {T : Nat → Nat} {X : Nat} {I F : List Nat}
    (hw : szOK n w = true) (hT : ∀ i < N, PP n w (T i)) (hX : PP n w X)
    (h : pairFreeK n w N T X I F = true) :
    pairFreeCheck n (Array.ofFn (n := N) fun i => unpack n w (T i.val)) (unpack n w X) = true := by
  unfold pairFreeK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hF, hI⟩, hIF⟩ := h
  unfold pairFreeCheck
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < N := by simpa using hi
  simp only [Array.getElem_ofFn]
  rw [inv_eq hw (hT i hi')]
  cases hinv : invK n w (T i)
  · rfl
  have hiI : i ∈ I := by
    have := allN_spec hI i hi'
    rw [hinv] at this
    simpa using this
  rw [Bool.not_true, Bool.false_or, Array.all_eq_true]
  intro j hj
  have hj' : j < N := by simpa using hj
  simp only [Array.getElem_ofFn]
  rw [five_eq hw (hT j hj'), line_eq hw hX (hT j hj'), comm_eq (hT i hi') (hT j hj')]
  cases h5 : fiveK n w (T j)
  · rfl
  cases hl : lineK n w X (T j)
  · have hjF : j ∈ F := by
      have := allN_spec hF j hj'
      rw [h5, hl] at this
      simpa using this
    have hc := hIF i hiI j hjF
    rw [hc]
    rfl
  · rfl

end CFSG.KC.PairFree

end
