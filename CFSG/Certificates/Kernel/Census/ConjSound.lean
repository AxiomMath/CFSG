module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import Certificates.Data.Kernel.Census.PackedConj

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert

theorem zip_all_of_chunks {α β : Type*} {f : α × β → Bool} {a : List α} {b : List β} {L C : Nat}
    (hC : a.length ≤ C * L)
    (h : ∀ c < C, (((a.drop (c * L)).take L).zip ((b.drop (c * L)).take L)).all f = true) :
    (a.zip b).all f = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  rw [List.length_zip] at hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.mul_zero] at hC
      omega
    · exact h0
  have hdiv : i = i / L * L + i % L := by rw [Nat.mul_comm]; exact (Nat.div_add_mod i L).symm
  have hc : i / L < C := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  refine List.all_eq_true.1 (h (i / L) hc) _ ?_
  rw [List.mem_iff_getElem]
  have hm : i % L < L := Nat.mod_lt _ hL
  refine ⟨i % L, ?_, ?_⟩
  · simp only [List.length_zip, List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_zip, List.getElem_take, List.getElem_drop]
    congr 2 <;> omega

theorem pinvRest_append {n w : Nat} {xs : List Nat} : ∀ {m : Nat} {im a b : List Nat},
    pinvRest n w xs m im (a ++ b) =
      (pinvRest n w xs m im a).bind fun r => pinvRest n w xs (m + a.length) r b
  | m, im, [], b => by simp [pinvRest]
  | m, im, x :: a, b => by
    simp only [List.cons_append, pinvRest, List.length_cons]
    rw [show m + (a.length + 1) = m + 1 + a.length by omega]
    cases Nat.beq (im.headD (2 ^ xs.length)) m <;>
      cases (Nat.beq m 0 || (Nat.blt x n && !(Nat.beq (ppcAt w xs m (ppcAt w xs m x)) x))) <;>
      simp [pinvRest_append]

theorem pinvRest_append_of {n w : Nat} {xs : List Nat} {m m' L : Nat} {im r a b : List Nat}
    (hL : a.length = L) (hm : m + L = m') (ha : pinvRest n w xs m im a = some r) :
    pinvRest n w xs m im (a ++ b) = pinvRest n w xs m' r b := by
  rw [pinvRest_append, ha]
  simp [hL, hm]

theorem pentsOK_of_blocks {n w : Nat} {bs : Array (Array Nat)} {cN : Array ArrCertP}
    {us cs ci : Array Nat} {es : List (Nat × Nat × Nat)} {i L C : Nat}
    (hl : Nat.beq es.length us.size = true) (hC : us.size ≤ C * L)
    (h : ∀ c < C, (((us.toList.drop (c * L)).take L).zip ((es.drop (c * L)).take L)).all
      (fun ue => pentOK n w bs cN cs ci i ue.1 ue.2) = true) :
    pentsOK n w bs cN us cs ci es i = true := by
  unfold pentsOK
  rw [hl, Bool.true_and]
  exact zip_all_of_chunks (by simpa using hC) h

theorem pnodeOKC_of_q {n w : Nat} {ps : List Nat} {inX outX inW : Nat → Bool}
    {allowPW allowInX allowU : Bool} {d : ConjDataP} {cN : Array ArrCertP} {e0 : Array Nat}
    {i : Nat}
    (hq : (penumOK n w d.nodes[i]!.basis ps cN[i]! &&
      cond d.nodes[i]!.wit.isMono
        (pwitOK n w ps inX outX allowPW allowInX allowU d.nodes[i]!.basis cN[i]! d.wcs[i]!
          d.nodes[i]!.wit)
        (pwitOK n w ps inX outX allowPW allowInX allowU d.nodes[i]!.basis cN[i]! d.wcs[i]!
          d.nodes[i]!.wit || pexcOK n w ps inW e0 cN d.excs i)) = true)
    (he : d.nodes[i]!.wit.isMono = false →
      pentsOK n w (d.nodes.map NodeP.basis) cN d.us d.cs d.ci d.ents[i]! i = true) :
    pnodeOKC n w ps inX outX inW allowPW allowInX allowU d cN e0 i = true := by
  cases hm : d.nodes[i]!.wit.isMono <;> simp_all [pnodeOKC]

theorem pnodeOKC_of_mono {n w : Nat} {ps : List Nat} {inX outX inW : Nat → Bool}
    {allowPW allowInX allowU : Bool} {d : ConjDataP} {cN : Array ArrCertP} {e0 : Array Nat}
    {i : Nat} (hE : penumOK n w d.nodes[i]!.basis ps cN[i]! = true)
    (hw : pwitOK n w ps inX outX allowPW allowInX allowU d.nodes[i]!.basis cN[i]! d.wcs[i]!
      d.nodes[i]!.wit = true) (hm : d.nodes[i]!.wit.isMono = true) :
    pnodeOKC n w ps inX outX inW allowPW allowInX allowU d cN e0 i = true := by
  simp [pnodeOKC, hE, hw, hm]

theorem pnodeOKC_of_ents {n w : Nat} {ps : List Nat} {inX outX inW : Nat → Bool}
    {allowPW allowInX allowU : Bool} {d : ConjDataP} {cN : Array ArrCertP} {e0 : Array Nat}
    {i : Nat} (hE : penumOK n w d.nodes[i]!.basis ps cN[i]! = true)
    (hw : (pwitOK n w ps inX outX allowPW allowInX allowU d.nodes[i]!.basis cN[i]! d.wcs[i]!
      d.nodes[i]!.wit || pexcOK n w ps inW e0 cN d.excs i) = true)
    (he : pentsOK n w (d.nodes.map NodeP.basis) cN d.us d.cs d.ci d.ents[i]! i = true) :
    pnodeOKC n w ps inX outX inW allowPW allowInX allowU d cN e0 i = true := by
  simp only [pnodeOKC, Bool.and_eq_true, Bool.or_eq_true] at hw ⊢
  exact ⟨hE, Or.inr ⟨hw, he⟩⟩

end CFSG.KC.Census
