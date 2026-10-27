module

public import Certificates.Data.Kernel.D42ConjP
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeD42ConjData
import CFSG.Certificates.Kernel.D4PlaneSound

public section

namespace CFSG.KC.D42ConjP

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.KC.D4PlaneP
open CFSG.LocalAnalysis.AGL81I.Section3.D42Over

theorem conjAny_of_ix {ls : List Nat} {kA kB : Nat} {ws : List (List Nat)} {x i : Nat}
    (h : conjIxP ls kA kB ws x i = true) : conjAnyP ls kA kB ws x = true := by
  unfold conjIxP at h
  unfold conjAnyP
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with h | ⟨hi, hw⟩
  · exact Or.inl h
  · refine Or.inr (List.any_eq_true.2 ⟨ws.getD i [], ?_, hw⟩)
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

theorem conjAny_of_ixAll {ls : List Nat} {kA kB : Nat} {ws : List (List Nat)} :
    ∀ (xs is : List Nat), ixAllP ls kA kB ws xs is = true →
      ∀ x ∈ xs, conjAnyP ls kA kB ws x = true
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | y :: xs, [], h, _, _ => by simp [ixAllP] at h
  | y :: xs, i :: is, h, x, hx => by
    rw [ixAllP, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact conjAny_of_ix h.1
    · exact conjAny_of_ixAll xs is h.2 x hx

section Twin

variable {ls : List Nat} (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)

include hL

theorem elem_eq (x : Array GF8) (hx : x.size = 64) :
    (x == oneArr || !(mulArr x (mulArr x x) == oneArr) ||
      (d42ConjWords.map fun w => (wordArr w, wordArr w.reverse)).any fun p =>
        mulArr (mulArr p.1 x) p.2 == wordArr kAW || mulArr (mulArr p.1 x) p.2 == wordArr kBW) =
      conjAnyP ls (wordP ls kAW) (wordP ls kBW) d42ConjWords (packA x) := by
  unfold conjAnyP cube1P
  have hw : ∀ w ∈ d42ConjWords,
      ((fun p : Array GF8 × Array GF8 =>
          mulArr (mulArr p.1 x) p.2 == wordArr kAW || mulArr (mulArr p.1 x) p.2 == wordArr kBW) ∘
        fun w => (wordArr w, wordArr w.reverse)) w =
        hitW ls (wordP ls kAW) (wordP ls kBW) (packA x) w := by
    intro w _
    simp only [Function.comp, hitW, hitP, isKP, beq_pack (size_mulArr _ _) (size_wordArr _),
      packA_mulArr, packA_wordArr hL]
  rw [List.any_map, any_congr_mem hw, beq_pack hx size_oneArr,
    beq_pack (size_mulArr _ _) size_oneArr, packA_oneArr, packA_mulArr, packA_mulArr]

theorem d42ConjCheck_of {es ix : List Nat}
    (hE : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar es = true)
    (hI : ixAllP ls (wordP ls kAW) (wordP ls kBW) d42ConjWords es ix = true) :
    d42ConjCheck = true := by
  have hS : sylowElems.map packA = es := (map_sylowElems hL).trans (bfsP_of_bfsOK _ _ _ _ hE)
  unfold d42ConjCheck
  dsimp only
  refine List.all_eq_true.2 fun x hx => ?_
  refine (elem_eq hL x (size_sylowElems x hx)).trans ?_
  refine conjAny_of_ixAll es ix hI (packA x) ?_
  rw [← hS]
  exact List.mem_map_of_mem hx

end Twin

end CFSG.KC.D42ConjP

end
