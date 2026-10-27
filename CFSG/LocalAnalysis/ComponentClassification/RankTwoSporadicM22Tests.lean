module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import CFSG.Monster.CodeAut.Perm

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M22

open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.Code

@[expose] def wordComp (x : Fin 24 → ZMod 2) (a : Array ℕ) : Fin 24 → ZMod 2 :=
  fun j => x ⟨a[(j : ℕ)]! % 24, Nat.mod_lt _ (by norm_num)⟩

@[expose] def autA (a : Array ℕ) : Bool :=
  validA 24 a && (List.finRange 12).all (fun i => decide (wordComp (B i) a ∈ C)) &&
    (List.finRange 12).all (fun i => decide (wordComp (B i) (invCand 24 a) ∈ C))

theorem wordComp_eq {a : Array ℕ} {p : Equiv.Perm (Fin 24)} (h : Rep 24 a p)
    (x : Fin 24 → ZMod 2) : wordComp x a = x ∘ ⇑p := by
  funext j
  simp only [wordComp, Function.comp_apply]
  congr 1
  refine Fin.ext ?_
  show a[(j : ℕ)]! % 24 = (p j : ℕ)
  rw [h j]
  exact Nat.mod_eq_of_lt (p j).2

theorem mem_AutPerm_of_autA {a : Array ℕ} (h : autA a = true) : permOfArr 24 a ∈ AutPerm := by
  simp only [autA, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
    true_implies] at h
  obtain ⟨⟨hv, h1⟩, h2⟩ := h
  refine mem_AutPerm_of_basis (fun i => ?_) (fun i => ?_)
  · rw [← wordComp_eq (rep_of_validA hv)]
    exact h1 i
  · rw [← wordComp_eq (rep_inv_of_validA hv)]
    exact h2 i

@[expose] def m22InX (a : Array ℕ) : Bool := autA a && a[0]! == 0 && a[1]! == 1

@[expose] def m22OutX (a : Array ℕ) : Bool := a[0]! == 0 && a[1]! == 1

@[expose] def pairA (a : Array ℕ) : Bool :=
  autA a && (a[0]! == 0 && a[1]! == 1 || a[0]! == 1 && a[1]! == 0)

@[expose] def m22PS : List ℕ := [0, 1, 2, 3, 4, 5, 8, 9]

@[expose] def m22Fuel : ℕ := 2 ^ 20

@[expose] def m22Check (allowPW allowInX : Bool) (s : String) : Bool :=
  let d := decodeCert 24 s
  censusOK 24 m22PS m22Fuel m22InX m22OutX allowPW allowInX false d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k => pairA d.sGens[k]!) &&
    (enumBfs 24 d.sGens m22PS m22Fuel).pts.size == 256

theorem m22PS_lt : ∀ p ∈ m22PS, p < 24 := by decide

end CFSG.ComponentClassification.RankTwoSporadic.M22
