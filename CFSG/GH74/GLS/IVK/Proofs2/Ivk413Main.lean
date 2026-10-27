module

public import CFSG.GH74.GLS.IVK.Proofs2.Stmt413
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Stage2.Final.ModelGroupTheory
public import CFSG.GH74.GLS.Stage2.Final.ModelTransport
public import CFSG.GH74.L5U5.IdentOdd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GorensteinWalter
  CFSG.GH74.GLS.IVK
open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem prime_ne_two_of_odd_pow {p f q : ℕ} (hq : q = p ^ f) (hodd : Odd q) (h3 : 3 < q) :
    p ≠ 2 := by
  rintro rfl
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
    omega
  have : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, hf⟩
  rw [← hq] at this
  exact (Nat.not_even_iff_odd.2 hodd) this

end CFSG.GH74.GLS.IVK.Proofs2
