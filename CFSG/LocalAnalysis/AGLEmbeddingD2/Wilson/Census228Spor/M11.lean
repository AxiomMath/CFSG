module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM11
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofThreeFive

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint

theorem threeFiveData228_M11 :
    ThreeFiveData228 (NativeSporadic.Carrier .M11) := by
  intro x k hx hk hxk
  exfalso
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hcard := Item434SporM11.card_centralizer_eq (x := x) hx3 hx1
  have hkC : k ∈ Subgroup.centralizer ({x} : Set (NativeSporadic.Carrier .M11)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxk.symm
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set (NativeSporadic.Carrier .M11))) := by
    have := orderOf_dvd_natCard (⟨k, hkC⟩ : Subgroup.centralizer ({x} : Set _))
    rwa [Subgroup.orderOf_mk, hk] at this
  have h18 : 5 ∣ 18 := by rw [← hcard]; exact h5
  omega

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
