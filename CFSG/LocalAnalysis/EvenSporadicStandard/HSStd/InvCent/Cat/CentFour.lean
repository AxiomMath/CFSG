module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.Dihedral.GorensteinWalter
import CFSG.Goldschmidt.Steps.G3bL2
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.CentFour.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

theorem catCentFour_holds :
    CatCentFour := by
  intro S _ _ hS hna _hcat V hV hC
  haveI := hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := CentFour.exists_sylow_eq hV hC
  have hK : IsKleinFour (P : Subgroup S) :=
    CentFour.isKleinFour_of_not_isCyclic hV (CentFour.not_isCyclic_sylow_of_card_four hna P hV)
  obtain ⟨e⟩ : Nonempty ((P : Subgroup S) ≃* DihedralGroup 2) := IsKleinFour.nonempty_mulEquiv
  rcases CFSG.GorensteinWalter.gorenstein_walter S hna P ⟨2, ⟨e⟩⟩ with
    ⟨⟨e7⟩⟩ | ⟨p, k, hp, hodd, h5, ⟨eL⟩⟩
  ·
    exfalso
    have hcard : Nat.card S = 2520 := by
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hmult : 2 ^ (Nat.card S).factorization 2 = 4 := P.card_eq_multiplicity.symm.trans hV
    rw [hcard] at hmult
    have h3 : 3 ≤ (2520 : ℕ).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mp (by norm_num)
    have h8 : 2 ^ 3 ≤ 2 ^ (2520 : ℕ).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3
    omega
  ·
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h5
      · exact hk
    haveI : Nontrivial (P : Subgroup S) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; norm_num)
    obtain ⟨⟨w, hwP⟩, hw1⟩ := exists_ne (1 : (P : Subgroup S))
    have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hw2 : orderOf w = 2 := by
      refine orderOf_eq_prime ?_ hw1'
      rw [pow_two]
      exact congrArg Subtype.val (IsKleinFour.mul_self (G := (P : Subgroup S)) ⟨w, hwP⟩)
    obtain ⟨h1, h3⟩ := CFSG.Goldschmidt.G3b.centralizer_dihedral_of_mulEquiv eL hodd hk hw2
    have hcent : Nat.card (centralizer ({w} : Set S)) = 4 := by
      rw [hC w hwP hw1']
      exact hV
    have hmod : p ^ k % 4 = 1 ∨ p ^ k % 4 = 3 := by
      obtain ⟨m, hm⟩ := hodd.pow (n := k)
      omega
    have hq5 : p ^ k = 5 := by
      rcases hmod with hm | hm
      · obtain ⟨f⟩ := h1 hm
        haveI : NeZero ((p ^ k - 1) / 2) := ⟨by omega⟩
        have := Nat.card_congr f.toEquiv
        rw [hcent, DihedralGroup.nat_card] at this
        omega
      · obtain ⟨f⟩ := h3 hm
        have := Nat.card_congr f.toEquiv
        rw [hcent, DihedralGroup.nat_card] at this
        omega
    exact (CFSG.Goldschmidt.G3b.five_facts_of_mulEquiv eL hodd hk hq5 P hwP hw1').1

end CFSG.EvenSporadicStandard.HSStd.InvCent
