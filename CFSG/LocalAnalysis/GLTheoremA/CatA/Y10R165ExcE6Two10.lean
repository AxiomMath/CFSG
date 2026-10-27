module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open CFSG.Open CFSG.LieType.Steinberg.Minuscule


theorem e6TwoModel165At_two_three (F : Type) [Field F] [Finite F] [CharP F 2] (n q : ℕ)
    (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (hrk : rk2Ord 3 n = 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) :
    letI : Finite ↥(e6Data_valid.minGroup F) :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
    ∀ Ã : Subgroup ↥(e6Data_valid.minGroup F), IsElemAbelian 3 Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(e6Data_valid.minGroup F)),
        orderOf g = 3 → g ∈ Ã) →
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤
        CFSG.Open.pRank 3 Ã →
      3 ≤ CFSG.Open.pRank 3 Ã →
      Concl165Avoid ↥(e6Data_valid.minGroup F) 3 q Ã
        (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  have h3 : 3 ∣ Nat.card F + 1 := by
    rw [hcard]
    exact (rk2Ord_eq_two_iff Nat.prime_three (by norm_num)).mp hrk
  exact e6TwoModel165At_two_of_rankConj F n 3 q hcard hn Nat.prime_three (by norm_num) hrk
    hq hq2 hq3 hqdiv (fun E hE => card_le_of_isElemAbelian_E6_three h3 hE)
    (fun A A₀ hA hAc hA₀ hA₀c => exists_conj_eq_of_card_E6_three h3 hA hAc hA₀ hA₀c)
    e6TwoLayerData_holds e6TwoFData_holds

theorem e6Model165At_two : E6Model165At 2 := by
  intro F hField hFinite hChar n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  by_cases hp3 : p = 3
  · subst hp3
    exact e6TwoModel165At_two_three F n q hcard hn hrk hq hq2 hqp hqdiv
  · exact e6TwoModel165At_two (F := F) n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv hp3
      e6TwoLayerData_holds e6TwoFData_holds

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
