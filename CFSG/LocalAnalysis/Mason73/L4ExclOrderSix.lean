module

public import CFSG.LocalAnalysis.Mason73.L4SylowTransport
public import CFSG.LocalAnalysis.Mason73.L4OrderTwoPart
public import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow

variable {G : Type} [Group G] [Finite G] {n p f : ℕ}

theorem false_of_lieModel_psl_six_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hL : CFSG.Blueprint.LieModel G .PSL 6 p f)
    (hq : p ^ f % 4 = 3) : False := by
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hL.card_eq_lieOrd (by norm_num),
    show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 6 (p ^ f) = Open.ordA 5 (p ^ f) from rfl,
    factorization_two_ordA_five_of_three hq] at h2
  omega

theorem false_of_lieModel_psu_six_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hL : CFSG.Blueprint.LieModel G .PSU 6 p f)
    (hq : p ^ f % 4 = 1) : False := by
  obtain ⟨hp, hf, -⟩ := hL.admissible
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hL.card_eq_lieOrd (by norm_num),
    show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSU 6 (p ^ f) = Open.ordTwistedA 5 (p ^ f)
      from rfl,
    factorization_two_ordTwistedA_five_of_one hq (Nat.one_lt_pow (by omega) hp.one_lt)] at h2
  omega

end CFSG.LocalAnalysis.Mason73
