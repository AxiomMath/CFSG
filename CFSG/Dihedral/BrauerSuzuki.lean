module

public import CFSG.Dihedral.BrauerSuzuki.Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.PF.AppendixII.OddCoreQuotient

public section

namespace CFSG

namespace BrauerSuzuki

theorem brauer_suzuki {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈
      Subgroup.center (G ⧸ oddCore G) := by
  have hcentral :
      QuotientGroup.mk' (pPrimeCore 2 G) t ∈
        Subgroup.center (G ⧸ pPrimeCore 2 G) :=
    BenderSuzuki.PFAppendixII.appendixII_quotient_involution_central_public P hn hquat t
      ⟨fun h => by simp [h] at ht_ord, by rw [← ht_ord]; exact pow_orderOf_eq_one t⟩
  exact BrauerSuzuki.center_mod_oddCore_of_center_mod_coprime_two
    (pPrimeCore 2 G) pPrimeCore_normal pPrimeCore_coprime_card hcentral

end BrauerSuzuki

end CFSG
