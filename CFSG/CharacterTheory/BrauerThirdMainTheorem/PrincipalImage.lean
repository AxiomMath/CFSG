module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Projection

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem brauerCorr_principal (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprime : prime.Prime) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G)) :
    BlocksBrauerCorr m subgroup overgroup (BlocksPrincipalBlock m overgroup)
      (BlocksPrincipalBlock m G) := by
  intro coefficients hcoefficients left hleft right hright
  have hleftScalar := principal_centralChar_congr m hm G hleft hcoefficients
  have haugmentation := principal_augmentation_congr m hm prime hprime hprimeMem
    subgroup overgroup hpGroup hcentralizer hcoefficients
  have hrightScalar := principal_centralChar_congr m hm overgroup hright
    (brauerProj_central m hm subgroup overgroup hnormalizer hcoefficients)
  have hnegative : BlocksCentralChar (fun _ => 1) (BlocksBrauerProj subgroup overgroup coefficients) -
      BlocksCentralChar right (BlocksBrauerProj subgroup overgroup coefficients) ∈
        BlocksLocalMaxIdeal m := by
    convert localMaxIdeal_neg m hrightScalar using 1
    ring
  exact localMaxIdeal_trans m hm (localMaxIdeal_trans m hm hleftScalar haugmentation) hnegative

end CFSG.BrauerThirdMainTheorem.Helpers
