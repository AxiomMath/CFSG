module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SecOdd
public import CFSG.Sporadic.Co1Block.TwoBD
public import Certificates.Certificate26992

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic.Co1Block CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native


theorem g24_dihedral :
    ∃ u v : ↥twoBD, u * u = 1 ∧ v * v = 1 ∧ (u * v) ^ 4 = 1 ∧ u * v ≠ v * u := by
  have h := Certificates.certificate26992
  have hX : permOfArr 1365 G24Aut.xa = xBar := strong0_eq
  have hY : permOfArr 1365 G24Aut.ya = yBar := strong1_eq
  rw [hX, hY] at h
  obtain ⟨u, hu, v, hv, hu2, hv2, huv, hne⟩ := h
  refine ⟨⟨u, hu⟩, ⟨v, hv⟩, Subtype.ext hu2, Subtype.ext hv2, Subtype.ext ?_,
    fun h => hne (congrArg Subtype.val h)⟩
  rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
  exact huv

theorem sylowNonabelian_twoBD : SylowNonabelian ↥twoBD := by
  obtain ⟨u, v, hu, hv, huv, hne⟩ := g24_dihedral
  have : Finite ↥twoBD := inferInstance
  exact sylowNonabelian_of_dihedral hu hv huv hne

end CFSG.EvenSporadicStandard.Induction
