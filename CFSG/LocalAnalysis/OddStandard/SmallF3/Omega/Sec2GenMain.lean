module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenConn
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenTop

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82OmegaPlusGen_holds : Asc82OmegaPlusGen := by
  intro G _ _ Y hY z hz
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hσ, ⟨e⟩⟩ := isOmegaStar_of_lieModel_plus hY.2
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨hzY, f, hf, hfz⟩ := exists_quaternion_quotient_of_le (le_refl Y) hz
  obtain ⟨y, hyy, hty, hωy⟩ := exists_invType_of_quaternion_omegaProj hQ hdim
    (f := e.toMonoidHom.comp f) (e.injective.comp hf)
  have hz2 : z * z = 1 := by
    rw [← pow_two]
    exact hz.1 ▸ pow_orderOf_eq_one z
  have hωz : omegaToProj hQ y = e (QuotientGroup.mk (⟨z, hzY⟩ : ↥Y)) := by
    rw [hωy]
    change e (f (QuaternionGroup.a 2)) = _
    rw [hfz]
  refine gen_of_genP Y hY.1.1 e hzY hz2 ?_
  rw [← hωz]
  exact genP_omegaProj hQ hdim hσ hyy hty

end CFSG.OddStandard.SmallF3.Omega
