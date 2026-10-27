module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketSix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fg_pocket_P : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ z : G, z ∈ L → (IsI4PlusIn L z ↔ orderOf z = 2 ∧ InducesTypeSome L z 6 1 4 1) := by
  intro G _ _ L hL z hz
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hs⟩ := ff_exists_model_six_plus hL
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [ff_center_eq_oddCore_six_plus hL]
    exact ff_odd_card_oddCore ↥L
  constructor
  · intro hI
    have hz2 := hI.1
    have hP : IsI4PlusIn (⊤ : Subgroup ↥(omegaProj hQ)) (ff6mPhi e ⟨z, hz⟩) :=
      (fg_isI4PlusIn_iff_of_cover (ff6m_phi_cover e hodd) hz hz2).mp hI
    exact ⟨hz2, V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
      projOrthToProjSim Q ((ff6mPhi e ⟨z, hz⟩ : ↥(omegaProj hQ)) : ProjOrth Q), hdim, hs,
      ff6m_induces_of_mem hQ e hz, _, rfl,
      fg_hasType_of_isI4PlusIn_top_six_plus hQ hdim hs hP⟩
  · rintro ⟨hz2, V', _, _, _, Q', hQ', e', x', hdim', hs', hind, y, hy, hT⟩
    have hxu := ff_induces_unique hQ' (by omega) e' hind (ff6m_induces_of_mem hQ' e' hz)
    have hy' : y = ((ff6mPhi e' ⟨z, hz⟩ : ↥(omegaProj hQ')) : ProjOrth Q') :=
      projOrthToProjSim_injective (hy.trans hxu)
    rw [hy'] at hT
    exact (fg_isI4PlusIn_iff_of_cover (ff6m_phi_cover e' hodd) hz hz2).mpr
      (fg_isI4PlusIn_top_of_hasType_six_plus hQ' hdim' hs' hT)

end CFSG.OddStandard.SmallF3.Omega
