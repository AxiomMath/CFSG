module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Hom
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.HomCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.SetupLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.SetupPhi

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem z2s6_mod_setup {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal]
    (hC : centralizer (S : Set K) = ⊥)
    (hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S))
    {z : K} (hz : orderOf z = 2) {ψ : ↥(centralizer ({z} : Set K)) →* Z2S6}
    (hψ : ModData z (alternatingGroup (Fin 6)) ψ) :
    ∃ (σ : MulAut ↥S) (J : Subgroup ↥(fixedSubgroup σ)), Z2S6ModData ↥S σ J := by
  refine ⟨MulAut.conjNormal (H := S) z, ?_⟩
  have hodd := odd_ker_fixedPhi (S := S) (z := z) hψ.odd
  have hA := a6Factor_le_range_fixedPhi hC hsolv hψ.surj hψ.odd
  obtain ⟨J, hJn, -, hJmap, hperf, hP, hiso⟩ := exists_twoComponent _ hodd hA
  haveI := hJn
  exact ⟨J, ⟨orderOf_conjNormal_eq_two S hC hz, hJn, hP, hiso, hperf,
    ⟨(fixedPhi S z ψ).ker, inferInstance, hodd, natCard_quotient_ker_dvd _⟩,
    dvd_natCard_of_a6Factor_le_range _ hA, not_two_pow_six_dvd_natCard _ hodd,
    orderOf_ne_eight_of_odd_ker _ hodd,
    fun _ hU hUJ => natCard_le_two_of_le_centralizer _ hodd hJmap hU hUJ,
    fixed_pCore_le_center S hψ⟩⟩

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
