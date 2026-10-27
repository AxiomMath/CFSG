module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodReeF4
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits
public import CFSG.RankThree.PartOne.SEITZX.ReeSplit
public import CFSG.Quasithin.Vol2.KGFactInspOutDer
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.OutStructure CFSG.LieType.SeitzGeneration
open CFSG.LieType.Ree CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc

section Suzuki


theorem innGoodAt_suzuki {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : InnGoodAt p (.suzuki m) (Cat ⟨.suzuki m, hv⟩) := by
  refine innGoodAt_of_forall_card_ne (fun D hD hDle hcard => ?_)
  have hcomm := CFSG.RankThree.PartTwo.KFacts.KP7.commutator_le_inner (suzukiModel_cat hv)
  have hDi : D ≤ inner (Cat ⟨.suzuki m, hv⟩) := hDle.trans (sup_le le_rfl hcomm)
  exact (not_innerPlane_suzuki hv hp hp2 hD hcard hDi).elim

end Suzuki

section ReeG2


theorem innGoodAt_reeG2 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) : InnGoodAt p (.reeG2 m) (Cat ⟨.reeG2 m, hv⟩) := by
  let S := Cat ⟨.reeG2 m, hv⟩
  obtain ⟨X, _, _, _, hm1, hX, ⟨e⟩⟩ :=
    exists_reeG2_model (K := S) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  haveI : Finite (ModGL ReeTag.G2.tag X) := CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.G2.reeGamma X m) := Subtype.finite
  haveI : Finite S := Finite.of_equiv _ e.symm.toEquiv
  have hcyc : IsCyclic (Outer S) :=
    (MulEquiv.isCyclic (equivalence e)).2 (isCyclic_outer_reeG2 hm1 hX)
  have hout : OutPNice p S := outPNice_of_isCyclic_outer hp hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  refine innGoodAt_of_forall_card_ne (fun D hD hDle hcard => ?_)
  have hDi : D ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := fun β hβ =>
    mem_inner_of_mem_innAutDerived_of_outPNice hout (hDle hβ) (hD.2 β hβ)
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_mulEquiv e
      (conj_injective_of_center_eq_bot (ReeTag.center_reeGamma_G2_eq_bot hX))
  exact (false_of_inner_plane_of_no_plane hinj
    (fun F hF hFc => no_plane_cat_reeG2 hv hp hp3 F hF hFc) hD hcard hDi).elim

end ReeG2

section Tits


theorem innGoodAt_tits (hv : TauCeti.LieTypeIndex.tits.Valid) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) : InnGoodAt p .tits (Cat ⟨.tits, hv⟩) := by
  exact innGoodAt_of_forall_card_ne (fun D _ _ hcard =>
    (no_plane_tits hv hp hp2 hp3 hp5 hcard).elim)

end Tits

section ReeF4


theorem innGoodAt_reeF4 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : InnGoodAt p (.reeF4 m) (Cat ⟨.reeF4 m, hv⟩) := by
  let S := Cat ⟨.reeF4 m, hv⟩
  obtain ⟨K, _, _, _, hm1, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.SEITZX.exists_reeGamma_model (K := S)
      ⟨hv, ⟨MulEquiv.refl _⟩⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K m) := Subtype.finite
  haveI : Finite S := Finite.of_equiv _ e.symm.toEquiv
  have hZ : Subgroup.center S = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, ReeTag.large_Ree_fixed_group_center_trivial m K hK,
      Subgroup.map_bot]
  have hplanes : PerfectCentralizerPlanes p S :=
    PerfectCentralizerPlanes.of_mulEquiv e.symm
      (perfectCentralizerPlanes_reeGamma_F4 hm1 hK hp hp2)
  have hcyc : IsCyclic (Outer S) :=
    CFSG.Quasithin.H13.KGInsp4316.outer_cyclic_2f4 (reeTitsModel_cat_reeF4 hv)
  exact innGoodAt_of_outPNice hp hZ (outPNice_of_isCyclic_outer hp hcyc) hplanes (.reeF4 m)

end ReeF4

section Assembly


theorem lieInnGood_suzRee : LieInnGood suzRee := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | suzuki m => exact innGoodAt_suzuki hv hp hp2
  | reeG2 m =>
    have hchar : (⟨TauCeti.LieTypeIndex.reeG2 m, hv⟩ :
        TauCeti.ValidLieTypeIndex).1.characteristic = 3 := by
      change (TauCeti.LieTypeIndex.reeG2 m).characteristic = 3
      exact TauCeti.LieTypeIndex.characteristic_reeG2 m
    have hpne : p ≠ 3 := fun h => hpc (h.trans hchar.symm)
    have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hpne
    exact innGoodAt_reeG2 hv hp (by omega)
  | tits =>
    have hp3 : p ≠ 3 := fun h => h3 ⟨h, by simp [ov2Idx, fieldSize]⟩
    have hp5 : p ≠ 5 := fun h => h5 ⟨h, rfl⟩
    exact innGoodAt_tits hv hp hp2 hp3 hp5
  | reeF4 m => exact innGoodAt_reeF4 hv hp hp2
  | _ => exact absurd hP (by simp [suzRee])

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
