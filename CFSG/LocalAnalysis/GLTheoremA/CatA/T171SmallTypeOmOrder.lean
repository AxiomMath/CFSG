module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer
public import CFSG.LargeExtraspecial.A2ModOrdCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.LieType.Universal.Spin

theorem zmod_two_no_root (b c : ZMod 2) (h : ∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) :
    b = 1 ∧ c = 1 := by
  revert b c
  decide

theorem zmod_two_poly_one (s : ZMod 2) : s ^ 2 + 1 * s + 1 ≠ 0 := by
  revert s
  decide

theorem card_orthDerived_plus_six {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 3)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card ↥(orthDerived Q) = 20160 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ hdim hplus
  have hcard : Nat.card ↥(orthDerived Q) =
      Nat.card ↥(orthDerived (quadPlus 3 (ZMod 2))) :=
    Nat.card_congr (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr e).toEquiv
  rw [hcard]
  have eΩ := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadPlus 3 (ZMod 2)) (CFSG.LieType.Universal.Spin.coe_quadPlus 3 (ZMod 2))
  rw [← Nat.card_congr eΩ.toEquiv]
  exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.card_statedOmega_quadPlus_three

theorem card_orthDerived_plus_eight {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card ↥(orthDerived Q) = CFSG.Open.ordD 4 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ hdim hplus
  let φ : ↥(orthDerived Q) ≃*
      ↥(orthDerived (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus
        4 (ZMod 2))) :=
    (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr e).trans
      (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusIsometry
          4 (ZMod 2)))
  have hLM := CFSG.SeitzReduction.OmegaPilot.lieModel_of_mulEquiv_orthDerived_plus
    (m := 4) (f := 1) (by norm_num) (by norm_num) (by norm_num) φ
  exact (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_POmegaPlus hLM).2

theorem seven_dvd_card_orthDerived_plus_eight {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    7 ∣ Nat.card ↥(orthDerived Q) := by
  rw [card_orthDerived_plus_eight hQ hdim hplus, CFSG.Open.ordD]
  norm_num
  decide

theorem card_orthDerived_minus_eight {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card ↥(orthDerived Q) = CFSG.Open.ordTwistedD 4 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hno : ¬ Nonempty (Q.IsometryEquiv (quadPlus 4 (ZMod 2))) := by
    rintro ⟨e⟩
    exact hminus ((CFSG.GroupTheory.WeirSylow.isPlusType_congr e).2
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (ZMod 2) 4))
  obtain ⟨b, c, hirr, ⟨e₀⟩⟩ :=
    (CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ
      (n := 4) (by norm_num) hdim).resolve_left hno
  obtain ⟨hb, hc⟩ := zmod_two_no_root b c hirr
  subst hb
  subst hc
  let φ : ↥(orthDerived Q) ≃*
      ↥(orthDerived (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus
        4 (ZMod 2) (by omega) 1 1)) :=
    (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr e₀).trans
      (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry
          4 (ZMod 2) (by omega) 1 1))
  have hLM := CFSG.SeitzReduction.OmegaPilot.lieModel_of_mulEquiv_orthDerived_minus
    (m := 4) (f := 1) (by norm_num) (by norm_num) (by norm_num) zmod_two_poly_one φ
  exact (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_POmegaMinus hLM).2

theorem seven_dvd_card_orthDerived_minus_eight {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    7 ∣ Nat.card ↥(orthDerived Q) := by
  rw [card_orthDerived_minus_eight hQ hdim hminus, CFSG.Open.ordTwistedD]
  norm_num
  decide

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
