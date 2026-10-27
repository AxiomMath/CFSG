module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Classical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTParamMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank
open TauCeti (PrimePower LieTypeIndex)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_sp6_omegaMinus8 {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ φ : StatedSp 3 F →* StatedOmega (StatedQuadMinus 4 F b c), Function.Injective φ := by
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
  · have hK : Nat.card F = 2 := by rw [hF, pow_one]
    exact ⟨CFSG.SeitzReduction.SymplecticPilot.q2OmMIota (r := 3) le_rfl hirr hK,
      CFSG.SeitzReduction.SymplecticPilot.q2OmMIota_injective le_rfl hirr hK⟩
  · exact ⟨CFSG.SeitzReduction.F4Pilot.omegaMinusIota hF hf2 hirr,
      CFSG.SeitzReduction.F4Pilot.omegaMinusIota_injective hF hf2 hirr⟩

theorem witness_projOmegaMinus8 {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Witness (StatedProj (StatedOmega (StatedQuadMinus 4 F b c))) := by
  obtain ⟨φ, hφ⟩ := exists_sp6_omegaMinus8 hF hf hirr
  let π := QuotientGroup.mk' ((StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) F).subgroupOf
    (StatedOmega (StatedQuadMinus 4 F b c)))
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (CFSG.LieType.Universal.Spin.coe_quadMinus 4 F b c)
      ⟨CFSG.SeitzReduction.F4Pilot.minusVec F, by
        rw [CFSG.SeitzReduction.F4Pilot.quadMinus_minusVec]
        exact one_ne_zero⟩
  exact Sp62.witness_sp6two.map (φ := π.comp (φ.comp (Sp62.spField F)))
    (hπ.comp (hφ.comp Sp62.spField_injective))

theorem familyAt_twistedD4 (q : PrimePower) (hq : q.p = 2) : FamilyAt (.twistedD 4 q) := by
  intro hv K _ _ _ ⟨e⟩ _ hSh
  exfalso
  obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD 4 q hv e
  rw [hq] at hF
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      q.exponent_pos hF
  have hW := witness_projOmegaMinus8 hF q.exponent_pos hirr
  exact (hSh (three_dvd_of_witness e' hW)).not_witness_equiv e' hW

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev
