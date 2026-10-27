module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrModel
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

@[expose] def Asc82OmegaPlusProjInner : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate), Module.finrank (ZMod 3) V = 8 →
      quadSign Q = 1 → ∀ y : omegaGroup hQ, (y : OGroup Q) * y = piOrth Q →
        InnerData (omegaProj hQ) (omegaToProj hQ y)

theorem oddCentralCover_quotient_oddCore {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple Y) {P : Type} [Group P] (e : Y ⧸ oddCore Y ≃* P) :
    OddCentralCover (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore Y))) := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore Y))).ker = oddCore Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hcen : oddCore Y ≤ Subgroup.center Y :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple
      (⟨hq.1.commutator_eq_top, hq.2.1⟩ : CFSG.Open.IsQuasisimple Y)
  refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · rw [hker]
    exact hcen
  · rw [hker]
    exact odd_card_oddCore

theorem asc82OmegaPlusInner_of_projInner (hproj : Asc82OmegaPlusProjInner) :
    Asc82OmegaPlusInner := by
  intro G _ _ Y hY w hw hwY hnp
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hσ, ⟨e⟩⟩ := isOmegaStar_of_lieModel_plus hY.2
  letI := i1
  letI := i2
  letI := i3
  have hρ := oddCentralCover_quotient_oddCore hY.1.1 e
  have hw' : (⟨w, hwY⟩ : ↥Y) * ⟨w, hwY⟩ = 1 := by
    apply Subtype.ext
    change w * w = 1
    rw [← pow_two]
    exact hw ▸ pow_orderOf_eq_one w
  have hdata : InnerData (omegaProj hQ)
      ((e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥Y))) ⟨w, hwY⟩) := by
    refine innerData_omegaProj_of_not_pocketed hQ hdim hσ (hproj V Q hQ hdim hσ) ?_ ?_ ?_
    · rw [← map_mul, hw', map_one]
    · intro h1
      have h2 := hρ.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) hw'
      have h3 : w = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at hw
      exact absurd hw (by decide)
    · intro h
      have h1 := isI4PlusIn_top_map_mulEquiv e.symm h
      have h2 : e.symm ((e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥Y))) ⟨w, hwY⟩) =
          QuotientGroup.mk (⟨w, hwY⟩ : ↥Y) := e.symm_apply_apply _
      rw [h2] at h1
      exact hnp (isI4PlusIn_of_quotient hwY hw h1)
  exact exists_inner_of_innerData Y _ hρ hwY hw hdata

end CFSG.OddStandard.SmallF3.Omega
