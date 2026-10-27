module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLayerStandardCore
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotExceptional
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotClassical
public import CFSG.LocalAnalysis.ComponentInitial.J4CommutingFactors
public import CFSG.Sporadic.SmallOddCore.MathieuJankoBlock
public import CFSG.Sporadic.SmallOddCore.J2Block
public import CFSG.Sporadic.SmallOddCore.McLBlock
public import CFSG.Sporadic.SmallOddCore.Co3Block
public import CFSG.Sporadic.Schreier.RuBlock
public import CFSG.Sporadic.SuzOddCore.Block
public import CFSG.Sporadic.ONOddCore.Block
public import CFSG.Sporadic.Co2Schreier.Components
public import CFSG.Sporadic.FischerOddCore.Fi22Block
public import CFSG.Sporadic.FischerOddCore.Fi23Block
public import CFSG.Sporadic.Schreier.LyBlock

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint

@[expose] def CommutingBlockOvergroupExclusion (X : Type) [Group X] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J : Subgroup G), CFSG.Assembly.IsQuasisimple J →
    Even (Nat.card J) → IsUniversalComponent J → (block J).Nontrivial → ∀ L : Subgroup G,
    CFSG.Assembly.IsQuasisimple L → blockGroup J ≤ L →
    ¬ L ≤ normalizer (blockGroup J : Set G) → ¬ Nonempty (L ⧸ center L ≃* X)

theorem not_nonempty_mulEquiv_j4_of_block {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hML : blockGroup J ≤ L) : ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.J4) := by
  rintro ⟨e⟩
  obtain ⟨K, ⟨⟨g, rfl⟩, hcr⟩, hne⟩ := hΔ.exists_ne J
  have hcomm : ⁅J, conjSub g J⁆ = ⊥ := hcr.resolve_left fun h => hne h.symm
  have hJL : J ≤ L := (le_blockGroup mem_block_self).trans hML
  have hKL : conjSub g J ≤ L := (le_blockGroup ⟨⟨g, rfl⟩, hcr⟩).trans hML
  set eK : ↥J ≃* ↥(conjSub g J) :=
    J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hqn := (AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
  have hq₁ : CFSG.Assembly.IsQuasisimple (J.subgroupOf L) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      ((isQuasisimple_congr (subgroupOfEquivOfLe hJL).symm).mp hqn)
  have hq₂ : CFSG.Assembly.IsQuasisimple ((conjSub g J).subgroupOf L) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      ((isQuasisimple_congr (eK.trans (subgroupOfEquivOfLe hKL).symm)).mp hqn)
  have hc : ⁅J.subgroupOf L, (conjSub g J).subgroupOf L⁆ = ⊥ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hJL, map_subgroupOf_eq_of_le hKL, hcomm,
      Subgroup.map_bot]
  obtain ⟨f₁, -⟩ := exists_centerQuotient_congr (subgroupOfEquivOfLe hJL)
  obtain ⟨f₂, -⟩ := exists_centerQuotient_congr ((subgroupOfEquivOfLe hKL).trans eK.symm)
  exact j4_central_quotient_excludes_equal_commuting_quasisimple_factors (A := center ↥L) le_rfl e
    ⟨_, _, hq₁, hq₂, hc, (Nat.card_congr f₁.toEquiv).trans (Nat.card_congr f₂.toEquiv).symm⟩

theorem escapingOvergroupNotCatalog_of_exclusions
    (hHS : CommutingBlockOvergroupExclusion NativeSporadic.HS)
    (hHe : CommutingBlockOvergroupExclusion NativeSporadic.He)
    (hCo1 : CommutingBlockOvergroupExclusion NativeSporadic.Co1)
    (hFi24 : CommutingBlockOvergroupExclusion NativeSporadic.Fi24prime)
    (hHN : CommutingBlockOvergroupExclusion NativeSporadic.HN)
    (hTh : CommutingBlockOvergroupExclusion NativeSporadic.Th)
    (hB : CommutingBlockOvergroupExclusion NativeSporadic.B)
    (hM : CommutingBlockOvergroupExclusion NativeSporadic.M) : EscapingOvergroupNotCatalog := by
  intro G _ _ J hq heven hV hJ hΔ L hL hML hLH hcat
  classical
  obtain ⟨-, -, x, y, hxy⟩ := (AssemblyBPredicates.isQuasisimple_iff_native _).mp hL
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hex | ⟨s, ⟨e⟩⟩
  ·
    apply hxy
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact (commuting_block_escaping_quasisimple_overgroup_not_alternating hq heven hJ hΔ hL hML
      hLH).2.2 (Fin n) (by simpa using hn) ⟨e⟩
  · exact commuting_block_escaping_overgroup_not_classical hq heven hV hJ hΔ hL hML hLH hcl
  · exact commuting_block_escaping_overgroup_not_exceptional hq heven hV hJ hΔ hL hML hLH hex
  · have hMJ := Sporadic.SmallOddCore.commuting_block_mathieu_j1_j3_overgroup_exclusion hq heven
      hJ hΔ hML
    cases s with
    | M11 => exact hMJ.1 ⟨e⟩
    | M12 => exact hMJ.2.1 ⟨e⟩
    | M22 => exact hMJ.2.2.1 ⟨e⟩
    | M23 => exact hMJ.2.2.2.1 ⟨e⟩
    | M24 => exact hMJ.2.2.2.2.1 ⟨e⟩
    | J1 => exact hMJ.2.2.2.2.2.1 ⟨e⟩
    | J3 => exact hMJ.2.2.2.2.2.2 ⟨e⟩
    | J2 =>
      exact Sporadic.SmallOddCore.commuting_block_j2_overgroup_exclusion hq heven hJ hΔ hL hML
        hLH ⟨e⟩
    | J4 => exact not_nonempty_mulEquiv_j4_of_block hq hΔ hML ⟨e⟩
    | Co1 => exact hCo1 G J hq heven hJ hΔ L hL hML hLH ⟨e⟩
    | Co2 =>
      exact Sporadic.Co2Schreier.commuting_block_co2_overgroup_exclusion hq heven hJ hΔ hL hML
        hLH ⟨e⟩
    | Co3 =>
      exact Sporadic.SmallOddCore.commuting_block_co3_overgroup_exclusion hq heven hV hJ hΔ hL
        hML hLH ⟨e⟩
    | Fi22 =>
      exact Sporadic.FischerOddCore.CTI_commuting_block_Fi22_overgroup_exclusion hq heven hJ hΔ
        hL hML hLH ⟨e⟩
    | Fi23 =>
      exact Sporadic.FischerOddCore.CTI_commuting_block_Fi23_overgroup_exclusion hq heven hJ hΔ
        hL hML hLH ⟨e⟩
    | Fi24Prime => exact hFi24 G J hq heven hJ hΔ L hL hML hLH ⟨e⟩
    | HS => exact hHS G J hq heven hJ hΔ L hL hML hLH ⟨e⟩
    | McL =>
      exact Sporadic.SmallOddCore.commuting_block_mcl_overgroup_exclusion hq heven hV hJ hΔ hL
        hML hLH ⟨e⟩
    | He => exact hHe G J hq heven hJ hΔ L hL hML hLH ⟨e⟩
    | Ru =>
      exact Sporadic.RuSchreier.commuting_block_ru_overgroup_exclusion hq heven hJ hΔ hL hML
        hLH ⟨e⟩
    | Suz =>
      exact Sporadic.SuzOddCore.commuting_block_suz_overgroup_exclusion hq heven hJ hΔ hL hML
        hLH ⟨e⟩
    | ONan =>
      exact Sporadic.ONOddCore.cti_commuting_block_on_overgroup_exclusion hq heven hJ hΔ hL hML
        hLH ⟨e⟩
    | HN => exact hHN G J hq heven hJ hΔ L hL hML hLH ⟨e⟩
    | Ly =>
      exact Sporadic.LySchreier.commuting_block_ly_overgroup_exclusion hq heven hJ hΔ hL hML
        hLH ⟨e⟩
    | Th => exact hTh G J hq heven hJ hΔ L hL hML hLH ⟨e⟩
    | B => exact hB G J hq heven hJ hΔ L hL hML hLH ⟨e⟩
    | M => exact hM G J hq heven hJ hΔ L hL hML hLH ⟨e⟩

theorem layerGeneratedUniversalComponentStandard_of_exclusions
    (hHS : CommutingBlockOvergroupExclusion NativeSporadic.HS)
    (hHe : CommutingBlockOvergroupExclusion NativeSporadic.He)
    (hCo1 : CommutingBlockOvergroupExclusion NativeSporadic.Co1)
    (hFi24 : CommutingBlockOvergroupExclusion NativeSporadic.Fi24prime)
    (hHN : CommutingBlockOvergroupExclusion NativeSporadic.HN)
    (hTh : CommutingBlockOvergroupExclusion NativeSporadic.Th)
    (hB : CommutingBlockOvergroupExclusion NativeSporadic.B)
    (hM : CommutingBlockOvergroupExclusion NativeSporadic.M) :
    LayerGeneratedUniversalComponentStandard :=
  layerGeneratedUniversalComponentStandard_of_escapingOvergroupNotCatalog
    (escapingOvergroupNotCatalog_of_exclusions hHS hHe hCo1 hFi24 hHN hTh hB hM)

end CFSG.ComponentClassification.UnbalancedCorr
