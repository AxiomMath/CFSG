module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntriesCriteria
public import CFSG.LieType.Ree.FixedSubgroupData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
import CFSG.CharacterTheory.Semidihedral.FixedFieldData
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
import CFSG.RankThree.PartOne.K159.AutTitsIso
public import CFSG.LieType.Ree.ReeHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne.K159 (AutWitness)

theorem not_smallAutomizer_tits
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : ¬ SmallAutomizer 5 K := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .tits := hd
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact not_smallAutomizer_of_autWitness
    (CFSG.RankThree.PartOne.K159.autWitness_of_isoLie_tits ⟨hv, ⟨e⟩⟩)

theorem autWitness_reeGamma
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    AutWitness 5 (ReeTag.F4.reeGamma K 2) := by
  obtain ⟨σ, -, hσ, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
      2 5 Nat.prime_two (by norm_num) K (by simpa using hK)
  have hk := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by norm_num : 1 ≤ 5) (by simpa using hK) σ).2
  rw [hσ] at hk
  have hk1 : Nat.card (fixSubfield σ) = 2 ^ 1 := by simpa using hk
  have hfix := CFSG.SignalizerFunctorTheorem.CatalogBridge.fixed_reeGamma_F4_eq_map
    (a := 2) (b := 0) (d := 1) (m := 2) σ hk1 (by norm_num)
  have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hk1
  haveI : Fact (Nat.card (fixSubfield σ) = 2) := ⟨hk2⟩
  let D := commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0)
  let e₁ := ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0
  let φ := (baseChangeGL (fixSubfield σ).subtype).comp
    ((ReeTag.F4.reeGamma (fixSubfield σ) 0).subtype.comp (e₁.toMonoidHom.comp D.subtype))
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective _).comp (Subtype.val_injective.comp
      (e₁.injective.comp Subtype.val_injective))
  have hmem : ∀ x, φ x ∈ ReeTag.F4.reeGamma K 2 := by
    intro x
    have h1 : φ x ∈ (ReeTag.F4.reeGamma (fixSubfield σ) 0).map
        (baseChangeGL (fixSubfield σ).subtype) := ⟨_, (e₁ x).2, rfl⟩
    rw [← hfix] at h1
    obtain ⟨γ, -, hγ⟩ := h1
    rw [← hγ]
    exact γ.2
  let ψ := φ.codRestrict _ hmem
  have hψinj : Function.Injective ψ := fun a b h => hφinj (congrArg Subtype.val h)
  have hD : AutWitness 5 D :=
    CFSG.RankThree.PartOne.K159.autWitness_titsD.of_mulEquiv
      (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := fixSubfield σ)).symm
  exact autWitness_of_injective ψ hψinj hD

theorem not_smallAutomizer_reeFFour
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : ¬ SmallAutomizer 5 S := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hX := CFSG.AGLEmbedding.reeTitsModel_of_catGroup_reeF4 hd
  obtain ⟨a, K, _, _, _, -, hfa, hK, ⟨f⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX
  obtain rfl : a = 2 := by omega
  exact not_smallAutomizer_of_autWitness ((autWitness_reeGamma hK).of_mulEquiv (e.trans f).symm)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
