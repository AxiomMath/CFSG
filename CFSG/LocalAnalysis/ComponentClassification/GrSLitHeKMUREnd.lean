module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKIMain

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKMUR

variable {X : Type} [Group X] [Finite X]

theorem heldKNormalAt_of_isPComponent
    {L : Subgroup X} (hset : HeldEndSetting X L) {n : X} (hn : HeldTwoA L n)
    (hKp : IsPComponent 2 ((gsFixedLayer L n).subgroupOf (centralizer ({n} : Set X))))
    (hc : ∀ x ∈ (pPrimeCore 2 ↥(gsFixedLayer L n)).map (gsFixedLayer L n).subtype,
      ∀ m ∈ gsFixedLayer L n, x * m = m * x) :
    HeldKNormalAt L := by
  obtain ⟨-, -, -, ⟨eL⟩, -⟩ := id hset
  have hKn : gsFixedLayer L n ≤ centralizer ({n} : Set X) :=
    (gsFixedLayer_le_inf L n).trans inf_le_right
  have hq : IsQuasisimple ↥(gsFixedLayer L n) := LocalCores.isQuasisimple_of_mulEquiv
    (subgroupOfEquivOfLe hKn) (HeUC.isComponent_of_central hKn hKp hc).1
  intro v hv
  obtain ⟨l, hlL, hvl⟩ := heldTwoAClassFact X L ⟨eL⟩ n v hn hv
  have hLl : L.map (MulAut.conj l).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hlL)
  have hmap := GSLit.map_gsFixedLayer (MulAut.conj l) L n
  rw [hLl, MulAut.conj_apply, ← hvl] at hmap
  obtain ⟨-, hp⟩ := GSLit.isPComponent_map_centralizer (MulAut.conj l) hKn hKp
  rw [hmap, MulAut.conj_apply, ← hvl] at hp
  obtain ⟨-, -, hsub, -⟩ := hp
  have hKv : gsFixedLayer L v ≤ centralizer ({v} : Set X) :=
    (gsFixedLayer_le_inf L v).trans inf_le_right
  have hqv : IsQuasisimple ↥(gsFixedLayer L v) :=
    LocalCores.isQuasisimple_of_mulEquiv (((gsFixedLayer L n).equivMapOfInjective _
      (MulAut.conj l).injective).trans (MulEquiv.subgroupCongr hmap)) hq
  exact heldKNormalFromComponent_of_inputs heldKInvariantComponentStep X L hset v hv
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKv).symm hqv, hsub⟩

theorem false_of_isPComponent
    {L : Subgroup X} (hset : HeldEndSetting X L) {n : X} (hn : HeldTwoA L n)
    (hKp : IsPComponent 2 ((gsFixedLayer L n).subgroupOf (centralizer ({n} : Set X))))
    (hc : ∀ x ∈ (pPrimeCore 2 ↥(gsFixedLayer L n)).map (gsFixedLayer L n).subtype,
      ∀ m ∈ gsFixedLayer L n, x * m = m * x) : False := by
  have hKN := heldKNormalAt_of_isPComponent hset hn hKp hc
  have hB := heldTwoBCentralizerFact_of_model HeGS.heldTwoBTwelveModel
  have hFour := heldTwoAFourFact_of_model HeGS.heldTwoAFourModel
  have h36 : ∀ v ∈ L, orderOf v = 2 → ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({v} : Set X) →
      (K₁.subgroupOf (centralizer ({v} : Set X))).Normal →
      (∃ u : X, HeldTwoA L u ∧ Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u))) → HeldTwoA L v :=
    fun _ hvL hv _ h1 h2 h3 => heldLemma36 hB heldTwoALayerFact hFour hset hKN hvL hv h1 h2 h3
  exact heldZStarEndStep_of_facts heldOuterSolvableFact heldInvolAutFact heldTwoAKFact heldTwoBFact
      heldSylowFourFact heldTwoALayerFact (heldTwoAFourFact_of_model HeGS.heldTwoAFourModel)
      (heldTwoBCentralizerFact_of_model HeGS.heldTwoBTwelveModel)
      (heldTwoAPairFact_of_model HeGS.heldTwoAPairModel)
      (heldTwoAGenerationFact_of_model HeGS.heldTwoAGenerationModel) X L hset (fun u hu => hKN u hu) h36 fun _ hu =>
    heldCor37 heldTwoAClassFact (heldTwoAPairFact_of_model HeGS.heldTwoAPairModel)
      (heldTwoAGenerationFact_of_model HeGS.heldTwoAGenerationModel) hset hKN h36 hu

end HeKMUR

end CFSG.ComponentClassification.GrSLit
