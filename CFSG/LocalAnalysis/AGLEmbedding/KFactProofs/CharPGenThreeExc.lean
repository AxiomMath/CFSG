module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieExc
import all CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieExc

public section

namespace CFSG.AGLEmbedding.CharPGenThree

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.AGLEmbedding.CharPGen

section Certified


theorem three_le_pRank_posUnipotentExcept_modelUniv {t : StatedLieTag}
    (htag : t ∈ chevalleyExceptionalTags) (p f : ℕ) (hp : p.Prime)
    [Finite (modelUniv t 0 p f hp).K]
    {nn : Fin (modelUniv t 0 p f hp).D.rank → (modelUniv t 0 p f hp).K}
    {H : Fin (modelUniv t 0 p f hp).D.rank → Subgroup (modelUniv t 0 p f hp).K}
    (hext : SteinbergExtras (modelUniv t 0 p f hp).D nn H)
    (hX : ∀ γ ∈ (modelUniv t 0 p f hp).D.roots,
      IsPGroup p ((modelUniv t 0 p f hp).D.rootGroup γ))
    (hD : (modelUniv t 0 p f hp).D.divisible = ∅) :
    ∀ i, 3 ≤ Open.pRank p (posUnipotentExcept (modelUniv t 0 p f hp).D i) := by
  obtain ⟨M, k, hk, hMk, hM, h3⟩ :=
    CFSG.AGLEmbedding.P1Lie.heightData_modelUniv htag p f hp
  exact fun i => three_le_pRank_of_heights hext hp hX hD hk hMk hM h3 i

theorem exists_pGroup_glbCore_of_chevalleyExceptionalModel {t : StatedLieTag}
    (htag : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t 0 p f) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hmodel : ChevalleyExceptionalModel X t p f) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBCore p 3 P = ⊤ := by
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at htag
    rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have h1 : ¬ (t = .PSL ∧ 0 = 2) := fun h => absurd h.2 (by decide)
  have h2 : ¬ (t = .PSU ∧ 0 = 3) := fun h => absurd h.2 (by decide)
  have h3 : ¬ (t = .PSU ∧ ¬ Even 0) := fun h => by
    obtain ⟨rfl, -⟩ := h
    simp [chevalleyExceptionalTags] at htag
  have hX : LieModel X t 0 p f := Or.inr (Or.inl ⟨rfl, htag, hmodel⟩)
  have : Finite (modelUniv t 0 p f hp).K := finite_modelUniv hp2 hp hfund hadm
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t 0 p f hp hp2
    hfund hadm X hX
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum t 0 p f hp hfund hadm
  have hXp := CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv t 0 p f hp hfund hadm
  have hrank := two_le_rank t 0 p f hp hfund hadm h1 h2
  exact exists_pGroup_glbCore_of_central_cover hp hct hext (by omega) hXp
    (CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t 0 p f hp hp2 hfund hadm)
    ψ hψs hψk
    (three_le_pRank_posUnipotentExcept_modelUniv htag p f hp hext hXp
      (CFSG.LieType.HighestRoot.divisible_modelUniv t 0 p f hp hfund hadm h3))

end Certified

end CFSG.AGLEmbedding.CharPGenThree

namespace CFSG.AGLEmbedding

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.CharPGenThree

section Certified


theorem charPGen3At_exceptional : CharPGen3At IsExceptionalIndex := by
  intro K _ _ _ _ d hd ⟨e⟩ p hp hp2 hchar hrank T
  suffices h : ∃ P : Subgroup K, IsPGroup p P ∧ GLBCore p 3 P = ⊤ by
    obtain ⟨P, hP, hcore⟩ := h
    exact CFSG.AGLEmbeddingD2.glbCore_eq_top_of_pGroup hp 3 hP hcore T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ <;>
    simp only at hd hchar <;> subst hd <;> (have hpq : p = q.p := by simpa using hchar) <;>
    subst hpq
  · have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
    have hadm : StatedLieAdmissible .G2 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl, h3⟩
    exact exists_pGroup_glbCore_of_chevalleyExceptionalModel (t := .G2) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .F4 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_glbCore_of_chevalleyExceptionalModel (t := .F4) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E6 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_glbCore_of_chevalleyExceptionalModel (t := .E6) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E7 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_glbCore_of_chevalleyExceptionalModel (t := .E7) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E8 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_glbCore_of_chevalleyExceptionalModel (t := .E8) (by decide) q.prime_p
      hp2 hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .twistedE6 0 q.p q.exponent :=
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_glbCore_of_chevalleyExceptionalModel (t := .twistedE6) (by decide)
      q.prime_p hp2 hadm ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv hp2 (by decide) e⟩
  · have hadm : StatedLieAdmissible .trialityD4 0 q.p q.exponent :=
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup_glbCore_of_chevalleyExceptionalModel (t := .trialityD4) (by decide)
      q.prime_p hp2 hadm ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hp2 (by decide) e⟩

end Certified

end CFSG.AGLEmbedding
