module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Fam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenExc
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Abstract

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg

theorem exists_pGroup2_of_central_cover {K X : Type} [Group K] [Finite K] [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : UniversalRootDatum K} {nn : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hext : SteinbergExtras D nn H) (hrank : 2 ≤ D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hadj : ∀ i, ∃ j, j ≠ i ∧ D.cartan i j ≠ 0)
    (hcen : ∀ z ∈ Subgroup.center K, z ^ p = 1 → z = 1) (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  have hU : IsPGroup p (posUnipotent D) := isPGroup_iSup_pos hext hX
  have hinj : ∀ x ∈ posUnipotent D, ψ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact CFSG.AGLEmbedding.CharPGen.eq_one_of_mem_center_of_pow_prime_pow hcen
      (hker (MonoidHom.mem_ker.2 hx1)) (congrArg Subtype.val hk)
  exact ⟨(posUnipotent D).map ψ, hU.map ψ,
    glbCore_map_eq_top_of_injOn hp ψ hψ hinj
      (glbCore_two_posUnipotent_eq_top hct hext hp hp2 hrank hX hadj)⟩

section Certified


theorem exists_pGroup2_of_lieModel {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p f)
    (h1 : ¬ (t = .PSL ∧ n = 2)) (h2 : ¬ (t = .PSU ∧ n = 3)) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hX : CFSG.Blueprint.LieModel X t n p f) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  have : Finite (CFSG.ClassicalInvolution.ModelFacts.modelUniv t n p f hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp hfund hadm
  obtain ⟨ψ, hψs, hψk⟩ :=
    CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t n p f hp hp2 hfund hadm X hX
  obtain ⟨nn, H, hct, hext⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum t n p f hp hfund hadm
  have hrank := CFSG.ClassicalInvolution.ModelFacts.two_le_rank t n p f hp hfund hadm h1 h2
  exact exists_pGroup2_of_central_cover hp hp2 hct hext hrank
    (CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv t n p f hp hfund hadm)
    (exists_adj_of_isIrreducible
      (CFSG.ClassicalInvolution.ModelFacts.cartanOK t n p f hp hfund hadm).irreducible hrank)
    (CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t n p f hp hp2 hfund hadm)
    ψ hψs hψk

theorem exists_pGroup2_of_chevalleyExceptionalModel {t : StatedLieTag}
    (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t 0 p f) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel X t p f) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    simp only [CFSG.Blueprint.chevalleyExceptionalTags, Finset.mem_insert,
      Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  exact exists_pGroup2_of_lieModel hp hp2 hfund hadm (fun h => absurd h.2 (by decide))
    (fun h => absurd h.2 (by decide)) (Or.inr (Or.inl ⟨rfl, ht, hmodel⟩))

theorem charPGen2At_exceptional : CharPGen2At CFSG.AGLEmbedding.IsExceptionalIndex := by
  refine charPGen2At_of_pGroup_simple ?_
  intro K _ _ _ d hd e p hp hp2 hchar
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd⟩ <;>
    simp only at hd hchar <;> subst hd <;> (have hpq : p = q.p := by simpa using hchar) <;>
    subst hpq
  · have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
    have hadm : StatedLieAdmissible .G2 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl, h3⟩
    exact exists_pGroup2_of_chevalleyExceptionalModel (t := .G2) (by decide) q.prime_p hp2
      hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .F4 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup2_of_chevalleyExceptionalModel (t := .F4) (by decide) q.prime_p hp2
      hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E6 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup2_of_chevalleyExceptionalModel (t := .E6) (by decide) q.prime_p hp2
      hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E7 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup2_of_chevalleyExceptionalModel (t := .E7) (by decide) q.prime_p hp2
      hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .E8 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup2_of_chevalleyExceptionalModel (t := .E8) (by decide) q.prime_p hp2
      hadm ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hp2 e⟩
  · have hadm : StatedLieAdmissible .twistedE6 0 q.p q.exponent :=
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup2_of_chevalleyExceptionalModel (t := .twistedE6) (by decide)
      q.prime_p hp2 hadm ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv hp2 (by decide) e⟩
  · have hadm : StatedLieAdmissible .trialityD4 0 q.p q.exponent :=
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    exact exists_pGroup2_of_chevalleyExceptionalModel (t := .trialityD4) (by decide)
      q.prime_p hp2 hadm ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hp2 (by decide) e⟩

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314
