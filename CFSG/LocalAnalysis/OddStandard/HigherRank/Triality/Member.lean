module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.ClassicalMember
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Triality.ShortMember

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Generic (modelUniv)

section


theorem exists_isClassicalMember_of_trialityD4 {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) .trialityD4 0 p e) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ (J : Subgroup L) (u : L),
      CFSG.ClassicalInvolution.Generic.IsClassicalMember p (3 * e) J u ∧
        u ∉ Subgroup.center L := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (L ⧸ center L) := hq.2
  have hadm : StatedLieAdmissible .trialityD4 0 p e := ⟨hp, he, rfl⟩
  haveI : Finite (modelUniv .trialityD4 0 p e hp).K :=
    ModelFacts.finite_modelUniv hp2 hp trivial hadm
  obtain ⟨ψ, hψ, hker⟩ := Upgrade.lieModelCentralCover .trialityD4 0 p e hp hp2 trivial hadm
    (L ⧸ center L) hm
  obtain ⟨J, z, hJ, hz⟩ := exists_isClassicalMember_cube (p := p) (e := e) hp2 he
  have hψz : ψ z ≠ 1 := fun h => hz (hker h)
  have hF : Odd (Nat.card (GaloisField p (3 * e))) := by
    rw [GaloisField.card p (3 * e) (by omega)]
    exact (hp.odd_of_ne_two hp2).pow
  have hmem' := ModelFacts.isClassicalMember_map_central ψ hψ hker hF hJ hψz
  have h5 := five_le_pow_three_mul hp hp2 he
  obtain ⟨J', u, hJ', -, hu⟩ := ModelFacts.IsClassicalMember.exists_lift hp2 h5
    (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hmem'
  refine ⟨J', u, hJ', fun hc => hψz ?_⟩
  rw [← hu]
  exact (QuotientGroup.eq_one_iff u).mpr hc

theorem hasClassicalMember_of_trialityD4 {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) .trialityD4 0 p e) : HasClassicalMember L := by
  obtain ⟨J', u, hJ', hu⟩ :=
    exists_isClassicalMember_of_trialityD4 (p := p) (e := e) hp hp2 he hq hm
  exact ⟨p, 3 * e, ⟨hp⟩, hp2, five_le_pow_three_mul hp hp2 he, J', u, hJ', hu⟩

theorem trialityD43Member_holds : TrialityD43Member := fun _ _ _ hq hm =>
  hasClassicalMember_of_trialityD4 Nat.prime_three (by norm_num) le_rfl hq hm

end

end CFSG.OddStandard.HigherRank
