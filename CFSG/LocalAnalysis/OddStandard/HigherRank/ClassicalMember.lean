module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModel
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.HighestRoot CFSG.ClassicalInvolution
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoOddLie
open CFSG.ClassicalInvolution.Generic (modelUniv IsFundTag IsLongestRoot IsClassicalMember)
open scoped MatrixGroups

@[expose] def HasClassicalMember (L : Type) [Group L] : Prop :=
  ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 5 ≤ p ^ f ∧
    ∃ (J : Subgroup L) (u : L), IsClassicalMember p f J u ∧ u ∉ center L

@[expose] def TrialityD43Member : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Blueprint.LieModel (L ⧸ center L) .trialityD4 0 3 1 → HasClassicalMember L

section


theorem exists_isClassicalMember_of_lieModel (hI : OddLieInputs) (h4 : TrialityD4SL2Unique)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) {t : StatedLieTag}
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hfund : IsFundTag t) (hne : ¬ (t = .PSL ∧ n = 2)) (h5 : 5 ≤ p ^ f)
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) t n p f) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ (J : Subgroup L) (u : L),
      CFSG.ClassicalInvolution.Generic.IsClassicalMember p f J u ∧ u ∉ Subgroup.center L := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (L ⧸ center L) := hq.2
  have hf0 : f ≠ 0 := by
    have := hadm.2.1
    omega
  have hF : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf0]
    exact (hp.odd_of_ne_two hp2).pow
  have hne' : (t, n) ≠ (.PSL, 2) := fun h => hne (Prod.mk.inj h)
  haveI : Finite (modelUniv t n p f hp).K := ModelFacts.finite_modelUniv hp2 hp hfund hadm
  obtain ⟨γ, hγ, hdata⟩ := exists_sl2CentralizerData hI h4 hp2 hfund hadm hne'
  obtain ⟨eR⟩ := nonempty_rankOne_equiv hp2 hfund hadm hγ
  have hz2 := orderOf_centralInv eR hF
  have hzR := centralInv_mem eR
  obtain ⟨hCZ, -⟩ := hdata _ hzR hz2
  have hRC : rankOneGroup (modelUniv t n p f hp).D γ ≤
      centralizer ({centralInv eR} : Set (modelUniv t n p f hp).K) := fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (centralInv_mem_centralizer eR)) x hx
  have hmem := isClassicalMember_of_sl2 hp2 h5 eR hz2 hzR hRC hCZ
  have hznc : centralInv eR ∉ center (modelUniv t n p f hp).K := by
    intro hzc
    have h1 : centralInv eR = 1 := by
      refine ModelFacts.fundNoncentral_generic p t n f hfund hadm hne _
        ⟨1, γ, Or.inl hγ, (ModelFacts.map_conj_one _).symm⟩ _ hzR (fun y => ?_)
      rw [← Subgroup.mem_center_iff.mp hzc y, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨ψ, hψ, hker⟩ := Upgrade.lieModelCentralCover t n p f hp hp2 hfund hadm (L ⧸ center L) hm
  have hψz : ψ (centralInv eR) ≠ 1 := fun h => hznc (hker h)
  have hmem' := ModelFacts.isClassicalMember_map_central ψ hψ hker hF hmem hψz
  obtain ⟨J, u, hJ, -, hu⟩ := ModelFacts.IsClassicalMember.exists_lift hp2 h5
    (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hmem'
  refine ⟨J, u, hJ, fun hc => hψz ?_⟩
  rw [← hu]
  exact (QuotientGroup.eq_one_iff u).mpr hc

theorem hasClassicalMember_of_lieModel (hI : OddLieInputs) (h4 : TrialityD4SL2Unique)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) {t : StatedLieTag}
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hfund : IsFundTag t) (hne : ¬ (t = .PSL ∧ n = 2)) (h5 : 5 ≤ p ^ f)
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) t n p f) : HasClassicalMember L := by
  obtain ⟨J, u, hJ, hu⟩ :=
    exists_isClassicalMember_of_lieModel hI h4 hq hp hp2 hadm hfund hne h5 hm
  exact ⟨p, f, ⟨hp⟩, hp2, h5, J, u, hJ, hu⟩

end

end CFSG.OddStandard.HigherRank
