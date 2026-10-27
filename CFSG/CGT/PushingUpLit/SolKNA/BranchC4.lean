module

public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4Final
public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4Rev
public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4Step1
public import CFSG.CGT.PushingUpLit.SolKNA.Dichotomy
public import CFSG.CGT.PushingUpLit.SolKNA.Lemma18Final
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolKAb
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

open CFSG.ComponentClassification.AschbacherTightEmbedding
open C4Aux

variable {G : Type} [Group G]

private theorem isSylowOf_self_two [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) :
    IsSylowOf 2 P P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  refine isSylowOf_of_card le_rfl ?_
  rw [hk, Nat.Prime.factorization_pow Nat.prime_two]
  simp

section Certs


variable [Finite G]

theorem basic_conj {R T : Subgroup G} {g : G} (cfg : NAConfig G R R T g) {x : G}
    (hx : x ∉ Subgroup.normalizer (R : Set G)) :
    ¬ conjSubgroup x R ≤ Subgroup.normalizer (R : Set G) →
      ∀ T' : Subgroup G, T' = conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G) → T' ≠ ⊥ →
        Nat.card ↥(R ⊓ Subgroup.normalizer (T' : Set G)) = Nat.card ↥T' ∧
          R ⊓ Subgroup.normalizer (T' : Set G) = R ⊓ Subgroup.centralizer (T' : Set G) := by
  intro hnle T' hT' hT'0
  have hrc : rightConjugate R x⁻¹ = conjSubgroup x R := rightConjugate_inv_eq R x
  have h2R : IsPGroup 2 ↥(conjSubgroup x R) :=
    cfg.sylowR.isPGroup.map (MulAut.conj x).toMonoidHom
  have hT'R : T' ≤ conjSubgroup x R := by
    rw [hT']
    exact inf_le_left
  have hT'N : T' ≤ Subgroup.normalizer (R : Set G) := by
    rw [hT']
    exact inf_le_right
  have h2 : IsPGroup 2 ↥T' := h2R.to_le hT'R
  have cfg' : NAConfig G R R T' x⁻¹ := by
    refine ⟨cfg.stSetting, cfg.perfect, cfg.sylowR, cfg.noncomm, cfg.rank, ?_, ?_, hT'0, ?_,
      hT'N, ?_⟩
    · intro h
      exact hx ((Subgroup.normalizer (R : Set G)).inv_mem_iff.mp h)
    · rw [hrc, ← hT']
      exact isSylowOf_self_two h2
    · have hne : T' ≠ conjSubgroup x R := fun h => hnle (h ▸ hT'N)
      have h1 : Nat.card ↥T' ≤ Nat.card ↥(conjSubgroup x R) := Subgroup.card_le_of_le hT'R
      have h3 : Nat.card ↥T' ≠ Nat.card ↥(conjSubgroup x R) := fun h =>
        hne (Subgroup.eq_of_le_of_card_ge hT'R (le_of_eq h.symm))
      rw [card_conjSubgroup] at h1 h3
      exact lt_of_le_of_ne h1 h3
    · rw [hrc]
      exact hT'R
  exact ⟨cfg'.basic.2.2.1, cfg'.inf_normalizer_eq⟩

theorem lemma18Trans_holds : Lemma18Trans G := by
  intro R g Z hgZ hRZ hR2 hTI T C N hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR hrel hT4 hN hNnorm
    hΦb₁ hΦb₂ hTZ
  exact lemma18_normalizer_conj_final hgZ hRZ hR2 hTI hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR
    hrel hT4 hN hNnorm hΦb₁ hΦb₂ hTZ

theorem caseII5_not_normal_false_of {K R T H : Subgroup G} {g : G}
    (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hM : ¬ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G))
    (hA : ∃ W, AData R T W ∧ W ⊓ R = H) : False := by
  obtain ⟨hKR, -, hT4, c, hcN, hc1, -, -, -, hsq⟩ := cfg.caseII5_not_normal h5 hM
  obtain ⟨W, A, rfl⟩ := hA
  have cfg' : NAConfig G R R T g := by
    rw [hKR] at cfg
    exact cfg
  have tight : TightlyEmbedded R := cfg'.tight
  have h2₁ : IsPGroup 2 ↥(rightConjugate R g) :=
    cfg'.sylowR.isPGroup.map (MulAut.conj g⁻¹).toMonoidHom
  have hRR₁ : R ⊓ rightConjugate R g = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    by_contra hu1
    have hu1' : u ≠ 1 := fun h => hu1 (Subgroup.mem_bot.mpr h)
    exact cfg'.g_not (normalizer_of_tight tight A.two_R hu.1 hu1'
      ((mem_rightConjugate_iff R g u).mp hu.2))
  have hR₁N : ∀ y ∈ rightConjugate R g, y ∈ Subgroup.normalizer (R : Set G) → y ∈ T := by
    intro y hy hyN
    have := cfg'.sylowT.eq_of_le cfg'.sylowT.le le_rfl h2₁.to_inf_left
    rw [← this]
    exact ⟨hy, hyN⟩
  obtain ⟨x, hxP, hxR⟩ := exists_x_normalizer_P A hT4 tight
    (CFSG.ComponentClassification.AS76b.tightlyEmbedded_rightConjugate tight g) h2₁ hRR₁
    cfg'.T_le (rightConjugate_card R g) hR₁N
  have D : C4Data R T W (R ⊓ Subgroup.normalizer (T : Set G))
      ((R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T) c x :=
    ⟨A, rfl, rfl, tight, hT4, hcN, hc1, hsq, hxP, hxR⟩
  exact D.false_of (basic_conj cfg' hxR) lemma18Trans_holds

theorem caseII5_not_normal_false {K R T H : Subgroup G} {g : G}
    (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hM : ¬ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) : False :=
  caseII5_not_normal_false_of cfg h5 hM (exists_aData_of_caseII5 cfg h5)

end Certs

end CFSG.CGT.PushingUpLit.SolKNA
