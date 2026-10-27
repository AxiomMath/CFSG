module

public import CFSG.LieType.Chevalley.E6EvenRootTorusAutFix
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6Reps
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.Sporadic.Schreier.TitsOther

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.E6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6GraphLevi (setA thetaRankOneGroup thetaTorus thetaTorusHom)
open CFSG.ComponentClassification.RankTwoExceptional.Exc CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

variable {K : Type} [Field K]

theorem e6Reps_mem_subsystemGroup
    [CharP K 2] :
    ∀ x ∈ e6Reps (K := K), (x : ModGL .E6 K) ∈ subsystemGroup TwistTag.E6.tag K setA := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro x hx
  simp only [e6Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact (E6EvenInvolution.jRep₁_facts h2).1
  · exact (E6EvenInvolution.jRep₂_facts h2).1
  · exact (E6EvenInvolution.jRep₃_facts h2).1

theorem leviData_e6
    [Finite K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) {j : adjointGroup TwistTag.E6.tag K}
    (hj : (j : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA) :
    LeviData (zx j)
      ((thetaRankOneGroup (RingHom.id K)).subgroupOf (adjointGroup TwistTag.E6.tag K))
      ((thetaTorus (RingHom.id K)).subgroupOf (adjointGroup TwistTag.E6.tag K))
      ((torusGroup TwistTag.E6.tag K).subgroupOf (adjointGroup TwistTag.E6.tag K))
      ((subsystemGroup TwistTag.E6.tag K setA).subgroupOf (adjointGroup TwistTag.E6.tag K)) := by
  have hm1 : 1 ≤ m := by omega
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hLG : subsystemGroup TwistTag.E6.tag K setA ≤ adjointGroup TwistTag.E6.tag K :=
    E6GraphLevi.subsystemGroup_le_adjointGroup
  have hXG : thetaRankOneGroup (RingHom.id K) ≤ adjointGroup TwistTag.E6.tag K :=
    E6GraphRadical.thetaRankOneGroup_le_adjointGroup (RingHom.id K)
  have hXL : thetaRankOneGroup (RingHom.id K) ≤
      centralizer (subsystemGroup TwistTag.E6.tag K setA : Set (ModGL TwistTag.E6.tag K)) :=
    E6EvenRootTorus.thetaRankOneGroup_le_centralizer hm1 hK
  have hHX : thetaTorus (RingHom.id K) ≤ thetaRankOneGroup (RingHom.id K) :=
    E6EvenRootTorus.thetaTorus_le_thetaRankOneGroup h2
  have hHG : thetaTorus (RingHom.id K) ≤ adjointGroup TwistTag.E6.tag K := hHX.trans hXG
  have hTG : torusGroup TwistTag.E6.tag K ≤ adjointGroup TwistTag.E6.tag K :=
    (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
  have hF1 : adjointGroup TwistTag.E6.tag K ⊓
      centralizer (thetaRankOneGroup (RingHom.id K) : Set (ModGL TwistTag.E6.tag K)) =
        subsystemGroup TwistTag.E6.tag K setA :=
    E6EvenRootTorus.centralizer_thetaRankOneGroup hm1 hK
  obtain ⟨hcomm, hq, hodd, -⟩ := E6EvenRootTorus.subsystemGroup_facts hm1 hK
  have hXj : ∀ d ∈ (thetaRankOneGroup (RingHom.id K)).subgroupOf
      (adjointGroup TwistTag.E6.tag K), d ∈ cent j := fun d hd =>
    mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_iff.1 (hXL (mem_subgroupOf.1 hd)) _ hj).symm)
  obtain ⟨t, ht⟩ := E6EvenRootTorus.exists_units_ne_one hm hK
  refine
    { D_perfect := commutator_subgroupOf_of_perfect hXG
        (E6EvenRootTorus.commutator_thetaRankOneGroup h2 h4)
      D_le := fun d hd => mem_centralizer_iff.2 fun w hw => hw.2.1 d (hXj d hd)
      Q_le := fun s hs => mem_subgroupOf.2 (hHX (mem_subgroupOf.1 hs))
      Q_ne_bot := ?_
      odd_Q := ?_
      Q_le_H := fun s hs =>
        mem_subgroupOf.2 (E6GraphLevi.thetaTorus_le_torusGroup _ (mem_subgroupOf.1 hs))
      H_comm := fun a ha b hb => Subtype.ext
        (RootTorus.torusGroup_mul_comm (mem_subgroupOf.1 ha) (mem_subgroupOf.1 hb))
      H_le := fun h hh => by
        rw [← Subgroup.subgroupOf_normalizer_eq hLG]
        exact mem_subgroupOf.2
          (RootTorus.torusGroup_le_normalizer_subsystemGroup _ (mem_subgroupOf.1 hh))
      L_le := fun l hl => mem_centralizer_iff.2 fun s hs => Subtype.ext
        (mem_centralizer_iff.1 (hXL (hHX (mem_subgroupOf.1 hs))) _ (mem_subgroupOf.1 hl)).symm
      cent_eq := fun c hc => ?_
      quasisimple := hq
      odd_center := hodd
      Z_le := fun w hw => ?_ }
  · intro hbot
    have hmem : (⟨_, E6EvenRootTorus.thetaTorusHom_mem_adjointGroup h2 t⟩ :
        adjointGroup TwistTag.E6.tag K) ∈
          (thetaTorus (RingHom.id K)).subgroupOf (adjointGroup TwistTag.E6.tag K) :=
      E6EvenRootTorus.thetaTorusHom_mem_thetaTorus t
    rw [hbot, mem_bot] at hmem
    have h1 : thetaTorusHom K t = 1 := congrArg Subtype.val hmem
    exact ht (E6GraphLevi.thetaTorusHom_injective h2 (h1.trans (map_one _).symm))
  · rw [Nat.card_congr (subgroupOfEquivOfLe hHG).toEquiv, E6EvenRootTorus.card_thetaTorus h2,
      Nat.card_units, hK]
    exact E6EvenRootTorus.odd_two_pow_sub_one hm1
  · have hcθ : (c : ModGL TwistTag.E6.tag K) ∈
        centralizer (thetaTorus (RingHom.id K) : Set (ModGL TwistTag.E6.tag K)) := by
      rw [mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (mem_centralizer_iff.1 hc ⟨s, hHG hs⟩ (mem_subgroupOf.2 hs))
    obtain ⟨h, hh, hhc⟩ := RootTorus.exists_mul_of_mem_centralizer_thetaTorus h2 ht c.2 hcθ
    exact ⟨⟨h, hTG hh⟩, mem_subgroupOf.2 hh, mem_subgroupOf.2 hhc⟩
  · obtain ⟨-, hwz, -⟩ := hw
    rw [mem_subgroupOf, ← hF1]
    refine mem_inf.2 ⟨w.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact (congrArg Subtype.val (hwz ⟨y, hXG hy⟩ (hXj ⟨y, hXG hy⟩ (mem_subgroupOf.2 hy)))).symm

theorem autFix_e6
    [Finite K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) :
    AutFix ((thetaTorus (RingHom.id K)).subgroupOf (adjointGroup TwistTag.E6.tag K))
      ((subsystemGroup TwistTag.E6.tag K setA).subgroupOf (adjointGroup TwistTag.E6.tag K)) :=
  fun α hα hQ hL => E6EvenRootTorus.eq_one_of_fix hm hK α hα hQ hL

theorem statedClassicalModel_of_mulEquiv_e6
    [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {L : Type} [Group L]
    (e : L ≃* rankTwoQuot
      ((subsystemGroup TwistTag.E6.tag K setA).subgroupOf (adjointGroup TwistTag.E6.tag K))) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 6 2 m := by
  obtain ⟨-, -, -, ⟨e'⟩⟩ := E6EvenRootTorus.subsystemGroup_facts hm hK
  exact ⟨⟨Nat.prime_two, hm, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance, hK,
    ⟨e.trans e'⟩⟩

theorem step814_e6
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) : Step814 .E6 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | e6 m hm K hK e =>
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hm hK
    have h34 : Asc08Lemma34 := asc08Lemma34
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    have : Finite (ModGL .E6 K) := finite_modGL
    have : Finite (adjointGroup .E6 K) := Subtype.finite
    have hZC : center (adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
    have e₁ : AdjointQuotient .E6 K ≃* adjointGroup .E6 K :=
      (QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot
    have hOut := odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_E
      (S := rankTwoQuot A) (Or.inl rfl) hm ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩)
    have hq2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    refine exists_config814_of_torus h32 h33 h4 h34 (ExcModel.e6 m hm K hK e) hA hZA hZC
      (e.trans e₁) hOut (2 ^ m) rfl hq2 (reps := e6Reps) classesCover_e6Reps residualMem_e6Reps
      charTwo_e6Reps (fun hq x hx => Or.inl (card_zx_e6Reps (by rw [hK, hq]) x hx))
      (fun hq x hx => ?_)
      (fun _ => EvenOddRadical.centralizerOTwoFree_adjointGroup (Or.inr (Or.inl rfl)))
      (fun h => by simp [ExcModel.IsTrialityFour] at h)
    have hm2 : 2 ≤ m := by
      by_contra h
      have hm1 : m = 1 := by omega
      rw [hm1] at hq
      norm_num at hq
    exact ⟨_, _, _, _, leviData_e6 hm2 hK (j := x) (e6Reps_mem_subsystemGroup x hx),
      autFix_e6 hm2 hK, fun L₀ ⟨f⟩ => statedClassicalModel_of_mulEquiv_e6 hm hK f,
      fun h => by simp [ExcModel.IsTrialityFour] at h⟩
  | g2 => simp [ExcModel.tag] at hD
  | f4 => simp [ExcModel.tag] at hD
  | e7 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional.E6Sec8
