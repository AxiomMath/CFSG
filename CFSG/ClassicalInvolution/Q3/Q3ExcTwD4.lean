module

public import CFSG.ClassicalInvolution.Q3.Q3ExcCenterD4
public import CFSG.ClassicalInvolution.Q3.Q3ExcLift
public import CFSG.ClassicalInvolution.Q3.Q3ExcComp
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4OddCore
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

section Core

variable {K0 : Type} [Field K0] {σ : K0 →+* K0} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem td4_subnormal_eq_range (hK : (-1 : K0ˣ) ≠ 1) [Finite K0] (h4 : 4 ≤ Nat.card K0)
    (hF3 : Nat.card (fixedField σ) = 3)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K0 σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K0 σ)
    [Finite (twistedGroup σ)] {L : Subgroup (twistedGroup σ)} (eL : SL(2, ZMod 3) ≃* L)
    (hL : IsSubnormal L (Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)))) :
    L = (slLong σ hσ).range := by
  set C := Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) with hC
  set Q := (slB σ hσ).range with hQ
  have hBc : ∀ B : SL(2, K0), slB σ hσ B ∈ C := fun B => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← slB_neg_one hσ, ← map_mul, ← map_mul,
      ← neg_one_mul_comm_SL2]
  have hQC : Q ≤ C := by
    rintro _ ⟨B, rfl⟩
    exact hBc B
  have hLC : L ≤ C := isSubnormal_le hL
  have hSP : ∀ n ∈ C, n ∈ SProd σ hσ := fun n hn =>
    mem_SProd_of_centralizes hσ hK hC₀ hgF (Subgroup.mem_centralizer_singleton_iff.mp hn)
  have hQn : (Q.subgroupOf C).Normal := ⟨fun x hx g => by
    obtain ⟨B, hB⟩ := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨B', hB'⟩ := SProd_conj_slB hσ (hSP g g.2) B
    refine Subgroup.mem_subgroupOf.2 ⟨B', ?_⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [← hB]
    exact hB'.symm⟩
  have hQqs : CFSG.IsQuasisimple Q :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (slB_injective hσ))
      (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4)
  have hQqs' : CFSG.IsQuasisimple (Q.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQC).symm hQqs
  have eL' : SL(2, ZMod 3) ≃* L.subgroupOf C :=
    eL.trans (Subgroup.subgroupOfEquivOfLe hLC).symm
  have hLsolv : Group.IsSolvable (L.subgroupOf C) :=
    CFSG.LieType.HighestRoot.isSolvable_of_mulEquiv (Nat.card_zmod 3) eL'.symm
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hLsolv
    (exc3_isSubnormal_subgroupOf hL)).1 (Q.subgroupOf C) ⟨hQqs', hQn.isSubnormal⟩
  have hcent : ∀ x ∈ L, ∀ B : SL(2, K0), x * slB σ hσ B = slB σ hσ B * x := by
    intro x hx B
    have hm := Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.2 ⟨B, rfl⟩ : (⟨slB σ hσ B, hBc B⟩ : C) ∈ Q.subgroupOf C)
      (Subgroup.mem_subgroupOf.2 hx : (⟨x, hLC hx⟩ : C) ∈ L.subgroupOf C)
    rw [hcomm, Subgroup.mem_bot] at hm
    exact (congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp hm)).symm
  have hle : L ≤ (slLong σ hσ).range := fun x hx => by
    obtain ⟨A, hA⟩ := exists_slLong_of_centralizes_slB hσ (hSP x (hLC hx)) (hcent x hx)
    exact ⟨A, hA.symm⟩
  have hcard : Nat.card (slLong σ hσ).range ≤ 24 :=
    (CFSG.LieType.HighestRoot.card_eq_24 hF3
      (MonoidHom.ofInjective (slLong_injective hσ)).symm).le
  exact eq_of_le_of_natCard_le eL hle hcard

include hσ in
theorem td4_member_eq_conj (hK : (-1 : K0ˣ) ≠ 1) [Finite K0] (h4 : 4 ≤ Nat.card K0)
    (hF3 : Nat.card (fixedField σ) = 3)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K0 σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K0 σ)
    [Finite (twistedGroup σ)]
    (hconj : ∀ u : twistedGroup σ, u * u = 1 → u ≠ 1 →
      ∃ g : twistedGroup σ, g * u * g⁻¹ = slLong σ hσ (-1))
    {L : Subgroup (twistedGroup σ)} {z : twistedGroup σ} (hL : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ g : twistedGroup σ,
      L = conjSub g⁻¹ (CFSG.LieType.CurtisTits.rankOne (twistedRootGroup σ) (ng 0)) := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hL.orderOf_eq_two, pow_two] at this
  obtain ⟨g, hg⟩ := hconj z hz2 hL.ne_one
  have hL' := hL.conj g
  rw [hg] at hL'
  obtain ⟨e₀⟩ := hL.nonempty_equiv_sl2 hO
  have eL' : SL(2, ZMod 3) ≃* conjSub g L :=
    e₀.symm.trans (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  have h := td4_subnormal_eq_range hσ hK h4 hF3 hC₀ hgF eL' hL'.subnormal
  refine ⟨g, ?_⟩
  rw [ModelFacts.rankOne_long_eq_range hσ, ← h, conjSub_inv_conjSub]

end Core

section Model

theorem classicalMembersFundamental3Tag_trialityD4 :
    ClassicalMembersFundamental3Tag .trialityD4 := by
  intro n hp hFT hadm L z hL hO
  obtain rfl : n = 0 := hadm.2.2
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hfinK : Finite (modelUniv .trialityD4 0 3 1 hp).K :=
    ModelFacts.finite_modelUniv (by norm_num) hp hFT hadm
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfin := finite_galoisField_three (p := 3) 1 le_rfl
  have hσ := sigma_three_td4 (p := 3) 1 le_rfl
  have hK1 := neg_one_ne_one_galoisField_td4 hp2 (3 * 1)
  have hrange := range_twistedIncl_eq hp2 1 le_rfl
  have hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField 3 (3 * 1))
      (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1) ≤
      (twistedIncl (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1)).range := hrange.ge
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1),
      twistedIncl (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField 3 (3 * 1))
          (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1) := fun g => hrange ▸ ⟨g, rfl⟩
  have hcardK : Nat.card (GaloisField 3 (3 * 1)) = 27 := by
    rw [GaloisField.card 3 (3 * 1) (by omega), pow_mul']
    norm_num
  have hσ3 : ∀ c, iterateFrobenius (GaloisField 3 (3 * 1)) 3 1 c = c ^ 3 := fun c => by
    rw [iterateFrobenius_def, pow_one]
  have hchar : ringChar (GaloisField 3 (3 * 1)) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 (3 * 1)) 3]
    exact hp2
  have hF3 := CFSG.LieType.HighestRoot.card_fixedField_eq_three hchar hσ3
  set σ := iterateFrobenius (GaloisField 3 (3 * 1)) 3 1 with hσdef
  have hτ2 : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : slLong σ hσ (-1) ≠ 1 := by
    intro h
    have h' := twistedIncl_slLong_neg_one hσ
    rw [h, map_one, ← rootDiagUnit_one] at h'
    exact aLongTD4_ne_one hK1 (rootDiagUnit_injective h'.symm)
  have hconj : ∀ u : twistedGroup σ, u * u = 1 → u ≠ 1 →
      ∃ g : twistedGroup σ, g * u * g⁻¹ = slLong σ hσ (-1) := fun u hu2 hu1 =>
    CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 le_rfl hu2 hτ2
      hu1 hτ1
  obtain ⟨g, hg⟩ := td4_member_eq_conj hσ hK1 (by omega) hF3 hC₀ hgF hconj hL hO
  refine ⟨g⁻¹, Pi.single (ng 0) 1, Or.inr (Or.inr ⟨rfl, ?_⟩), hg⟩
  change Pi.single (ng 0) 1 ∈ (twistedDatum σ).roots
  rw [twistedDatum_roots]
  exact isRoot_single .G2 (ng 0)

theorem td4_oddCoreIn_eq_bot (hp : Nat.Prime 3)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1)
    [Finite (modelUniv .trialityD4 0 3 1 hp).K] {c : (modelUniv .trialityD4 0 3 1 hp).K}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    oddCoreIn (Subgroup.centralizer ({c} : Set (modelUniv .trialityD4 0 3 1 hp).K)) = ⊥ :=
  td4ThreeOddCore_proved 0 3 1 hp hadm (by norm_num) c hc2 hc1 _ (oddCoreIn_le _)
    (fun y hy n hn => conj_mem_oddCoreIn hy hn) (odd_card_oddCoreIn _)

theorem simpleOddCentralizerFreeTag_trialityD4 : SimpleOddCentralizerFreeTag .trialityD4 := by
  intro n hp hadm s hs
  obtain rfl : n = 0 := hadm.2.2
  obtain ⟨hfin, hZ2⟩ := modelFiniteCenterTwoGroup3 .trialityD4 0 hp trivial hadm
  have hZ := exc3_center_trialityD4 0 hp
  have hqs : CFSG.Open.IsQuasisimple (modelUniv .trialityD4 0 3 1 hp).K :=
    (ModelFacts.modelClauseZero .trialityD4 0 3 1 hp trivial hadm).1
  refine exc3_simpleOddCentralizer_of_cover (MonoidHom.id _) Function.surjective_id ?_ ?_ s hs
  · rw [MonoidHom.ker_id, hZ]
  · intro c hc2
    by_cases hc1 : c = 1
    · subst hc1
      have hC : Subgroup.centralizer ({1} : Set (modelUniv .trialityD4 0 3 1 hp).K) = ⊤ := by
        simp
      rw [hC]
      obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_isQuasisimple hqs
      exact oddCoreIn_top_eq_bot_of_isQuasisimple hqs hZ2 ⟨x, hx⟩
    · exact td4_oddCoreIn_eq_bot hp hadm hc2 hc1

theorem oddCentralizerFreeTag_trialityD4 : OddCentralizerFreeTag .trialityD4 :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_trialityD4

end Model

end CFSG.ClassicalInvolution.Q3
