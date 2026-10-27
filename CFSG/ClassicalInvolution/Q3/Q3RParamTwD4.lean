module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsComp
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4Edge
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
theorem td4_abelian_of_isSubnormal_of_isSolvable (hK : (-1 : K0ˣ) ≠ 1) [Finite K0]
    (h4 : 4 ≤ Nat.card K0) (hF4 : 4 ≤ Nat.card (fixedField σ))
    (hC₀ : graphFixedRootGroup TwistTag.D4 K0 σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K0 σ)
    [Finite (twistedGroup σ)] {N : Subgroup (twistedGroup σ)} (hsolv : Group.IsSolvable N)
    (hN : IsSubnormal N (Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)))) :
    ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  set C := Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) with hC
  set Q := (slB σ hσ).range with hQ
  have hBc : ∀ B : SL(2, K0), slB σ hσ B ∈ C := fun B => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← slB_neg_one hσ, ← map_mul, ← map_mul,
      ← neg_one_mul_comm_SL2]
  have hQC : Q ≤ C := by
    rintro _ ⟨B, rfl⟩
    exact hBc B
  have hNC : N ≤ C := CFSG.ClassicalInvolution.isSubnormal_le hN
  have hSP : ∀ n ∈ C, n ∈ SProd σ hσ := fun n hn =>
    mem_SProd_of_centralizes hσ hK hC₀ hgF (Subgroup.mem_centralizer_singleton_iff.mp hn)
  have hQqs : CFSG.IsQuasisimple Q :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (slB_injective hσ))
      (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4)
  have hQn : C ≤ Subgroup.normalizer (Q : Set (twistedGroup σ)) :=
    le_normalizer_of_forall_conj_mem fun c hc x hx => by
      obtain ⟨B, rfl⟩ := hx
      obtain ⟨B', hB'⟩ := SProd_conj_slB hσ (hSP c hc) B
      exact ⟨B', hB'.symm⟩
  have hcomm := commute_of_isSubnormal_of_isSolvable (A := Q) (C := C) (N := N)
    (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple hQqs) hQC hQn hN hsolv
  have hcent : ∀ x ∈ N, ∀ B : SL(2, K0), x * slB σ hσ B = slB σ hσ B * x := fun x hx B =>
    hcomm x hx _ ⟨B, rfl⟩
  have hle : N ≤ (slLong σ hσ).range := fun x hx => by
    obtain ⟨A, hA⟩ := exists_slLong_of_centralizes_slB hσ (hSP x (hNC hx)) (hcent x hx)
    exact ⟨A, hA.symm⟩
  set QA := (slLong σ hσ).range with hQA
  have hQAC : QA ≤ C := by
    rintro _ ⟨A, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      ← neg_one_mul_comm_SL2]
  have hQAqs : CFSG.IsQuasisimple QA :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (slLong_injective hσ))
      (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le hF4)
  have hNQ : IsSubnormal N QA := by
    have := CFSG.ClassicalInvolution.ModelFacts.isSubnormal_inf hN hQAC
    rwa [inf_eq_left.mpr hle] at this
  rcases CFSG.ClassicalInvolution.ModelFacts.eq_or_le_center_of_isSubnormal hNQ hQAqs with h | h
  · exfalso
    rw [h] at hsolv
    exact false_of_isQuasisimple_of_isSolvable
      (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple hQAqs) hsolv
  · intro a ha b hb
    obtain ⟨c, hc, hca⟩ := h ha
    have hbQ : b ∈ QA := hle hb
    have := Subgroup.mem_center_iff.mp hc ⟨b, hbQ⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [← hca]
    exact h2.symm

end Core

section Model


theorem classicalMemberParameters3At_trialityD4 : ClassicalMemberParameters3At .trialityD4 := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  obtain rfl : n = 0 := hadm.2.2
  have he : 1 ≤ e := hadm.2.1
  have h5 := five_le_pow_of_odd_prime_of_ne_three hr hr2 he hne
  have hfinK : Finite (modelUniv .trialityD4 0 r e hr).K :=
    ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have hfin := finite_galoisField_three (p := r) e he
  have hσ := sigma_three_td4 (p := r) e he
  have hK1 := neg_one_ne_one_galoisField_td4 hr2 (3 * e)
  have hrange := range_twistedIncl_eq hr2 e he
  have hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField r (3 * e))
      (iterateFrobenius (GaloisField r (3 * e)) r e) ≤
      (twistedIncl (iterateFrobenius (GaloisField r (3 * e)) r e)).range := hrange.ge
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField r (3 * e)) r e),
      twistedIncl (iterateFrobenius (GaloisField r (3 * e)) r e) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField r (3 * e))
          (iterateFrobenius (GaloisField r (3 * e)) r e) := fun g => hrange ▸ ⟨g, rfl⟩
  have hF4 : 4 ≤ Nat.card (fixedField (iterateFrobenius (GaloisField r (3 * e)) r e)) :=
    (by omega : 4 ≤ r ^ e).trans (ModelFacts.le_card_fixedField_iterateFrobenius he)
  have h4 : 4 ≤ Nat.card (GaloisField r (3 * e)) := by
    rw [GaloisField.card r (3 * e) (by omega), pow_mul']
    exact (by omega : 4 ≤ r ^ e).trans (Nat.le_self_pow (by norm_num) _)
  set σ := iterateFrobenius (GaloisField r (3 * e)) r e with hσdef
  have hτ2 : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : slLong σ hσ (-1) ≠ 1 := by
    intro h
    have h' := twistedIncl_slLong_neg_one hσ
    rw [h, map_one, ← rootDiagUnit_one] at h'
    exact aLongTD4_ne_one hK1 (rootDiagUnit_injective h'.symm)
  have hqs : CFSG.Open.IsQuasisimple (modelUniv .trialityD4 0 r e hr).K :=
    (ModelFacts.modelClauseZero .trialityD4 0 r e hr trivial hadm).1
  refine false_of_isClassicalMember3_of_oddGenerated ψ hψ hker ?_ h
  intro w hw N hNC hNs hNsolv _
  refine derivedSeries_two_eq_bot_of_commute ?_
  by_cases hw1 : w = 1
  · subst hw1
    have hC1 : Subgroup.centralizer ({1} : Set (modelUniv .trialityD4 0 r e hr).K) = ⊤ := by
      simp
    rw [hC1] at hNs
    rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hqs N hNs with
      hle | htop
    · intro a ha b hb
      exact (Subgroup.mem_center_iff.mp (hle ha) b).symm
    · exfalso
      rw [htop] at hNsolv
      have e : (modelUniv .trialityD4 0 r e hr).K ≃* (⊤ : Subgroup _) := Subgroup.topEquiv.symm
      exact false_of_isQuasisimple_of_isSolvable hqs
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hr2 he
      hw hτ2 hw1 hτ1
    refine commute_of_forall_map_mulEquiv (MulAut.conj g) hNs hNsolv ?_
    intro M hM hMsolv x hx y hy
    have hgw : (MulAut.conj g) w = slLong σ hσ (-1) := hg
    rw [hgw] at hM
    exact td4_abelian_of_isSubnormal_of_isSolvable hσ hK1 h4 hF4 hC₀ hgF hMsolv hM x hx y hy

end Model

end CFSG.ClassicalInvolution.Q3
