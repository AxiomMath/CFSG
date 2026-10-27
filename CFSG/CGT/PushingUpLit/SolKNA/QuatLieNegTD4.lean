module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieComponent
import CFSG.CGT.PushingUpLit.SolKNA.QuatLieDatum
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore
public import CFSG.ClassicalInvolution.Q3.Q3ExcCenterD4
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4Edge
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.Assembly (pCoreOf)

section TD4

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

variable {K0 : Type} [Field K0] {σ : K0 →+* K0} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem td4_component (hK : (-1 : K0ˣ) ≠ 1) [Finite K0] (h4 : 4 ≤ Nat.card K0)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K0 σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K0 σ)
    [Finite (twistedGroup σ)] :
    ∃ Q : Subgroup (twistedGroup σ),
      Q ≤ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) ∧
      (Q.subgroupOf (Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)))).Normal ∧
        CFSG.IsQuasisimple ↥Q := by
  set C := Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) with hC
  set Q := (slB σ hσ).range with hQ
  have hBc : ∀ B : SL(2, K0), slB σ hσ B ∈ C := fun B => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← slB_neg_one hσ, ← map_mul, ← map_mul,
      ← neg_one_mul_comm_SL2]
  have hQC : Q ≤ C := by
    rintro _ ⟨B, rfl⟩
    exact hBc B
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
  exact ⟨Q, hQC, hQn, hQqs⟩

end TD4

section Main

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

theorem negModel_TD4 : NegModel .trialityD4 0 := by
  intro X _ _ hm K hK R hq
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hch : (StatedLieTag.trialityD4) ∈ chevalleyExceptionalTags := by decide
  have hadm : StatedLieAdmissible .trialityD4 0 3 1 :=
    (CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_of_lieModel hch hm).1
  have : IsSimpleGroup X := hK.simple
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover .trialityD4 0 3 1
    hp (by norm_num) trivial hadm X hm
  have hZ := exc3_center_trialityD4 0 hp
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hψk.trans hZ.le)
  let e : (modelUniv .trialityD4 0 3 1 hp).K ≃* X := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩
  obtain ⟨t, P, SP, hTD, -, hU, hCN⟩ := exists_tightDatum_of_quaternion hK R hq
  have ht2 : orderOf t = 2 := hTD.order
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht2
    omega
  have hfinK : Finite (modelUniv .trialityD4 0 3 1 hp).K := Finite.of_equiv X e.symm.toEquiv
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
  obtain ⟨Q, hQC, hQn, hQq⟩ := td4_component hσ hK1 (by omega) hC₀ hgF
  obtain ⟨E, hEC, hEn, hEq⟩ := exists_component_of_conj_involution e hconj hQC hQn hQq htt ht1
  rw [hCN] at hEC hEn
  exact false_of_normal_quasisimple_in_normalizer hK hEC hEn hEq

end Main


end CFSG.CGT.PushingUpLit.SolKNA
