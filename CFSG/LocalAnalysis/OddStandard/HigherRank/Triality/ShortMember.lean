module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4Edge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModel

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.RankTwoOddLie (isClassicalMember_of_sl2)
open scoped MatrixGroups

theorem five_le_pow_three_mul {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    5 ≤ p ^ (3 * e) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  calc 5 ≤ 3 ^ 3 := by norm_num
    _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
    _ ≤ p ^ (3 * e) := Nat.pow_le_pow_right hp.pos (by omega)

section


theorem slLong_neg_one_ne_one {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : (-1 : Kˣ) ≠ 1) : slLong σ hσ (-1) ≠ 1 := by
  intro h
  have h' := twistedIncl_slLong_neg_one hσ
  rw [h, map_one, ← rootDiagUnit_one] at h'
  exact aLongTD4_ne_one hK (rootDiagUnit_injective h'.symm)

theorem isClassicalMember_slB {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {σ : GaloisField p f →+* GaloisField p f} (hσ : ∀ c, σ (σ (σ c)) = c)
    (hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField p f) σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ,
      twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 (GaloisField p f) σ) :
    IsClassicalMember p f (slB σ hσ).range (slLong σ hσ (-1)) := by
  have hK1 := neg_one_ne_one_galoisField_td4 hp2 f
  have hτ2 : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hz2 : orderOf (slLong σ hσ (-1)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hτ2) (slLong_neg_one_ne_one hσ hK1)
  have hzB : slLong σ hσ (-1) ∈ (slB σ hσ).range := ⟨-1, slB_neg_one hσ⟩
  have hLC : (slB σ hσ).range ≤ centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) := by
    rintro _ ⟨C, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← slB_neg_one hσ, ← map_mul, ← map_mul,
      ← neg_one_mul_comm_SL2]
  have hconj : ∀ c ∈ centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)),
      ∀ C : SL(2, GaloisField p f), ∃ C', c * slB σ hσ C * c⁻¹ = slB σ hσ C' := fun c hc C =>
    SProd_conj_slB hσ (mem_SProd_of_centralizes hσ hK1 hC₀ hgF
      (Subgroup.mem_centralizer_singleton_iff.mp hc)) C
  have hCN : centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) ≤
      normalizer ((slB σ hσ).range : Set (twistedGroup σ)) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨C, rfl⟩
      obtain ⟨C', hC'⟩ := hconj c hc C
      exact ⟨C', hC'.symm⟩
    · rintro ⟨C', hC'⟩
      obtain ⟨C, hC⟩ := hconj c⁻¹ (inv_mem hc) C'
      refine ⟨C, ?_⟩
      rw [← hC, hC', inv_inv]
      group
  let eL : (slB σ hσ).range ≃* SL(2, GaloisField p f) :=
    (MonoidHom.ofInjective (slB_injective hσ)).symm
  exact isClassicalMember_of_sl2 hp2 h5 eL hz2 hzB hLC hCN

end

section


theorem exists_isClassicalMember_cube {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    ∃ (J : Subgroup (modelUniv .trialityD4 0 p e Fact.out).K)
      (z : (modelUniv .trialityD4 0 p e Fact.out).K),
      IsClassicalMember p (3 * e) J z ∧
        z ∉ Subgroup.center (modelUniv .trialityD4 0 p e Fact.out).K := by
  have hfin := finite_galoisField_three (p := p) e he
  have hσ := sigma_three_td4 (p := p) e he
  have hrange := range_twistedIncl_eq hp2 e he
  have hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (iterateFrobenius (GaloisField p (3 * e)) p e) ≤
      (twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e)).range := hrange.ge
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
          (iterateFrobenius (GaloisField p (3 * e)) p e) := fun g => hrange ▸ ⟨g, rfl⟩
  have h5 := five_le_pow_three_mul (Fact.out : p.Prime) hp2 he
  refine ⟨(slB _ hσ).range, slLong _ hσ (-1), isClassicalMember_slB hp2 h5 hσ hC₀ hgF, ?_⟩
  rw [CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 he]
  exact fun h => slLong_neg_one_ne_one hσ (neg_one_ne_one_galoisField_td4 hp2 (3 * e))
    (Subgroup.mem_bot.mp h)

end

end CFSG.OddStandard.HigherRank
