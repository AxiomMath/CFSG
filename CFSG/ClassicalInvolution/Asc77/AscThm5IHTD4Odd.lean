module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHChart
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore
public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4One
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4NonToral

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance.Q27
  CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

section Core

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem thm5IH_oddCore_td4 (hK : (-1 : Kˣ) ≠ 1) [Finite K]
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {N : Subgroup (twistedGroup σ)}
    (hNc : N ≤ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)))
    (hNnorm : ∀ c ∈ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)),
      ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_neg_one_ne_one hK
  have hoddK : Odd (Nat.card K) := thm5IH_odd_card_of_two_ne_zero h2K
  have h2F : (2 : fixedField σ) ≠ 0 := fun h => h2K (by
    have h' := congrArg (fixedField σ).subtype h
    rwa [map_ofNat, map_zero] at h')
  have hoddF : Odd (Nat.card (fixedField σ)) := thm5IH_odd_card_of_two_ne_zero h2F
  have hBc : ∀ C : SL(2, K), slB σ hσ C ∈
      Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) := fun C => by
    rw [Subgroup.mem_centralizer_singleton_iff, ← slB_neg_one hσ, ← map_mul, ← map_mul,
      ← neg_one_mul_comm_SL2]
  have hNBnormal : (N.comap (slB σ hσ)).Normal := ⟨fun x hx g => by
    show slB σ hσ (g * x * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNnorm _ (hBc g) _ hx⟩
  have hNBodd : Odd (Nat.card (N.comap (slB σ hσ))) := by
    have h1 : Nat.card ((N.comap (slB σ hσ)).map (slB σ hσ)) = Nat.card (N.comap (slB σ hσ)) :=
      Subgroup.card_map_of_injective (slB_injective hσ)
    have h2 : (N.comap (slB σ hσ)).map (slB σ hσ) ≤ N := Subgroup.map_comap_le _ _
    rw [← h1]
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le h2)
  have hNBbot : N.comap (slB σ hσ) = ⊥ := thm5IH_sl2_odd_normal_eq_bot hoddK hNBnormal hNBodd
  have hSP : ∀ n ∈ N, n ∈ SProd σ hσ := fun n hn =>
    mem_SProd_of_centralizes hσ hK hC₀ hgF (Subgroup.mem_centralizer_singleton_iff.mp (hNc hn))
  have hcent : ∀ n ∈ N, ∀ C : SL(2, K), n * slB σ hσ C = slB σ hσ C * n := by
    intro n hn C
    obtain ⟨C', hC'⟩ := SProd_conj_slB hσ (hSP n hn) C
    have hmem : slB σ hσ (C' * C⁻¹) ∈ N := by
      rw [map_mul, map_inv, ← hC']
      have h1 := hNnorm _ (hBc C) _ (inv_mem hn)
      have h2 := mul_mem hn h1
      simpa [mul_assoc] using h2
    have h3 : C' * C⁻¹ ∈ N.comap (slB σ hσ) := hmem
    rw [hNBbot, Subgroup.mem_bot, mul_inv_eq_one] at h3
    rw [h3] at hC'
    exact mul_inv_eq_iff_eq_mul.mp hC'
  have hA : ∀ n ∈ N, ∃ A : SL(2, fixedField σ), n = slLong σ hσ A := fun n hn =>
    exists_slLong_of_centralizes_slB hσ (hSP n hn) (hcent n hn)
  have hNAnormal : (N.comap (slLong σ hσ)).Normal := ⟨fun x hx g => by
    show slLong σ hσ (g * x * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNnorm _ (slLong_mem_centralizer_tauL hσ g) _ hx⟩
  have hNAodd : Odd (Nat.card (N.comap (slLong σ hσ))) := by
    have h1 : Nat.card ((N.comap (slLong σ hσ)).map (slLong σ hσ)) =
        Nat.card (N.comap (slLong σ hσ)) := Subgroup.card_map_of_injective (slLong_injective hσ)
    have h2 : (N.comap (slLong σ hσ)).map (slLong σ hσ) ≤ N := Subgroup.map_comap_le _ _
    rw [← h1]
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le h2)
  have hNAbot : N.comap (slLong σ hσ) = ⊥ := thm5IH_sl2_odd_normal_eq_bot hoddF hNAnormal hNAodd
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  obtain ⟨A, rfl⟩ := hA n hn
  have h1 : A ∈ N.comap (slLong σ hσ) := hn
  rw [hNAbot, Subgroup.mem_bot] at h1
  rw [h1, map_one]

end Core

section Model

variable {p : ℕ} [Fact p.Prime]

theorem thm5IH_td4_oddCoreTrivial (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    InvolutionOddCoreTrivial (modelUniv .trialityD4 0 p e Fact.out).K := by
  have he : 1 ≤ e := hadm.2.1
  have hfin := finite_galoisField_three (p := p) e he
  have hσ := sigma_three_td4 (p := p) e he
  have hK1 := neg_one_ne_one_galoisField_td4 hp2 (3 * e)
  have hrange := range_twistedIncl_eq hp2 e he
  have hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (iterateFrobenius (GaloisField p (3 * e)) p e) ≤
      (twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e)).range := hrange.ge
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
          (iterateFrobenius (GaloisField p (3 * e)) p e) := fun g => hrange ▸ ⟨g, rfl⟩
  set σ := iterateFrobenius (GaloisField p (3 * e)) p e with hσdef
  have hτ2 : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : slLong σ hσ (-1) ≠ 1 := by
    intro h
    have h' := twistedIncl_slLong_neg_one hσ
    rw [h, map_one, ← rootDiagUnit_one] at h'
    exact aLongTD4_ne_one hK1 (rootDiagUnit_injective h'.symm)
  apply involutionOddCoreTrivial_of_conj
    (fun u v hu hv hu1 hv1 =>
      CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 he hu hv hu1 hv1)
  refine ⟨slLong σ hσ (-1), hτ2, hτ1, ?_⟩
  intro N hNc hNnorm hNodd
  exact thm5IH_oddCore_td4 hσ hK1 hC₀ hgF hNc hNnorm hNodd

theorem td4OddCoreAll_proved : TD4OddCoreAll p :=
  fun _ hadm hp2 => thm5IH_td4_oddCoreTrivial hp2 hadm

theorem td4GenerateAll_proved : TD4GenerateAll p :=
  fun _ hadm hp2 => involutionCentralizersGenerate_td4_proved hp2 hadm

theorem t5BaseAt_td4_proved {f k e : ℕ} (P : Prop → Prop) : T5BaseAt p f .trialityD4 k e P :=
  t5BaseAt_td4 td4OddCoreAll_proved td4GenerateAll_proved P

end Model

end CFSG.ClassicalInvolution.Asc77
