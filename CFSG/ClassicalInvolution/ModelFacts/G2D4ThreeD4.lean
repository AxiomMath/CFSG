module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC
public import CFSG.ClassicalInvolution.Balance.Q27D4Parts

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Balance.Q27

variable {p : ℕ} [Fact p.Prime]

section Existence

theorem exists_short_fund_trialityD4 (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    ∃ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D,
      ⁅R, R⁆ = R ∧ ∃ c, IsUniqueInvolution R c := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  have hodd : Odd (Nat.card (GaloisField p (3 * e))) := by
    rw [GaloisField.card p (3 * e) (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have h4S : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
    rw [hK]
    exact four_le_pow_three (by
      calc 2 ≤ 3 := by norm_num
        _ ≤ p := hp3
        _ ≤ p ^ e := Nat.le_self_pow (by omega) p)
  set i : Fin (modelUniv .trialityD4 0 p e Fact.out).D.rank :=
    ⟨1, by show 1 < 2; exact Nat.one_lt_two⟩ with hi
  have hR : rankOne (modelUniv .trialityD4 0 p e Fact.out).D.rootGroup i =
      (slShort (iterateFrobenius (GaloisField p (3 * e)) p e) hσ).range :=
    ModelFacts.rankOne_short_eq_range hσ
  refine ⟨(slShort (iterateFrobenius (GaloisField p (3 * e)) p e) hσ).range, ?_, ?_, ?_⟩
  · rw [← hR]
    exact ⟨1, Pi.single i 1, Or.inr (Or.inr ⟨rfl,
      CFSG.ClassicalInvolution.Balance.single_mem_roots _ i⟩), (conjSub_one _).symm⟩
  · refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · have h1 := ModelFacts.fundPerfect_range_le_commutator
        (CFSG.ClassicalInvolution.sl2_isPerfect h4S)
        (slShort (iterateFrobenius (GaloisField p (3 * e)) p e) hσ)
      exact h1
  · exact ⟨_, isUniqueInvolution_range_sl2 hodd
      (slShort_injective hσ)⟩

theorem exists_perfect_fund_of_involution (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {u : (modelUniv .trialityD4 0 p e Fact.out).K} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D,
      ⁅R, R⁆ = R ∧ IsUniqueInvolution R u := by
  obtain ⟨R₀, hR₀, hperf, c₀, hc₀⟩ := exists_short_fund_trialityD4 hp2 hadm
  obtain ⟨g, hg⟩ : ∃ g : (modelUniv .trialityD4 0 p e Fact.out).K, g * c₀ * g⁻¹ = u :=
    Balance.Bootstrap.trialityD4_involutions_conj hp2 hadm.2.1
      (x := c₀) (x' := u) hc₀.sq hu hc₀.ne_one hu1
  refine ⟨conjSub g R₀, RouteD.conjSub_mem_fundamentalSubgroups hR₀ g, ?_, ?_⟩
  · show ⁅R₀.map (MulAut.conj g).toMonoidHom, R₀.map (MulAut.conj g).toMonoidHom⁆ =
      R₀.map (MulAut.conj g).toMonoidHom
    rw [← Subgroup.map_commutator, hperf]
  · have := hc₀.conj g
    rwa [hg] at this

end Existence

section Centralizers

theorem eq_of_centralizer_eq_td4 (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {u₁ u₂ : (modelUniv .trialityD4 0 p e Fact.out).K} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (h₁1 : u₁ ≠ 1) (h₂1 : u₂ ≠ 1)
    (h : Subgroup.centralizer ({u₁} : Set (modelUniv .trialityD4 0 p e Fact.out).K) =
      Subgroup.centralizer ({u₂} : Set (modelUniv .trialityD4 0 p e Fact.out).K)) : u₁ = u₂ := by
  obtain ⟨R, -, hperf, hR⟩ := exists_perfect_fund_of_involution hp2 hadm h₁ h₁1
  have hRc₁ : ∀ r ∈ R, u₁ * r = r * u₁ := fun r hr => isUniqueInvolution_central hR hr
  have hRc₂ : ∀ r ∈ R, u₂ * r = r * u₂ := by
    intro r hr
    have h1 : r ∈ Subgroup.centralizer ({u₁} : Set (modelUniv .trialityD4 0 p e Fact.out).K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hRc₁ r hr).symm
    rw [h, Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1.symm
  exact ModelFacts.trialityD4_eq_of_central_in_perfect p e hp2 hadm.2.1 hperf h₂ h₂1 h₁1 hR.mem
    hRc₁ hRc₂

theorem centralizer_isCoatom_td4 (hM : G2D4MaxNormalizer p) (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {u : (modelUniv .trialityD4 0 p e Fact.out).K} (hu : u * u = 1) (hu1 : u ≠ 1) :
    IsCoatom (Subgroup.centralizer ({u} : Set (modelUniv .trialityD4 0 p e Fact.out).K)) := by
  obtain ⟨R, hR, -, hRu⟩ := exists_perfect_fund_of_involution hp2 hadm hu hu1
  rw [← normalizer_eq_centralizer_model hM hadm hp2 (Or.inr rfl) hR hRu]
  exact hM .trialityD4 0 e hadm hp2 (Or.inr rfl) R hR

theorem involutionCentralizersGenerate_td4_of_maxNormalizer (hM : G2D4MaxNormalizer p)
    (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    InvolutionCentralizersGenerate (modelUniv .trialityD4 0 p e Fact.out).K := by
  intro u₁ u₂ hu₁ hu₂ hu₁1 hu₂1 hne _
  by_contra hS
  set S := Subgroup.centralizer ({u₁} : Set (modelUniv .trialityD4 0 p e Fact.out).K) ⊔
    Subgroup.centralizer ({u₂} : Set (modelUniv .trialityD4 0 p e Fact.out).K) ⊔
    Subgroup.centralizer ({u₁ * u₂} : Set (modelUniv .trialityD4 0 p e Fact.out).K) with hSdef
  have h1 : S = Subgroup.centralizer ({u₁} : Set (modelUniv .trialityD4 0 p e Fact.out).K) :=
    ((centralizer_isCoatom_td4 hM hp2 hadm hu₁ hu₁1).le_iff.mp
      ((le_sup_left : _ ≤ _ ⊔ _).trans le_sup_left)).resolve_left hS
  have h2 : S = Subgroup.centralizer ({u₂} : Set (modelUniv .trialityD4 0 p e Fact.out).K) :=
    ((centralizer_isCoatom_td4 hM hp2 hadm hu₂ hu₂1).le_iff.mp
      ((le_sup_right : _ ≤ _ ⊔ _).trans le_sup_left)).resolve_left hS
  exact hne (eq_of_centralizer_eq_td4 hp2 hadm hu₁ hu₂ hu₁1 hu₂1 (h1.symm.trans h2))

end Centralizers

section D4Three

@[expose] def TD4ThreeOddCore : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), StatedLieAdmissible .trialityD4 n p e → p ^ e = 3 →
    InvolutionOddCoreTrivial (modelUniv .trialityD4 n p e hp).K

theorem d4ThreeCentralizerFacts_of_maxNormalizer [Fact (Nat.Prime 3)]
    (hM : G2D4MaxNormalizer 3) (hB : TD4ThreeOddCore) : D4ThreeCentralizerFacts := by
  intro n p e hp hadm he3
  have hn : n = 0 := hadm.2.2
  subst hn
  have hp3 : p = 3 := by
    have he : e ≠ 0 := by
      have := hadm.2.1
      omega
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (he3 ▸ dvd_pow_self p he)
  subst hp3
  exact ⟨hB 0 3 e hp hadm he3,
    involutionCentralizersGenerate_td4_of_maxNormalizer hM (by norm_num) hadm⟩

end D4Three

end CFSG.ClassicalInvolution.G2D4Models
