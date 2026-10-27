module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Cover
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL2
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg

universe u

theorem exists_finset_card_four {K : Type} [Field K] [Finite K] (h5 : 5 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  have h : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h
  exact ⟨s, hs⟩

theorem sp4_noCover_pPrime {K : Type} [Field K] {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K) :
    NoCover.{u} (fun n => Odd n ∧ ¬ p ∣ n) (StatedSp 2 K) := by
  intro E _ _ _ π hπ hcen hQ
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.out.ne_zero)
  have : CharP K p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h5)
  have hdiv : ∀ m n : ℕ, m ∣ n → (Odd n ∧ ¬ p ∣ n) → (Odd m ∧ ¬ p ∣ m) :=
    fun m n hmn ⟨ho, hn⟩ => ⟨ho.of_dvd_nat hmn, fun h => hn (h.trans hmn)⟩
  have hlift : ∀ ρ : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K,
      ∃ ρ' : Matrix.SpecialLinearGroup (Fin 2) K →* E, ∀ g, π (ρ' g) = ρ g := fun ρ => by
    obtain ⟨β, hβ⟩ := exists_lift_of_noCover (Q := fun n => Odd n ∧ ¬ p ∣ n) hdiv
      (sl2_noCover hp2 hK) π hπ hcen hQ ρ
    exact ⟨β, fun g => DFunLike.congr_fun hβ g⟩
  obtain ⟨σ, hσ, -⟩ := sp_existsUnique_section_of_sl2_lift 2 hπ hcen hQ.2 hlift
  have htop : σ.range = ⊤ := by
    refine eq_top_of_perfect_of_central hcen (S := σ.range) (Z := π.ker) fun e => ?_
    refine ⟨σ (π e), ⟨_, rfl⟩, (σ (π e))⁻¹ * e, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨x, rfl⟩ : c ∈ σ.range := by rw [htop]; trivial
  rw [MonoidHom.mem_ker, hσ] at hc
  rw [hc, map_one]
  exact Subgroup.one_mem _

theorem sp4_noCover_odd {K : Type} [Field K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K) : NoCover.{u} Odd (StatedSp 2 K) := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hK
      omega
    · exact h
  refine NoCover.odd_of_pPrime (p := p) ?_ (sp4_noCover_pPrime hp2 hK h5)
  intro E _ _ _ π hπ hcen ⟨k, hk⟩
  refine sp4_ker_eq_bot_of_isPGroup hπ hcen hK hf h5 ?_
  exact IsPGroup.of_card hk

end CFSG.ClassicalInvolution.ModelFacts.OddCover
