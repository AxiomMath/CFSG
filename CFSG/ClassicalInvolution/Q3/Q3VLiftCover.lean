module

public import CFSG.ClassicalInvolution.Q3.Q3ZLiftCover

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Lift

open CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.Q3Z (exists_lift_of_coprime)
open scoped MatrixGroups

private theorem card_sl2_three : Nat.card SL(2, GaloisField 3 1) = 24 := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  norm_num

theorem isPerfect_sp_three {m : ℕ} (hm : 2 ≤ m) :
    Group.IsPerfect (StatedSp m (GaloisField 3 1)) := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  exact (CFSG.LieType.Universal.Symplectic.isQuasisimple m (GaloisField 3 1) (by omega)
    (Or.inr (Or.inl ⟨hF, hm⟩))).1

theorem spR_three_noCover (m : ℕ) :
    NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (StatedSp m (GaloisField 3 1)) := by
  intro E _ _ _ π hπ hcen ⟨hodd, h3⟩
  have hcop : Nat.Coprime (Nat.card π.ker) (Nat.card SL(2, GaloisField 3 1)) := by
    rw [card_sl2_three, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 ?_) ?_
    · exact Nat.coprime_two_right.mpr hodd
    · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have hlift : ∀ ρ : SL(2, GaloisField 3 1) →* StatedSp m (GaloisField 3 1),
      ∃ ρ' : SL(2, GaloisField 3 1) →* E, ∀ g, π (ρ' g) = ρ g := fun ρ => by
    obtain ⟨β, hβ⟩ := exists_lift_of_coprime π hπ hcop ρ
    exact ⟨β, fun g => DFunLike.congr_fun hβ g⟩
  obtain ⟨σ, hσ, -⟩ := sp_existsUnique_section_of_sl2_lift m hπ hcen h3 hlift
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

end CFSG.ClassicalInvolution.Q3.Q3V.Lift
