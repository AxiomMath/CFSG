module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSpDiag

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Balance
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

@[expose] def SpComplexOddFree (F : Type) [Field F] (n : ℕ) : Prop :=
  ∀ g : StatedSp n F, mat n F g * mat n F g = -1 →
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g : StatedSp n F ⧸ Subgroup.center (StatedSp n F))} :
        Set (StatedSp n F ⧸ Subgroup.center (StatedSp n F)))) = ⊥

section Assembly

variable {F : Type} [Field F] [Finite F]

theorem oddCoreIn_centralizer_eq_bot_of_sp_orderOf_eq_two (hF : Nat.card F = 3) {n : ℕ}
    (hn : 1 ≤ n) (hB : SpComplexOddFree F n)
    (s : StatedSp n F ⧸ Subgroup.center (StatedSp n F)) (hs : orderOf s = 2) :
    oddCoreIn (Subgroup.centralizer ({s} : Set (StatedSp n F ⧸ Subgroup.center (StatedSp n F)))) =
      ⊥ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hs2 : (QuotientGroup.mk g : StatedSp n F ⧸ Subgroup.center (StatedSp n F)) ^ 2 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one _
  have hs1 : (QuotientGroup.mk g : StatedSp n F ⧸ Subgroup.center (StatedSp n F)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  have hgc : g ∉ Subgroup.center (StatedSp n F) := fun h => hs1 ((QuotientGroup.eq_one_iff g).mpr h)
  have hg2c : g * g ∈ Subgroup.center (StatedSp n F) :=
    (QuotientGroup.eq_one_iff (g * g)).mp (by rw [QuotientGroup.mk_mul, ← pow_two]; exact hs2)
  obtain ⟨c, hc⟩ := exists_smul_of_mem_center hg2c
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : mat n F (g * g) * mat n F (g * g)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hc, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hcc : c * c = 1 := by
    have : Fintype F := Fintype.ofFinite F
    have h1 := FiniteField.pow_card_sub_one_eq_one c hc0
    rw [← Nat.card_eq_fintype_card, hF] at h1
    simpa [pow_two] using h1
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · refine oddCoreIn_centralizer_eq_bot_of_sp_sq_eq_one hF ?_ hgc
    apply mat_injective
    rw [map_mul, map_one]
    rw [map_mul] at hc
    rw [hc, h1, one_smul]
  · exact hB g (by rw [← map_mul, hc, h1, neg_one_smul])

end Assembly

theorem simpleOddCentralizerFreeTag_PSp_of_complex
    (hB : ∀ n, 2 ≤ n → SpComplexOddFree (GaloisField 3 1) n) :
    SimpleOddCentralizerFreeTag .PSp := by
  intro n hp hadm s hs
  have hn : 2 ≤ n := by
    obtain ⟨_, _, h2n, _⟩ := hadm
    exact h2n
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    simpa using GaloisField.card 3 1 one_ne_zero
  exact oddCoreIn_centralizer_eq_bot_of_sp_orderOf_eq_two hF (by omega) (hB n hn) s hs

end CFSG.ClassicalInvolution.Q3
