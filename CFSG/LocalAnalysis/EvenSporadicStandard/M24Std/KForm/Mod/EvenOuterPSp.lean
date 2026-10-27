module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSUPSp

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.SeitzReduction
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem psp_outer_fixed_rank_even {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel J .PSp n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (e / 2) ∧ 2 * (e / 2) = e ∧
        Nonempty (fixedSubgroup α ≃* StatedSp n k)) ∨
      (IsSimpleGroup (fixedSubgroup α) ∧ StatedLieAdmissible .twistedB2 0 2 e ∧
        LieModel (fixedSubgroup α) .twistedB2 0 2 e) := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hnf : (n, 2 ^ e) ≠ (2, 2) := hadm.2.2.2
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite J := Finite.of_equiv _ eJ.symm.toEquiv
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α * MulAut.congr eJ α = 1 := by
    rw [← sq, ← hβ, pow_orderOf_eq_one]
  have hβo : MulAut.congr eJ α ∉ inner (StatedProj (StatedSp n K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  let Ψ := fixedSubgroupCongrEquiv eJ α
  have hE : MulAut.congr eJ α ∈ spSemilinearAutGroup n K →
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (e / 2) ∧ 2 * (e / 2) = e ∧
        Nonempty (fixedSubgroup α ≃* StatedSp n k) := by
    intro hmem
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    obtain ⟨k, _, _, hk, hpar, ⟨Φ⟩⟩ := F4Pilot.psp_field_fixed hn hf hK hβ2 g σ hgσ hσ
    exact ⟨k, inferInstance, inferInstance, hk, hpar.symm, ⟨Ψ.trans Φ⟩⟩
  by_cases hn3 : 3 ≤ n
  · left
    apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
    exact mem_top _
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    rcases Nat.even_or_odd e with hfe | hfo
    · exact Or.inl (hE (heven hfe _ hβ))
    · obtain ⟨s, hs⟩ := hodd hfo _ hβ hβo
      obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h0
        obtain rfl : m = 0 := by omega
        exact hnf rfl
      rw [eq_exceptionalAut hγ] at hs
      obtain ⟨hS, hadmB, hLie⟩ := LinearPilot.psp_suzuki_fixed hm hK hβ2 s hs
      exact Or.inr ⟨Ψ.isSimpleGroup, hadmB, LieType.CurtisTits.lieModel_of_mulEquiv Ψ.symm hLie⟩

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
