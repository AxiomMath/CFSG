module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQGen
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outNoA4_statedProj_sp {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hr : 2 ≤ r) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) :
    OutNoA4 (StatedProj (StatedSp r K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : NeZero r := ⟨by omega⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  obtain ⟨-, -, hDn, -, ⟨g, -, hg⟩, -⟩ := standard_outer_quotient (K := K) (by omega : 1 ≤ r)
  have hE : spSemilinearAutGroup r K = ⊤ := eq_top_iff.mpr fun α _ =>
    mem_spSemilinearAutGroup_iff.mpr
      (CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard
        hodd hr α)
  have hD : (spLinearAutGroup r K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ spSemilinearAutGroup r K := hE ▸ Subgroup.mem_top γ
    have hd' : d ∈ spSemilinearAutGroup r K := hE ▸ Subgroup.mem_top d
    exact mem_subgroupOf.mp (hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩)
  have hcard : Nat.card (spLinearAutGroup r K ⧸
      (inner (StatedProj (StatedSp r K))).subgroupOf (spLinearAutGroup r K)) ∣ 2 :=
    (relIndex_inner_spLinearAutGroup_dvd (r := r) hℓ hf hK).trans (Nat.gcd_dvd_left 2 _)
  have : IsCyclic (MulAut (StatedProj (StatedSp r K)) ⧸ spLinearAutGroup r K) :=
    isCyclic_quotient_of_exists_zpow_top ⟨g, fun x => hg x (hE ▸ Subgroup.mem_top x)⟩
  exact outNoA4_of_ker_cyclic (QuotientGroup.mk' (spLinearAutGroup r K)) mul_comm_of_isCyclic
    (QuotientGroup.ker_mk' _).le (isCyclic_of_card_dvd_prime Nat.prime_two hcard)

theorem outNoA4_of_statedClassicalModel_PSp {S : Type} [Group S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hS : StatedClassicalModel S .PSp n p f) : OutNoA4 S := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hS
  exact OutNoA4.of_mulEquiv e.symm (outNoA4_statedProj_sp hp hp2 hf hn hK)

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
