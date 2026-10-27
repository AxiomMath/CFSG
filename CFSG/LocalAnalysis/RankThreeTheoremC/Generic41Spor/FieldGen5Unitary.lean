module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.HyperCoverUnitary
public import CFSG.LieType.SeitzGeneration.OuterSUData
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration

private theorem card_map_of_forall_eq_one {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (A : Subgroup G) (hA : ∀ x ∈ A, φ x = 1 → x = 1) : Nat.card (A.map φ) = Nat.card A := by
  have hinj : Function.Injective (φ.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hA x x.2 hx)
  rw [show A.map φ = (φ.comp A.subtype).range by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem exists_isElemAbelian_cube_of_statedClassicalModel_PSU {L : Type} [Group L] {n ℓ f p : ℕ}
    (hM : StatedClassicalModel L .PSU n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2 ∨ 6 ≤ n) :
    ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  obtain ⟨⟨hℓ, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨A, hAa, hAc, hAs, -⟩ := exists_hyperGen_su h hn hp hp2 hpq hq
  let π : unitarySU ℓ f K n →* StatedProj (StatedSU n (ℓ ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n))
  refine ⟨(A.map π).map e.symm.toMonoidHom, (hAa.map π).map _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective,
    card_map_of_forall_eq_one π A (fun x hx h1 => hAs x hx ((QuotientGroup.eq_one_iff x).1 h1)),
    hAc]

section Unitary


theorem fieldAutData_five_psu {L : Type} [Group L] [Finite L] {n ℓ f : ℕ}
    (hM : CFSG.Open.StatedClassicalModel L .PSU n ℓ f) (hℓ : ℓ ≠ 5)
    (hcyc : ∀ S : Sylow 5 L, IsCyclic (S : Subgroup L)) :
    CFSG.RankThree.PartOne.CTP.FieldAutData L 5 := by
  obtain ⟨-, -, hn3, hne, K, _, h, ⟨θ⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU hM
  have hg : ¬ 5 ∣ Nat.gcd n (ℓ ^ f + 1) := by
    intro hd
    have h1 := hd.trans (Nat.gcd_dvd_left _ _)
    have h2 := hd.trans (Nat.gcd_dvd_right _ _)
    have hn5 : 5 ≤ n := Nat.le_of_dvd (by omega) h1
    have hq2 : ℓ ^ f ≠ 2 := fun hq => by
      rw [hq] at h2
      omega
    obtain ⟨E, hE, hEc⟩ := exists_isElemAbelian_cube_of_statedClassicalModel_PSU hM
      Nat.prime_five (by norm_num) (by omega) h2 (Or.inl hq2)
    exact false_of_isElemAbelian_of_cyclic_sylow hcyc hE (by rw [hEc]; norm_num)
  exact (fieldAutData_primeFormP_odd (subfieldPairSUOdd
    CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds) hn3 h hne
    Nat.prime_five (by norm_num) (Ne.symm hℓ) hg).of_mulEquiv θ Nat.prime_five

end Unitary

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
