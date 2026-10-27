module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOGeneric
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE7Coroot

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ComponentClassification.HarrisLit.T1.P54.F3.E7Three


theorem hasPOmegaMember_of_lieModel_e7 {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (h : CFSG.Blueprint.LieModel Q .E7 0 3 1) : HasPOmegaMember Q := by
  obtain ⟨α, hα, hαk⟩ : ∃ α : E7sc 3 1 →* Q, Function.Surjective α ∧
      α.ker ≤ Subgroup.center (E7sc 3 1) :=
    CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover .E7 0 3 1 Nat.prime_three
      (by norm_num) trivial ⟨Nat.prime_three, le_rfl, rfl⟩ Q h
  obtain ⟨u, hu, hu2⟩ := exists_involution_std3 isRoot_thetaE7
  have huHJ : u ∈ HJ 3 1 := involution_theta_mem_HJ hu hu2
  have huZ : u ∉ Subgroup.center (E7sc 3 1) := fun hc => by
    rw [no_central_fund3 e7_fund_class3.2 hu hc, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hu1 : α u ≠ 1 := fun h1 => huZ (hαk h1)
  have hmul : u * u = 1 := by
    rw [← sq]
    exact hu2 ▸ pow_orderOf_eq_one u
  have hle : HJ 3 1 ≤ Subgroup.centralizer {u} := HJ_le_centralizer3 hu
  have hn : ∀ g ∈ Subgroup.centralizer {u}, ∀ j ∈ HJ 3 1, g * j * g⁻¹ ∈ HJ 3 1 :=
    fun g hg j hj => conjSub_HJ_le3 hu hu2 (Subgroup.mem_centralizer_singleton_iff.1 hg)
      (conj_mem_conjSub hj)
  have hnorm : ((HJ 3 1).subgroupOf (Subgroup.centralizer {u})).Normal :=
    (Subgroup.normal_subgroupOf_iff hle).2 fun j a hj ha => hn a ha j hj
  obtain ⟨hQ₂, hZ₂, hL₂⟩ := hj_facts3
  exact hasPOmegaMember_of_cover_block α hα hαk (HJ 3 1) u huHJ hmul hu1 hle hnorm
    ⟨hQ₂, hZ₂, 6, Or.inr rfl, hL₂⟩

end CFSG.OddStandard.HigherRank.F3
