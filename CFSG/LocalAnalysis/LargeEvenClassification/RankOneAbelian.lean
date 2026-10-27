module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianNormalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.ConjugationGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreTwoSubgroups

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem pGroup_generator_rank_one_cyclic {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (hrank : pGeneratorRank prime Ambient ≤ 1) : IsCyclic Ambient := by
  classical
  obtain ⟨generators, hgenerates, hcard⟩ := pGeneratorRank_generators hprime hpgroup
  obtain ⟨generator, hsubset⟩ := Finset.card_le_one_iff_subset_singleton.mp (hcard.le.trans hrank)
  have hclosureLe : Subgroup.closure (generators : Set Ambient) ≤ Subgroup.zpowers generator := by
    apply (Subgroup.closure_le _).mpr
    intro element helement
    have heq : element = generator := Finset.mem_singleton.mp (hsubset helement)
    exact heq ▸ Subgroup.mem_zpowers generator
  have htop : Subgroup.zpowers generator = ⊤ := top_unique (hgenerates ▸ hclosureLe)
  exact IsCyclic.mk ⟨generator, fun element => by
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top element)
    exact ⟨exponent, hexponent⟩⟩

theorem rank_one_abelian_subgroup_cyclic {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (Whole Abelian : Subgroup Ambient) (hle : Abelian ≤ Whole)
    (hpgroup : IsPGroup 2 Whole) (hrank : pRank 2 Whole ≤ 1)
    (hcommutative : IsMulCommutative Abelian) : IsCyclic Abelian := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup Abelian := { (inferInstance : Group Abelian) with
    mul_comm := @mul_comm' Abelian _ hcommutative }
  let Elementary := normalElementarySquareKernel Abelian hcommutative
  have helementaryLe : Elementary ≤ Abelian := Subgroup.map_subtype_le _
  have helementary := normalElementarySquareKernel_elementary Abelian hcommutative
  have helementaryPGroup : IsPGroup 2 Elementary :=
    (hpgroup.to_le hle).to_le helementaryLe
  obtain ⟨rank, hcard⟩ := helementaryPGroup.exists_card_eq
  have helementaryRank : rank ≤ 1 := by
    have hbound := pRank_mono (by decide : 1 < 2) (helementaryLe.trans hle)
    rw [elementary_pRank_card (by decide : 1 < 2) Elementary helementary hcard] at hbound
    exact hbound.trans hrank
  have hkernelCard : Nat.card (powMonoidHom 2 : Abelian →* Abelian).ker = 2 ^ rank := by
    exact (Nat.card_congr ((powMonoidHom 2 : Abelian →* Abelian).ker.equivMapOfInjective
      Abelian.subtype Abelian.subtype_injective).toEquiv).trans hcard
  have hgeneratorRank : pGeneratorRank 2 Abelian = rank := by
    unfold pGeneratorRank
    rw [commutative_frattini_card_eq_power_kernel Nat.prime_two (hpgroup.to_le hle), hkernelCard]
    exact Nat.log_pow (by decide : 1 < 2) rank
  exact pGroup_generator_rank_one_cyclic Nat.prime_two (hpgroup.to_le hle)
    (hgeneratorRank ▸ helementaryRank)

theorem rank_one_two_group_abelian_normal_cyclic {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1) :
    ∃ Normal : Subgroup Ambient, Normal.Normal ∧ IsCyclic Normal ∧
      Subgroup.centralizer (Normal : Set Ambient) = Normal := by
  have hbot : (⊥ : Subgroup Ambient).Normal ∧ IsMulCommutative (⊥ : Subgroup Ambient) :=
    ⟨inferInstance, inferInstance⟩
  obtain ⟨Normal, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun Normal : Subgroup Ambient => Normal.Normal ∧ IsMulCommutative Normal) hbot
  obtain ⟨hnormal, hcommutative⟩ := hmaximal.prop
  let := hnormal
  have hcyclic : IsCyclic Normal := rank_one_abelian_subgroup_cyclic (⊤ : Subgroup Ambient) Normal le_top
    (hpgroup.to_subgroup ⊤) hrank hcommutative
  have hselfCentralizing := maximal_abelian_normal_selfCentralizing Nat.prime_two hpgroup Normal
    hcommutative (fun Larger hnormalLarger hcommutativeLarger hlarger =>
      hmaximal.2 ⟨hnormalLarger, hcommutativeLarger⟩ hlarger)
  exact ⟨Normal, hnormal, hcyclic, hselfCentralizing⟩

theorem rank_one_two_group_three_generators {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (Candidate : Subgroup Ambient) :
    ∃ generators : Finset Candidate,
      Subgroup.closure (generators : Set Candidate) = ⊤ ∧ generators.card ≤ 3 := by
  obtain ⟨Normal, hnormal, hcyclic, hselfCentralizing⟩ :=
    rank_one_two_group_abelian_normal_cyclic hpgroup hrank
  let := hnormal
  let := hcyclic
  exact selfCentralizing_conj_subgroup_generator_bound Nat.prime_two hpgroup Normal inferInstance
    hselfCentralizing Candidate (cyclic_pGeneratorRank_le_one Nat.prime_two (hpgroup.to_subgroup Normal))
    (cyclic_two_aut_subgroup_generator_rank (hpgroup.to_subgroup Normal)
      ((MulAut.conjNormal (H := Normal)).comp Candidate.subtype).range)

theorem rank_one_two_group_generator_rank_le_three {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1) :
    pGeneratorRank 2 Ambient ≤ 3 := by
  obtain ⟨generators, hgenerates, hcard⟩ := rank_one_two_group_three_generators hpgroup hrank ⊤
  have hbound : pGeneratorRank 2 (⊤ : Subgroup Ambient) ≤ 3 :=
    (pGeneratorRank_le_generators Nat.prime_two (hpgroup.to_subgroup ⊤) generators hgenerates).trans hcard
  rw [← pGeneratorRank_mulEquiv Nat.prime_two hpgroup (Subgroup.topEquiv.symm)] at hbound
  exact hbound

end CFSG.LargeEvenClassification.Helpers
