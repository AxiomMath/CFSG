module

public import CFSG.LocalAnalysis.ComponentClassification.BlockPairSylowOmega

public section

open CFSG.Open

namespace CFSG.ComponentClassification.CommonInvolutionSubgroup

@[expose] noncomputable def sylowImage {G : Type*} [Group G] (subgroup : Subgroup G) (sylow : Sylow 2 subgroup) : Subgroup G :=
  (sylow : Subgroup subgroup).map subgroup.subtype

theorem exists_common {G Index : Type*} [Group G] [Finite G] [Fintype Index]
    (hcard : 3 ≤ Fintype.card Index) (normalizers overlaps : Index → Subgroup G)
    (hcontained : ∀ index, normalizers index ≤ overlaps index)
    (hcoverage : ∀ index, ∀ member ∈ overlaps index, orderOf member = 2 → member ∈ normalizers index)
    (rank : ℕ) (hrank : ∀ index, pRank 2 (normalizers index) = rank)
    (hpair : ∀ first second : Index, first ≠ second →
      ∀ firstSylow : Sylow 2 (normalizers first), ∀ secondSylow : Sylow 2 (normalizers second),
        IsMulCommutative ↥(sylowImage (normalizers first) firstSylow ⊔ sylowImage (normalizers second) secondSylow) ∧
        InvolutionGeneratedSubgroup.omega (sylowImage (normalizers first) firstSylow) =
          InvolutionGeneratedSubgroup.omega (sylowImage (normalizers second) secondSylow)) :
    ∃ elementary : Subgroup G, IsElemAbelian 2 elementary ∧ Nat.card elementary = 2 ^ rank ∧
      (∀ index, elementary ≤ overlaps index) ∧
      (∀ index, ∀ sylow : Sylow 2 (normalizers index),
        InvolutionGeneratedSubgroup.omega (sylowImage (normalizers index) sylow) = elementary) ∧
      (∀ index, ∀ member : G, member ∈ overlaps index ∧ orderOf member = 2 ↔
        member ∈ elementary ∧ member ≠ 1) := by
  classical
  have hnonempty : Nonempty Index := Fintype.card_pos_iff.mp (by omega)
  let base : Index := Classical.choice hnonempty
  obtain ⟨other, hother, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hcard base base
  let baseSylow : Sylow 2 (normalizers base) := Classical.choice inferInstance
  let otherSylow : Sylow 2 (normalizers other) := Classical.choice inferInstance
  let baseImage := sylowImage (normalizers base) baseSylow
  let otherImage := sylowImage (normalizers other) otherSylow
  let elementary := InvolutionGeneratedSubgroup.omega baseImage
  have hbasePair := hpair base other hother.symm baseSylow otherSylow
  have hbaseAb : IsMulCommutative baseImage := BlockPairSylowOmega.abelian_of_le le_sup_left hbasePair.1
  have hcommon : ∀ index, ∀ sylow : Sylow 2 (normalizers index),
      InvolutionGeneratedSubgroup.omega (sylowImage (normalizers index) sylow) = elementary := by
    intro index sylow
    by_cases heq : index = base
    · subst index
      exact ((hpair base other hother.symm sylow otherSylow).2).trans hbasePair.2.symm
    · exact (hpair index base heq sylow baseSylow).2
  have hab : ∀ index, ∀ sylow : Sylow 2 (normalizers index),
      IsMulCommutative (sylowImage (normalizers index) sylow) := by
    intro index sylow
    obtain ⟨different, hdifferent, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hcard index index
    let differentSylow : Sylow 2 (normalizers different) := Classical.choice inferInstance
    exact BlockPairSylowOmega.abelian_of_le le_sup_left (hpair index different hdifferent.symm sylow differentSylow).1
  have helementary := InvolutionGeneratedSubgroup.elementary baseImage hbaseAb
  have hsize : Nat.card elementary = 2 ^ rank := by
    rw [InvolutionGeneratedSubgroup.card baseImage hbaseAb]
    change 2 ^ pRank 2 ((baseSylow : Subgroup (normalizers base)).map (normalizers base).subtype) = 2 ^ rank
    rw [InvolutionGeneratedSubgroup.sylow_rank_eq (normalizers base) baseSylow, hrank]
  have hle : ∀ index, elementary ≤ overlaps index := by
    intro index
    let sylow : Sylow 2 (normalizers index) := Classical.choice inferInstance
    rw [← hcommon index sylow]
    apply (InvolutionGeneratedSubgroup.le _).trans
    rintro member ⟨lift, hlift, rfl⟩
    exact hcontained index lift.property
  refine ⟨elementary, helementary, hsize, hle, hcommon, ?_⟩
  intro index member
  constructor
  · rintro ⟨hmember, horder⟩
    have hnormalizer := hcoverage index member hmember horder
    have hcyclic : Subgroup.zpowers member ≤ normalizers index := Subgroup.zpowers_le.mpr hnormalizer
    have hcyclicTwo : IsPGroup 2 (Subgroup.zpowers member) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, horder]
      rfl
    obtain ⟨sylow, hcyclicSylow⟩ := (hcyclicTwo.comap_subtype (K := normalizers index)).exists_le_sylow
    have hmem : member ∈ sylowImage (normalizers index) sylow := by
      apply Subgroup.mem_map.mpr
      refine ⟨⟨member, hnormalizer⟩, ?_, rfl⟩
      exact hcyclicSylow (Subgroup.mem_zpowers member)
    have hsquare : member ^ 2 = 1 := by rw [← horder]; exact pow_orderOf_eq_one member
    have homega := (InvolutionGeneratedSubgroup.mem_iff _ (hab index sylow) member).mpr ⟨hmem, hsquare⟩
    rw [hcommon index sylow] at homega
    refine ⟨homega, ?_⟩
    intro hone
    rw [hone, orderOf_one] at horder
    omega
  · rintro ⟨hmember, hne⟩
    exact ⟨hle index hmember, orderOf_eq_prime (helementary.2 member hmember) hne⟩

end CFSG.ComponentClassification.CommonInvolutionSubgroup
