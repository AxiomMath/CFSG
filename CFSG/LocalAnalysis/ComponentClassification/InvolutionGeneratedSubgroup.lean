module

public import CFSG.LocalAnalysis.ComponentClassification.TwoRankSylow
public import CFSG.LocalAnalysis.ComponentClassification.ElementaryAbelianModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.Open

namespace CFSG.ComponentClassification.InvolutionGeneratedSubgroup

@[expose] noncomputable def omega {G : Type*} [Group G] (subgroup : Subgroup G) : Subgroup G :=
  Subgroup.closure {member : G | member ∈ subgroup ∧ member ^ 2 = 1}

theorem le {G : Type*} [Group G] (subgroup : Subgroup G) : omega subgroup ≤ subgroup := by
  apply (Subgroup.closure_le _).mpr
  intro member hmember
  exact hmember.1

theorem mem_iff {G : Type*} [Group G] (subgroup : Subgroup G) (hab : IsMulCommutative subgroup)
    (member : G) : member ∈ omega subgroup ↔ member ∈ subgroup ∧ member ^ 2 = 1 := by
  let squares : Subgroup G :=
    { carrier := {member : G | member ∈ subgroup ∧ member ^ 2 = 1}
      one_mem' := ⟨subgroup.one_mem, one_pow 2⟩
      mul_mem' := by
        intro first second hfirst hsecond
        refine ⟨subgroup.mul_mem hfirst.1 hsecond.1, ?_⟩
        have hcommute : Commute first second := congrArg Subtype.val
          (isMulCommutative_iff.mp hab (⟨first, hfirst.1⟩ : subgroup) (⟨second, hsecond.1⟩ : subgroup))
        rw [hcommute.mul_pow, hfirst.2, hsecond.2, one_mul]
      inv_mem' := by
        intro member hmember
        exact ⟨subgroup.inv_mem hmember.1, by rw [inv_pow, hmember.2, inv_one]⟩ }
  constructor
  · intro hmember
    have hle : omega subgroup ≤ squares := (Subgroup.closure_le _).mpr (fun element helement => helement)
    exact hle hmember
  · intro hmember
    exact Subgroup.subset_closure hmember

theorem elementary {G : Type*} [Group G] (subgroup : Subgroup G) (hab : IsMulCommutative subgroup) :
    IsElemAbelian 2 (omega subgroup) := by
  constructor
  · apply isMulCommutative_iff.mpr
    intro first second
    apply Subtype.ext
    change first.val * second.val = second.val * first.val
    exact congrArg Subtype.val (isMulCommutative_iff.mp hab
      (⟨first.val, le subgroup first.property⟩ : subgroup) (⟨second.val, le subgroup second.property⟩ : subgroup))
  · intro member hmember
    exact ((mem_iff subgroup hab member).mp hmember).2

theorem card {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G) (hab : IsMulCommutative subgroup) :
    Nat.card (omega subgroup) = 2 ^ pRank 2 subgroup := by
  have helementary := elementary subgroup hab
  let : CommGroup (omega subgroup) := ElementaryAbelianModule.subgroupCommGroup _ helementary.1
  have hpower : ∀ member : omega subgroup, member ^ 2 = 1 := by
    intro member
    apply Subtype.ext
    exact helementary.2 member.val member.property
  let : Module (ZMod 2) (Additive (omega subgroup)) := ElementaryAbelianModule.moduleStructure 2 hpower
  have hcard := ElementaryAbelianModule.card_eq_pow_finrank (G := omega subgroup) 2
  have hupper : pRank 2 subgroup ≤ Module.finrank (ZMod 2) (Additive (omega subgroup)) := by
    obtain ⟨elementary, hle, helementary, hsize⟩ := TwoRankTransport.witness subgroup
    have hleOmega : elementary ≤ omega subgroup := by
      intro member hmember
      exact (mem_iff subgroup hab member).mpr ⟨hle hmember, helementary.2 member hmember⟩
    have hsizeBound := Nat.card_le_card_of_injective (Subgroup.inclusion hleOmega) (Subgroup.inclusion_injective hleOmega)
    rw [hsize, hcard] at hsizeBound
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hsizeBound
  have hlower := TwoRankTransport.rank_le subgroup (omega subgroup) (le subgroup) helementary _ hcard
  rw [le_antisymm hlower hupper] at hcard
  exact hcard

theorem mono {G : Type*} [Group G] {first second : Subgroup G} (hle : first ≤ second) :
    omega first ≤ omega second := by
  apply (Subgroup.closure_le _).mpr
  intro member hmember
  exact Subgroup.subset_closure ⟨hle hmember.1, hmember.2⟩

theorem map {G H : Type*} [Group G] [Group H] (subgroup : Subgroup G) (homomorphism : G →* H)
    (hinjective : Function.Injective homomorphism) :
    (omega subgroup).map homomorphism = omega (subgroup.map homomorphism) := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro member hmember
    apply Subgroup.subset_closure
    exact ⟨Subgroup.mem_map.mpr ⟨member, hmember.1, rfl⟩, by rw [← map_pow, hmember.2, map_one]⟩
  · apply (Subgroup.closure_le _).mpr
    rintro member ⟨⟨preimage, hpreimage, rfl⟩, hsquare⟩
    apply Subgroup.mem_map.mpr
    refine ⟨preimage, Subgroup.subset_closure ⟨hpreimage, ?_⟩, rfl⟩
    apply hinjective
    rw [map_pow, map_one]
    exact hsquare

theorem eq_of_rank {G : Type*} [Group G] [Finite G] {first second : Subgroup G}
    (hfirst : IsMulCommutative first) (hsecond : IsMulCommutative second)
    (hle : first ≤ second) (hrank : pRank 2 first = pRank 2 second) : omega first = omega second := by
  apply Subgroup.eq_of_le_of_card_ge (mono hle)
  rw [card first hfirst, card second hsecond, hrank]

theorem sylow_rank_eq {G : Type*} [Group G] [Finite G] (ambient : Subgroup G) (sylow : Sylow 2 ambient) :
    pRank 2 ((sylow : Subgroup ambient).map ambient.subtype) = pRank 2 ambient := by
  rw [← TwoRankTransport.subgroup, ← TwoRankTransport.subgroup]
  let equivalence := (sylow : Subgroup ambient).equivMapOfInjective ambient.subtype ambient.subtype_injective
  have hfirst := TwoRankTransport.injective equivalence.toMonoidHom equivalence.injective
  have hsecond := TwoRankTransport.injective equivalence.symm.toMonoidHom equivalence.symm.injective
  have heq : twoRank ((sylow : Subgroup ambient).map ambient.subtype) = twoRank (sylow : Subgroup ambient) :=
    le_antisymm hsecond hfirst
  rw [heq, TwoRankSylow.invariant]

theorem two_of_elementary {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G)
    (helementary : IsElemAbelian 2 subgroup) : IsPGroup 2 subgroup := by
  let : CommGroup subgroup := ElementaryAbelianModule.subgroupCommGroup _ helementary.1
  have hpower : ∀ member : subgroup, member ^ 2 = 1 := by
    intro member
    exact Subtype.ext (helementary.2 member.val member.property)
  let : Module (ZMod 2) (Additive subgroup) := ElementaryAbelianModule.moduleStructure 2 hpower
  exact IsPGroup.of_card (ElementaryAbelianModule.card_eq_pow_finrank (G := subgroup) 2)

theorem eq_of_elementary_card {G : Type*} [Group G] [Finite G]
    (subgroup elementary : Subgroup G) (hab : IsMulCommutative subgroup)
    (helementary : IsElemAbelian 2 elementary) (hcontained : elementary ≤ subgroup)
    (hsize : Nat.card elementary = 2 ^ pRank 2 subgroup) : omega subgroup = elementary := by
  have hle : elementary ≤ omega subgroup := by
    intro member hmember
    exact Subgroup.subset_closure ⟨hcontained hmember, helementary.2 member hmember⟩
  apply (Subgroup.eq_of_le_of_card_ge hle _).symm
  rw [card subgroup hab, hsize]

end CFSG.ComponentClassification.InvolutionGeneratedSubgroup
