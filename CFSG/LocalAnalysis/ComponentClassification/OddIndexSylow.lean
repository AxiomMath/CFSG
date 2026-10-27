module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.OddIndexSylow

theorem factorization {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G)
    (hodd : Odd subgroup.index) : (Nat.card subgroup).factorization 2 = (Nat.card G).factorization 2 := by
  have hcard : Nat.card subgroup ≠ 0 := ne_of_gt Nat.card_pos
  have hindex : subgroup.index ≠ 0 := by
    intro hzero
    have hproduct := subgroup.card_mul_index
    rw [hzero, mul_zero] at hproduct
    exact (ne_of_gt (Nat.card_pos (α := G))) hproduct.symm
  have hfactorization := congrArg (fun value : ℕ => value.factorization 2) subgroup.card_mul_index
  rw [Nat.factorization_mul hcard hindex, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero] at hfactorization
  exact hfactorization

@[expose] noncomputable def ambientSylow {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hodd : Odd subgroup.index) (sylow : Sylow 2 subgroup) : Sylow 2 G :=
  Sylow.ofCard ((sylow : Subgroup subgroup).map subgroup.subtype) (by
    rw [Subgroup.card_map_of_injective subgroup.subtype_injective, sylow.card_eq_multiplicity,
      factorization subgroup hodd])

theorem coe_ambientSylow {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hodd : Odd subgroup.index) (sylow : Sylow 2 subgroup) :
    (ambientSylow subgroup hodd sylow : Subgroup G) = (sylow : Subgroup subgroup).map subgroup.subtype := rfl

theorem nested {G : Type*} [Group G] [Finite G] (smaller larger : Subgroup G)
    (hcontained : smaller ≤ larger) (hodd : Odd (smaller.subgroupOf larger).index)
    (sylow : Sylow 2 smaller) :
    ∃ ambient : Sylow 2 larger,
      (ambient : Subgroup larger).map larger.subtype = (sylow : Subgroup smaller).map smaller.subtype := by
  let equivalence : smaller ≃* smaller.subgroupOf larger := (Subgroup.subgroupOfEquivOfLe hcontained).symm
  let localSylow := sylow.mapSurjective (f := equivalence.toMonoidHom)
    (show Function.Surjective equivalence.toMonoidHom from equivalence.surjective)
  let ambient := ambientSylow (smaller.subgroupOf larger) hodd localSylow
  refine ⟨ambient, ?_⟩
  rw [coe_ambientSylow, Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  congr 1

end CFSG.ComponentClassification.OddIndexSylow
