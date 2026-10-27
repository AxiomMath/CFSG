module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoreTransport

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem normal_pSubgroup_eq_bot_of_selfCentralizing_core {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hcentralizer : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (subgroup : Subgroup G) (hnormal : subgroup.Normal) (hpgroup : IsPGroup prime subgroup) :
    subgroup = ⊥ := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisjoint : Disjoint subgroup (pCore 2 G) :=
    IsPGroup.disjoint_of_ne prime 2 hodd subgroup (pCore 2 G) hpgroup (pCore_isPGroup G 2)
  have hle : subgroup ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
    intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    exact (Subgroup.commute_of_normal_of_disjoint subgroup (pCore 2 G) hnormal
      (pCore_normal G 2) hdisjoint element other helement hother).eq.symm
  apply le_antisymm _ bot_le
  intro element helement
  apply Subgroup.mem_bot.mpr
  exact Subgroup.disjoint_def.mp hdisjoint helement (hcentralizer (hle helement))

theorem pCore_eq_bot_of_selfCentralizing_twoCore {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hcentralizer : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    pCore prime G = ⊥ := by
  exact normal_pSubgroup_eq_bot_of_selfCentralizing_core prime hprime hodd hcentralizer
    (pCore prime G) (pCore_normal G prime) (pCore_isPGroup G prime)

theorem charTwoType_local_odd_core_eq_bot {G : Type u} [Group G]
    (hchar : IsCharTwoType G) (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) : pCore prime subgroup = ⊥ := by
  exact pCore_eq_bot_of_selfCentralizing_twoCore prime hprime hodd
    (charTwoType_local_centralizer hchar subgroup hlocal)

theorem charTwoType_local_odd_coreOf_eq_bot {G : Type u} [Group G]
    (hchar : IsCharTwoType G) (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) : pCoreOf prime subgroup = ⊥ := by
  simp only [pCoreOf, charTwoType_local_odd_core_eq_bot hchar subgroup hlocal prime hprime hodd,
    Subgroup.map_bot]

theorem charTwoType_normal_local_odd_subgroup_eq_bot {G : Type u} [Group G]
    (hchar : IsCharTwoType G) (localSubgroup : Subgroup G) (hlocal : IsTwoLocal localSubgroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (subgroup : Subgroup G) (hle : subgroup ≤ localSubgroup)
    (hnormal : (subgroup.subgroupOf localSubgroup).Normal) (hpgroup : IsPGroup prime subgroup) :
    subgroup = ⊥ := by
  have hcore := normal_pSubgroup_le_pCoreOf prime subgroup localSubgroup hle hnormal hpgroup
  rw [charTwoType_local_odd_coreOf_eq_bot hchar localSubgroup hlocal prime hprime hodd] at hcore
  exact le_antisymm hcore bot_le

theorem pCore_map_le {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (prime : ℕ) (equivalence : G ≃* otherGroup) :
    (pCore prime G).map equivalence.toMonoidHom ≤ pCore prime otherGroup := by
  apply le_pCore_of_normal prime
  · exact (pCore_normal G prime).map equivalence.toMonoidHom equivalence.surjective
  · exact (pCore_isPGroup G prime).of_equiv (equivalence.subgroupMap (pCore prime G))

theorem pCore_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (prime : ℕ) (equivalence : G ≃* otherGroup) :
    (pCore prime G).map equivalence.toMonoidHom = pCore prime otherGroup := by
  apply le_antisymm (pCore_map_le prime equivalence)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equivalence.symm.toMonoidHom) equivalence.symm.injective).mp
  rw [subgroup_map_equiv_symm]
  exact pCore_map_le prime equivalence.symm

theorem pCore_characteristic (G : Type u) [Group G] (prime : ℕ) :
    (pCore prime G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro equivalence
  exact pCore_map_equiv prime equivalence

theorem odd_subgroup_disjoint_twoCore {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) (hodd : ¬2 ∣ Nat.card subgroup) :
    Disjoint subgroup (pCore 2 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp (pCore_isPGroup G 2)
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hcard]
  exact Nat.prime_two.coprime_pow_of_not_dvd hodd

theorem odd_subgroup_centralizer_twoCore_eq_bot {G : Type u} [Group G] [Finite G]
    (hcentralizer : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (subgroup : Subgroup G) (hodd : ¬2 ∣ Nat.card subgroup) :
    subgroup ⊓ Subgroup.centralizer (pCore 2 G : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro element hmem
  apply Subgroup.mem_bot.mpr
  exact Subgroup.disjoint_def.mp (odd_subgroup_disjoint_twoCore subgroup hodd)
    hmem.1 (hcentralizer hmem.2)

theorem conjugation_twoCore_injective_on_odd_subgroup {G : Type u} [Group G] [Finite G]
    (hcentralizer : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (subgroup : Subgroup G) (hodd : ¬2 ∣ Nat.card subgroup)
    (hnormal : (pCore 2 G).Normal) :
    Function.Injective ((@MulAut.conjNormal G _ (pCore 2 G) hnormal).comp subgroup.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro element hmem
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have haction := MonoidHom.mem_ker.mp hmem
  have hcentral : (element : G) ∈ Subgroup.centralizer (pCore 2 G : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    have hfixed := congrArg (fun automorphism : MulAut (pCore 2 G) =>
      ((automorphism (⟨other, hother⟩ : pCore 2 G)) : G)) haction
    change (element : G) * other * (element : G)⁻¹ = other at hfixed
    have hcommute := congrArg (fun value : G => value * (element : G)) hfixed
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcommute.symm
  exact Subgroup.disjoint_def.mp (odd_subgroup_disjoint_twoCore subgroup hodd)
    element.property (hcentralizer hcentral)

theorem charTwoType_local_odd_subgroup_centralizer_eq_bot {G : Type u} [Group G] [Finite G]
    (hchar : IsCharTwoType G) (localSubgroup : Subgroup G) (hlocal : IsTwoLocal localSubgroup)
    (subgroup : Subgroup localSubgroup) (hodd : ¬2 ∣ Nat.card subgroup) :
    subgroup ⊓ Subgroup.centralizer (pCore 2 localSubgroup : Set localSubgroup) = ⊥ := by
  exact odd_subgroup_centralizer_twoCore_eq_bot
    (charTwoType_local_centralizer hchar localSubgroup hlocal) subgroup hodd

end CFSG.RankThreeEvenClassification.Helpers
