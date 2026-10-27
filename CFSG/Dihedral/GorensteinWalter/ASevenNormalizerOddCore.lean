module

public import CFSG.Dihedral.GorensteinWalter.ASevenNormalizerCosetData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerThreeCycle
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Assembly.Defs

public section

namespace CFSG.GorensteinWalter

theorem a7ThreeNormalizer_commutator_t_sq :
    ∀ x : ASevenCosetGroup,
      (x * a7a * x⁻¹ = a7a ∨ x * a7a * x⁻¹ = a7a ^ 2) →
      (a7t * x * a7t⁻¹ * x⁻¹) ^ 2 = 1 := by
  decide +kernel

theorem a7ThreeNormalizer_normal_odd_le_U (W : Subgroup ASevenCosetGroup)
    (hWN : W ≤ a7ThreeNormalizer) (hnormal : (W.subgroupOf a7ThreeNormalizer).Normal)
    (hodd : Odd (Nat.card W)) : W ≤ a7U := by
  have hnormalized : a7ThreeNormalizer ≤ Subgroup.normalizer (W : Set ASevenCosetGroup) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mp hnormal
  have htN : a7t ∈ a7ThreeNormalizer := by
    rw [a7ThreeNormalizer, a7U_normalizer_mem_iff]
    decide
  have hWcent : W ≤ Subgroup.centralizer ({a7t} : Set ASevenCosetGroup) := by
    intro x hx
    let z := a7t * x * a7t⁻¹ * x⁻¹
    have hzW : z ∈ W := W.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hnormalized htN) x).mp hx) (W.inv_mem hx)
    have hzsq : z ^ 2 = 1 := a7ThreeNormalizer_commutator_t_sq x
      ((a7U_normalizer_mem_iff x).mp (hWN hx))
    have hzodd : Odd (orderOf z) := hodd.of_dvd_nat (W.orderOf_dvd_natCard hzW)
    have hzone : z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hzsq) with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hzodd
        norm_num at hzodd
    rw [Subgroup.mem_centralizer_singleton_iff]
    change a7t * x * a7t⁻¹ * x⁻¹ = 1 at hzone
    have h := congrArg (fun y => y * x * a7t) hzone
    simpa only [mul_assoc, inv_mul_cancel_left, one_mul, inv_mul_cancel, mul_one] using h.symm
  rw [a7U_eq_zpowers]
  exact aSeven_odd_subgroup_centralizing_a7t_le_zpowers
    (fun x hx => hodd.of_dvd_nat (W.orderOf_dvd_natCard hx)) hWcent

theorem a7ThreeNormalizer_oddCore_map :
    (Assembly.oddCore a7ThreeNormalizer).map a7ThreeNormalizer.subtype = a7U := by
  let J := Assembly.oddCore a7ThreeNormalizer
  have hJN : J.map a7ThreeNormalizer.subtype ≤ a7ThreeNormalizer :=
    Subgroup.map_subtype_le _
  have hJnormal : ((J.map a7ThreeNormalizer.subtype).subgroupOf a7ThreeNormalizer).Normal := by
    change (Subgroup.comap a7ThreeNormalizer.subtype (J.map a7ThreeNormalizer.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective a7ThreeNormalizer.subtype_injective]
    infer_instance
  have hJodd : Odd (Nat.card (J.map a7ThreeNormalizer.subtype)) := by
    rw [Subgroup.card_map_of_injective a7ThreeNormalizer.subtype_injective]
    exact DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hUN : a7U ≤ a7ThreeNormalizer := Subgroup.le_normalizer
  have hUnormal : (a7U.subgroupOf a7ThreeNormalizer).Normal :=
    Subgroup.normal_in_normalizer
  have hUodd : Odd (Nat.card (a7U.subgroupOf a7ThreeNormalizer)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv,
      aSeven_structure_fact_1_8_ii_centralizer.1]
    decide
  have hUJ : a7U.subgroupOf a7ThreeNormalizer ≤ J := le_sSup ⟨hUnormal, hUodd⟩
  apply le_antisymm (a7ThreeNormalizer_normal_odd_le_U _ hJN hJnormal hJodd)
  have h := Subgroup.map_mono (f := a7ThreeNormalizer.subtype) hUJ
  rwa [Subgroup.map_subgroupOf_eq_of_le hUN] at h

end CFSG.GorensteinWalter
