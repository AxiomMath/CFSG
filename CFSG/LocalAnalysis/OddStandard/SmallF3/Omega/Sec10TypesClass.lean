module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkI4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypesCert

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace Ty

theorem centCount_conj {c : P45}
    (hc : c ∈ QA45.originalSubgroup) (a : P45) : centCount (c * a * c⁻¹) = centCount a := by
  rw [centCount, centCount, ← card_inf_centralizer QA45 QA45_ok,
    ← card_inf_centralizer QA45 QA45_ok]
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c⁻¹).toEquiv fun x => ?_)
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨hx, hcm⟩
    refine ⟨QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.mul_mem
      (QA45.originalSubgroup.inv_mem hc) hx) hc, ?_⟩
    calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * x) * c := by rw [hcm]
      _ = a * (c⁻¹ * x * c) := by group
  · rintro ⟨hx, hcm⟩
    have hx' : x ∈ QA45.originalSubgroup := by
      have h := QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.mul_mem hc hx)
        (QA45.originalSubgroup.inv_mem hc)
      rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at h
    refine ⟨hx', ?_⟩
    calc x * (c * a * c⁻¹) = c * (c⁻¹ * x * c * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * x * c)) * c⁻¹ := by rw [hcm]
      _ = (c * a * c⁻¹) * x := by group

theorem exists_conj_tA {a : P45}
    (ha : IsI4PlusIn QP45.originalSubgroup a) :
    a ∈ QP45.originalSubgroup ∧ ∃ c ∈ QP45.originalSubgroup, c * a * c⁻¹ = Pk.tA := by
  obtain ⟨h2, K, hK⟩ := ha
  have haP : a ∈ QP45.originalSubgroup := (Subgroup.mem_inf.1 (hK.2.1 hK.1)).1
  obtain ⟨c, hc, hcov⟩ := Pk.exists_cover_pk haP h2
  refine ⟨haP, ?_⟩
  rcases hcov with h | h
  · exact ⟨c, hc, h⟩
  · exfalso
    have h' : c⁻¹ * Pk.tB * c⁻¹⁻¹ = a := by
      rw [inv_inv, ← h]
      group
    exact not_isI4PlusIn_of_conj_tB (QP45.originalSubgroup.inv_mem hc) h' ⟨h2, K, hK⟩

theorem invCent_of_isI4PlusIn
    {a : P45} (ha : IsI4PlusIn QP45.originalSubgroup a) :
    InvCent 1152 a := by
  obtain ⟨haP, c, hc, hca⟩ := exists_conj_tA ha
  have hA : InvCent 1152 Pk.tA := rowA
  have hcA : c⁻¹ ∈ QA45.originalSubgroup := QA45.originalSubgroup.inv_mem (QP45_le_QA45 hc)
  have hsq : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha.1, pow_two] at this
  have ha1 : a ≠ 1 := fun h => by
    have := ha.1
    rw [h, orderOf_one] at this
    omega
  refine ⟨QP45_le_QA45 haP, hsq, ha1, ?_⟩
  have h1 := centCount_conj hcA Pk.tA
  rw [show c⁻¹ * Pk.tA * c⁻¹⁻¹ = a by rw [inv_inv, ← hca]; group] at h1
  rw [h1]
  exact hA.2.2.2

theorem isI4PlusIn_of_invCent
    {y : P45} (hyP : y ∈ QP45.originalSubgroup)
    (hy : InvCent 1152 y) : IsI4PlusIn QP45.originalSubgroup y := by
  have hB : InvCent 192 Pk.tB := rowB
  have h2 : orderOf y = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hy.2.1) hy.2.2.1
  obtain ⟨c, hc, hcov⟩ := Pk.exists_cover_pk hyP h2
  have hcA : c⁻¹ ∈ QA45.originalSubgroup := QA45.originalSubgroup.inv_mem (QP45_le_QA45 hc)
  rcases hcov with h | h
  · refine isI4PlusIn_of_conj_tA (QP45.originalSubgroup.inv_mem hc) ?_
    show c⁻¹ * Pk.tA * c⁻¹⁻¹ = y
    rw [inv_inv, ← h]
    group
  · exfalso
    have h1 := centCount_conj hcA Pk.tB
    rw [show c⁻¹ * Pk.tB * c⁻¹⁻¹ = y by rw [inv_inv, ← h]; group, hB.2.2.2] at h1
    have h3 := hy.2.2.2
    omega

end Ty

end CFSG.OddStandard.SmallF3.Omega
