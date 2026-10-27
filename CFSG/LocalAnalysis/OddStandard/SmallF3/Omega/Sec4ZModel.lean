module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem sec4Z_factorization_27648 : Nat.factorization 27648 2 = 10 := by
  have h : (27648 : ℕ) = 2 ^ 10 * 27 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 27)]

theorem sec4Z_exists_central_four_plus (Q : Sylow 2 (ProjOrth Sec4IQ)) :
    ∃ z : ProjOrth Sec4IQ, HasType z 4 1 ∧ z ∈ (Q : Subgroup (ProjOrth Sec4IQ)) ∧
      ∀ q ∈ (Q : Subgroup (ProjOrth Sec4IQ)), q * z = z * q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀⟩ := exists_hasType_seven sec4IQ_nondegenerate sec4IQ_finrank
    (Or.inr (Or.inl rfl)) (1 : ℤˣ)
  have hxx : x₀ * x₀ = 1 := by
    obtain ⟨-, t, htt, -, rfl⟩ := hx₀
    rw [← map_mul, htt, map_one]
  have hord : orderOf x₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx₀.1
  have hCcard : Nat.card (centralizer ({x₀} : Set (ProjOrth Sec4IQ))) = 27648 :=
    natCard_centralizer_hasType_four_plus_seven sec4IQ_nondegenerate sec4IQ_finrank hx₀
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(centralizer ({x₀} : Set (ProjOrth Sec4IQ)))) :=
    inferInstance
  have hR' : IsSylow2Of ((R : Subgroup ↥(centralizer ({x₀} : Set (ProjOrth Sec4IQ)))).map
      (centralizer ({x₀} : Set (ProjOrth Sec4IQ))).subtype) (centralizer ({x₀} : Set _)) :=
    isSylow2Of_map_sylow R
  set R' : Subgroup (ProjOrth Sec4IQ) := (R : Subgroup ↥(centralizer ({x₀} :
    Set (ProjOrth Sec4IQ)))).map (centralizer ({x₀} : Set (ProjOrth Sec4IQ))).subtype with hR'def
  have hx₀R : x₀ ∈ R' := sec4_t_mem_S hR' hord
  have hRcomm : ∀ r ∈ R', r * x₀ = x₀ * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hR'.1 hr)
  have hR'card : Nat.card R' = 2 ^ 10 := by
    have h1 : Nat.card R' = Nat.card R :=
      (Nat.card_congr (Subgroup.equivMapOfInjective _ _
        (centralizer ({x₀} : Set (ProjOrth Sec4IQ))).subtype_injective).toEquiv).symm
    rw [h1, Sylow.card_eq_multiplicity, hCcard, sec4Z_factorization_27648]
  have hindex : ¬ 2 ∣ R'.index := by
    have h := Subgroup.card_mul_index R'
    rw [hR'card, natCard_projOrth_seven sec4IQ_nondegenerate sec4IQ_finrank] at h
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjOrth Sec4IQ) (hR'.2.1.toSylow hindex) Q
  have hQmem : ∀ q, q ∈ (Q : Subgroup (ProjOrth Sec4IQ)) ↔ ∃ r ∈ R', g * r * g⁻¹ = q := by
    intro q
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists,
      IsPGroup.toSylow_coe]
    rfl
  have hzzs : (g * x₀ * g⁻¹) * (g * x₀ * g⁻¹) = 1 := by
    calc (g * x₀ * g⁻¹) * (g * x₀ * g⁻¹) = g * (x₀ * x₀) * g⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hz1 : g * x₀ * g⁻¹ ≠ 1 := by
    intro h
    exact hx₀.1 (by simpa using h)
  refine ⟨g * x₀ * g⁻¹, ?_, (hQmem _).mpr ⟨x₀, hx₀R, rfl⟩, ?_⟩
  · refine hasType_of_natCard_eq_seven sec4IQ_nondegenerate sec4IQ_nondegenerate
      sec4IQ_finrank sec4IQ_finrank sec4IQ_quadSign sec4IQ_quadSign hxx hx₀.1 hzzs hz1 ?_
      (Or.inr (Or.inl rfl)) hx₀
    exact (natCard_centralizer_singleton_mulEquiv (MulAut.conj g) x₀).symm
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := (hQmem q).mp hq
    have h := hRcomm r hr
    calc g * r * g⁻¹ * (g * x₀ * g⁻¹) = g * (r * x₀) * g⁻¹ := by group
      _ = g * (x₀ * r) * g⁻¹ := by rw [h]
      _ = g * x₀ * g⁻¹ * (g * r * g⁻¹) := by group

end CFSG.OddStandard.SmallF3.Omega
