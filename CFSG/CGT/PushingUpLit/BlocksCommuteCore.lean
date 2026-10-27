module

public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.Quasithin.Background.A4
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem open_isSubnormal_top {X : Subgroup G} (h : X.IsSubnormal) :
    CFSG.Open.IsSubnormal X ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib h

theorem oTwoIn_eq_inf_pCore {X : Subgroup G} (hX : X.IsSubnormal) :
    oTwoIn X = X ⊓ pCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val = 2} hX
  rw [oTwoIn_eq_map, pCore_eq_piCore ↥X 2, pCore_eq_piCore G 2]
  exact h

theorem eq_oTwoUpper_of_short {X : Subgroup G} (hX : IsShortGroup ↥X) :
    X = CFSG.Quasithin.oTwoUpper X := by
  refine le_antisymm ?_ (CFSG.Quasithin.oTwoUpper_le X)
  exact noTwoQuot_of_short hX (CFSG.Quasithin.oTwoUpper X)
    (fun g hg n hn => CFSG.Quasithin.conj_mem_oTwoUpper (Subgroup.le_normalizer hg) hn)
    (fun g hg => CFSG.Quasithin.exists_pow_mem_oTwoUpper X hg)

omit [Finite G] in
theorem normal_set_mul_comm (N X : Subgroup G) (hN : N.Normal) :
    (N : Set G) * (X : Set G) = (X : Set G) * (N : Set G) := by
  ext g
  constructor
  · rintro ⟨n, hn, x, hx, rfl⟩
    refine ⟨x, hx, x⁻¹ * n * x, ?_, by group⟩
    simpa using hN.conj_mem n hn x⁻¹
  · rintro ⟨x, hx, n, hn, rfl⟩
    exact ⟨x * n * x⁻¹, hN.conj_mem n hn x, x, hx, by group⟩

theorem le_normalizer_of_isPGroup_normal {X N : Subgroup G} (hX : IsBlockOf X) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨-, hnorm⟩ := CFSG.Quasithin.a4_2_2 (eq_oTwoUpper_of_short hX.2)
    (open_isSubnormal_top hX.1) (R := N) le_top hN2 (normal_set_mul_comm N X hN)
  have hle : X ⊔ N ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).1 hnorm
  exact le_sup_right.trans hle

theorem commutator_normal_le {X N : Subgroup G} (hX : IsBlockOf X) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : ⁅N, X⁆ ≤ X ⊓ N :=
  le_inf (Subgroup.le_normalizer_iff_commutator_le_right.1
    (le_normalizer_of_isPGroup_normal hX hN hN2)) (Subgroup.commutator_le_left N X)

theorem commutator_pCore_le {X : Subgroup G} (hX : IsBlockOf X) :
    ⁅pCore 2 G, X⁆ ≤ oTwoIn X := by
  have := commutator_normal_le hX (pCore_normal (p := 2)) pCore_isPGroup
  rwa [← oTwoIn_eq_inf_pCore hX.1] at this

theorem commutator_mem_oTwoIn {X : Subgroup G} (hX : IsBlockOf X) {q x : G}
    (hq : q ∈ pCore 2 G) (hx : x ∈ X) : ⁅q, x⁆ ∈ oTwoIn X :=
  commutator_pCore_le hX (Subgroup.commutator_mem_commutator hq hx)

theorem oTwoIn_le_pCore {X : Subgroup G} (hX : X.IsSubnormal) : oTwoIn X ≤ pCore 2 G := by
  rw [oTwoIn_eq_inf_pCore hX]
  exact inf_le_right

theorem le_of_le_sup_pCore {X Y : Subgroup G} (hX : IsBlockOf X) (hY : IsBlockOf Y)
    (h : X ≤ Y ⊔ pCore 2 G) : X ≤ Y := by
  obtain ⟨hYeq, -⟩ := CFSG.Quasithin.a4_2_2 (eq_oTwoUpper_of_short hY.2)
    (open_isSubnormal_top hY.1) (R := pCore 2 G) le_top pCore_isPGroup
    (normal_set_mul_comm _ Y pCore_normal)
  calc X = CFSG.Quasithin.oTwoUpper X := eq_oTwoUpper_of_short hX.2
    _ ≤ CFSG.Quasithin.oTwoUpper (Y ⊔ pCore 2 G) := CFSG.Quasithin.oTwoUpper_mono h
    _ = Y := hYeq.symm

end CFSG.CGT.PushingUpLit
