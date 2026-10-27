module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.GH74.Generic

open CFSG Subgroup

theorem isCyclic_of_card_le_two {A : Type*} [Group A] [Finite A] (h : Nat.card A ≤ 2) :
    IsCyclic A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hc : Nat.card A = 1 ∨ Nat.card A = 2 := by omega
  rcases hc with hc | hc
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 hc).1
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card (p := 2) hc

theorem card_le_two_of_isPGroup {A : Type*} [Group A] [Finite A] (hA : IsPGroup 2 A)
    (h : Nat.card A < 4) : Nat.card A ≤ 2 := by
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rcases k with _ | _ | k
  · rw [hk]; norm_num
  · rw [hk]; norm_num
  · exfalso
    have : 2 ^ 2 ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_two_subgroup_card_ge_four {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    ∃ P : Subgroup Q, IsPGroup 2 P ∧ 4 ≤ Nat.card P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hS : Nat.card S ≤ 2 := card_le_two_of_isPGroup S.isPGroup' (hcon (S : Subgroup Q) S.isPGroup')
  have hScyc : IsCyclic ↥(S : Subgroup Q) := isCyclic_of_card_le_two hS
  obtain ⟨-, -, -, ⟨hnormal, hodd, hindex, -⟩, -⟩ := cyclic_sylow_normal_odd_complement S hScyc
  set N := pPrimeCore 2 Q with hN
  have hcycq : IsCyclic (Q ⧸ N) := by
    have : Nat.card (Q ⧸ N) ≤ 2 := by
      rw [← Subgroup.index_eq_card, hindex]; exact hS
    exact isCyclic_of_card_le_two this
  have hNtop : N = ⊤ := by
    have hperf : commutator Q = ⊤ := hQ.1.commutator_eq_top
    rw [eq_top_iff, ← hperf, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (IsCyclic.commGroup.mul_comm _ _)
  have hQodd : Odd (Nat.card Q) := by
    have : Nat.card N = Nat.card Q := by rw [hNtop]; exact Subgroup.card_top
    rw [← this]; exact hodd
  have hsolv : Group.IsSolvable Q := CFSG.Milestones.odd_order_solvable hQodd
  have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q hsolv

section B2

variable {X : Type*} [Group X]

theorem card_zpowers_le_two {z : X} (hz : z * z = 1) : Nat.card (zpowers z) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz))

theorem components_eq_of_two_subgroup_le [Finite X] {K : Subgroup X} (hK : IsComponent K) {z : X}
    (hz : z * z = 1)
    (hT : ∀ T : Subgroup X, IsPGroup 2 T → T ≤ centralizer (K : Set X) → T ≤ zpowers z)
    {K' : Subgroup X} (hK' : IsComponent K') : K' = K := by
  by_contra hne
  rcases LocalCores.distinct_components_commute hK hK' with h | h
  · exact hne h.symm
  · have hle : K' ≤ centralizer (K : Set X) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h
    obtain ⟨P, hP2, hP4⟩ := exists_two_subgroup_card_ge_four hK'.1
    have hmap : IsPGroup 2 (P.map K'.subtype) := hP2.map K'.subtype
    have hPle : P.map K'.subtype ≤ centralizer (K : Set X) := by
      rintro _ ⟨p, -, rfl⟩
      exact hle p.2
    have hcard : Nat.card (P.map K'.subtype) = Nat.card P :=
      Subgroup.card_map_of_injective K'.subtype_injective
    have hle2 := Subgroup.card_le_of_le (hT _ hmap hPle)
    have := card_zpowers_le_two hz
    omega

theorem layer_eq_of_two_subgroup_le [Finite X] {K : Subgroup X} (hK : IsComponent K) {z : X}
    (hz : z * z = 1)
    (hT : ∀ T : Subgroup X, IsPGroup 2 T → T ≤ centralizer (K : Set X) → T ≤ zpowers z) :
    layer X = K := by
  have hset : {K' : Subgroup X | IsComponent K'} = {K} := by
    ext K'
    exact ⟨fun h => components_eq_of_two_subgroup_le hK hz hT h, fun h => h ▸ hK⟩
  simp only [CFSG.layer.eq_sSup]
  rw [hset, sSup_singleton]

theorem centralizer_eq_zpowers [Finite X] {K : Subgroup X} (hK : IsComponent K) {z : X}
    (hzc : z ∈ center X) (hz : z * z = 1) (hz1 : z ≠ 1) (hX : pPrimeCore 2 X = ⊥)
    (hT : ∀ T : Subgroup X, IsPGroup 2 T → T ≤ centralizer (K : Set X) → T ≤ zpowers z) :
    centralizer (K : Set X) = zpowers z := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlayer := layer_eq_of_two_subgroup_le hK hz hT
  have hKn : K.Normal := by
    have hch : (layer X).Characteristic := LocalCores.layer_characteristic (G := X)
    have hn : (layer X).Normal := inferInstance
    rwa [hlayer] at hn
  set C : Subgroup X := centralizer (K : Set X) with hC
  have hzC : z ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro k _
    exact (Subgroup.mem_center_iff.1 hzc k)
  have hzle : zpowers z ≤ C := (Subgroup.zpowers_le).2 hzC
  let z' : ↥C := ⟨z, hzC⟩
  have hz'2 : z' * z' = 1 := Subtype.ext hz
  have hz'ord : IsPGroup 2 (zpowers z') := by
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨1, Subtype.ext ?_⟩
    change (z' ^ n) ^ (2 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show z' ^ 2 = 1 by rw [sq]; exact hz'2, one_zpow]
  obtain ⟨S, hzS⟩ := hz'ord.exists_le_sylow
  have hcardS : Nat.card S = 2 := by
    have h1 : Nat.card (zpowers z') ≤ Nat.card S := Subgroup.card_le_of_le hzS
    have h2 : Nat.card (zpowers z') = 2 := by
      rw [Nat.card_zpowers]
      refine orderOf_eq_prime (by rw [sq]; exact hz'2) ?_
      intro h
      exact hz1 (by simpa [z'] using congrArg Subtype.val h)
    have h3 : Nat.card S ≤ 2 := by
      have hmap : IsPGroup 2 ((S : Subgroup ↥C).map C.subtype) := S.isPGroup'.map C.subtype
      have hle : (S : Subgroup ↥C).map C.subtype ≤ centralizer (K : Set X) := by
        rintro _ ⟨c, -, rfl⟩
        exact c.2
      have := Subgroup.card_le_of_le (hT _ hmap hle)
      rw [Subgroup.card_map_of_injective C.subtype_injective] at this
      exact this.trans (card_zpowers_le_two hz)
    omega
  have hScyc : IsCyclic ↥(S : Subgroup ↥C) := isCyclic_of_card_le_two (by omega)
  obtain ⟨hcard, -, -, -, -⟩ := cyclic_sylow_normal_odd_complement S hScyc
  have hOC : pPrimeCore 2 ↥C = ⊥ := by
    have hCn : C.Normal := by rw [hC]; infer_instance
    have hnorm : ((pPrimeCore 2 ↥C).map C.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥C).map C.subtype)) := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card
    have hle : (pPrimeCore 2 ↥C).map C.subtype ≤ pPrimeCore 2 X := le_sSup ⟨hnorm, hcop⟩
    rw [hX, le_bot_iff] at hle
    exact Subgroup.map_injective C.subtype_injective (by rw [Subgroup.map_bot]; exact hle)
  rw [hOC, Subgroup.card_bot, hcardS] at hcard
  have hCcard : Nat.card ↥C = 2 := by
    have h2 : 2 ∣ Nat.card ↥C := by
      have := Subgroup.card_subgroup_dvd_card (S : Subgroup ↥C)
      rwa [show Nat.card (S : Subgroup ↥C) = 2 from hcardS] at this
    have hpos : 0 < Nat.card ↥C := Nat.card_pos
    obtain ⟨m, hm⟩ := h2
    rw [hm] at hcard ⊢
    have : m = 1 := by simpa using hcard.symm
    omega
  symm
  apply Subgroup.eq_of_le_of_card_ge hzle
  rw [hCcard]
  have : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hz) hz1
  omega

theorem fitting_eq_of_centralizer [Finite X] {K : Subgroup X} (hK : IsComponent K) {z : X}
    (hzc : z ∈ center X) (hz : z * z = 1) (hz1 : z ≠ 1) (hzK : z ∈ K) (hX : pPrimeCore 2 X = ⊥)
    (hT : ∀ T : Subgroup X, IsPGroup 2 T → T ≤ centralizer (K : Set X) → T ≤ zpowers z) :
    pCore 2 X = zpowers z ∧ fittingSubgroup X = zpowers z ∧ generalizedFitting X = K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := centralizer_eq_zpowers hK hzc hz hz1 hX hT
  have hzn : (zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hgz : Commute g z := Subgroup.mem_center_iff.1 hzc g
    have hcomm : Commute g (z ^ k) := hgz.zpow_right k
    have : g * z ^ k * g⁻¹ = z ^ k := by rw [hcomm.eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hz2 : IsPGroup 2 (zpowers z) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨1, Subtype.ext ?_⟩
    change (z ^ n) ^ (2 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show z ^ 2 = 1 by rw [sq]; exact hz, one_zpow]
  have hge : zpowers z ≤ pCore 2 X := le_sSup ⟨hzn, hz2⟩
  have hle : pCore 2 X ≤ zpowers z := by
    have hnil : Group.IsNilpotent (pCore 2 X) := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
    have hsolv : Group.IsSolvable (pCore 2 X) := inferInstance
    have hsub : (pCore 2 X).IsSubnormal := (pCore_normal (p := 2) (G := X)).isSubnormal
    have hcomm := (LocalCores.component_solvable_centralizer hsolv hsub).1 K hK
    rw [← hC]
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hp2 : pCore 2 X = zpowers z := le_antisymm hle hge
  have hF : fittingSubgroup X = zpowers z := by rw [Fitting_eq_pcore X 2 hX, hp2]
  refine ⟨hp2, hF, ?_⟩
  simp only [CFSG.generalizedFitting.eq_sup]
  rw [hF, layer_eq_of_two_subgroup_le hK hz hT]
  exact sup_eq_right.2 ((Subgroup.zpowers_le).2 hzK)

end B2

end CFSG.GH74.Generic
