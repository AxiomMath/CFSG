module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def ThreePointCentralization (H D : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ D → 3 ≤ Nat.card (pointFixedSet H X) →
    ∀ s : G, orderOf s = 2 → s ∈ Subgroup.normalizer (X : Set G) →
      X ≤ Subgroup.centralizer ({s} : Set G)

theorem pointFixedSet_zpowers_eq (H : Subgroup G) (x : G) :
    pointFixedSet H (Subgroup.zpowers x) = elementFixedSet H x := by
  ext a
  rw [mem_pointFixedSet_iff, Subgroup.zpowers_le]
  exact mem_point_right_stabilizer_iff H a x

theorem right_fixed_triple_card [Finite G] (H X : Subgroup G)
    (a b c : pointRightCosetSpace H) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : a ∈ pointFixedSet H X) (hb : b ∈ pointFixedSet H X)
    (hc : c ∈ pointFixedSet H X) : 3 ≤ Nat.card (pointFixedSet H X) := by
  have hsub : ({c, a, b} : Set (pointRightCosetSpace H)) ⊆ pointFixedSet H X := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact hc
    · exact ha
    · exact hb
  have hcard : ({c, a, b} : Set (pointRightCosetSpace H)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simpa using And.intro hca hcb), Set.ncard_pair hab]
  rw [← hcard]
  exact Set.ncard_le_ncard hsub

theorem inverter_normalizes_zpowers (x t : G) (ht : orderOf t = 2)
    (hinv : rightConjugateElem x t = x⁻¹) :
    t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  have htx : (MulAut.conj t) x = x⁻¹ := by
    simpa only [MulAut.conj_apply, rightConjugateElem,
      inv_eq_self_of_orderOf_eq_two ht] using hinv
  change Subgroup.zpowers ((MulAut.conj t) x) = Subgroup.zpowers x
  rw [htx, Subgroup.zpowers_inv]

theorem odd_inverted_element_not_commute (x t : G) (hx : x ≠ 1)
    (hodd : Odd (orderOf x)) (hinv : rightConjugateElem x t = x⁻¹) :
    ¬ Commute x t := by
  intro hcomm
  have hright : rightConjugateElem x t = x := by
    change t⁻¹ * x * t = x
    rw [mul_assoc, hcomm.eq, inv_mul_cancel_left]
  have hxeq : x = x⁻¹ := hright.symm.trans hinv
  have hxpow : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := congrArg (fun y : G => y * x) hxeq
      _ = 1 := inv_mul_cancel x
  have horder : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right dvd_rfl
      (orderOf_dvd_of_pow_eq_one hxpow)
  exact hx (orderOf_eq_one_iff.mp horder)

theorem pair_inverted_element_full_fixed_set [Finite G]
    (H : Subgroup G) (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (hthree : ThreePointCentralization H
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (t : G) (ht : orderOf t = 2) (x : G) (hx : x ≠ 1)
    (hxD : x ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (hodd : Odd (orderOf x)) (hinv : rightConjugateElem x t = x⁻¹) :
    elementFixedSet H x = {a, b} := by
  have hxcyclic : Subgroup.zpowers x ≤
      rightCosetStabilizer H a ⊓ rightCosetStabilizer H b :=
    Subgroup.zpowers_le.mpr hxD
  have ha : a ∈ pointFixedSet H (Subgroup.zpowers x) :=
    (mem_pointFixedSet_iff H _ a).mpr (hxcyclic.trans inf_le_left)
  have hb : b ∈ pointFixedSet H (Subgroup.zpowers x) :=
    (mem_pointFixedSet_iff H _ b).mpr (hxcyclic.trans inf_le_right)
  ext c
  constructor
  · intro hc
    by_contra hnot
    have hca : c ≠ a := by intro heq; exact hnot (by simp [heq])
    have hcb : c ≠ b := by intro heq; exact hnot (by simp [heq])
    have hcard := right_fixed_triple_card H (Subgroup.zpowers x) a b c hab hca hcb
      ha hb ((pointFixedSet_zpowers_eq H x).symm ▸ hc)
    have hcentral := hthree _ hxcyclic hcard t ht (inverter_normalizes_zpowers x t ht hinv)
    exact odd_inverted_element_not_commute x t hx hodd hinv
      (Subgroup.mem_centralizer_singleton_iff.mp (hcentral (Subgroup.mem_zpowers x)))
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact (pointFixedSet_zpowers_eq H x) ▸ ha
    · exact (pointFixedSet_zpowers_eq H x) ▸ hb

theorem commuting_pair_product_geometry (H : Subgroup G)
    (a b : pointRightCosetSpace H) (hab : a ≠ b) (u t : G)
    (hu : orderOf u = 2) (ht : orderOf t = 2) (hut : Commute u t)
    (huD : u ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (hflip : pointRightCosetMul H a t = b) :
    u ≠ t ∧ orderOf (u * t) = 2 ∧
      pointRightCosetMul H a (u * t) = b ∧
      pointRightCosetMul H b (u * t) = a ∧
      Disjoint (elementFixedSet H (u * t)) ({a, b} : Set (pointRightCosetSpace H)) := by
  have hne : u ≠ t := by
    intro heq
    have ha := (mem_point_right_stabilizer_iff H a u).mp huD.1
    rw [heq, hflip] at ha
    exact hab ha.symm
  have hutne : u * t ≠ 1 := by
    intro heq
    have he : u = t := by
      calc
        u = (u * t) * t := by
          rw [mul_assoc, ← pow_two, ← ht, pow_orderOf_eq_one, mul_one]
        _ = t := by rw [heq, one_mul]
    exact hne he
  have hv : orderOf (u * t) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hutne⟩
    have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    rw [hut.mul_pow, hu2, ht2, one_mul]
  have hav : pointRightCosetMul H a (u * t) = b := by
    rw [← pointRightCosetMul_mul, (mem_point_right_stabilizer_iff H a u).mp huD.1, hflip]
  have hbv := right_involution_flip_reverse H (u * t) hv a b hav
  refine ⟨hne, hv, hav, hbv, ?_⟩
  apply Set.disjoint_left.mpr
  intro c hc hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact hab (hc.symm.trans hav)
  · exact hab (hbv.symm.trans hc)

theorem odd_normalizer_fixes_pair [Finite G] (H X U : Subgroup G)
    (hUodd : Odd (Nat.card U)) (hUN : U ≤ Subgroup.normalizer (X : Set G))
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (hpair : pointFixedSet H X = {a, b}) :
    U ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b := by
  classical
  let Delta := pointFixedSet H X
  let := pointInvariantSetInverseRightAction H U Delta
    (fun u hu _ hd => normalizer_preserves_pointFixedSet (hUN hu) hd)
  let rho : U →* Equiv.Perm Delta := MulAction.toPermHom U Delta
  have hDcard : Nat.card Delta = 2 := by
    change Nat.card (pointFixedSet H X) = 2
    rw [hpair]
    exact Set.ncard_pair hab
  let : Fintype Delta := Fintype.ofFinite _
  have hPcard : Nat.card (Equiv.Perm Delta) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [← Nat.card_eq_fintype_card, hDcard]
    norm_num
  have hodd : Odd (Nat.card rho.range) := hUodd.of_dvd_nat (Subgroup.card_range_dvd rho)
  have hdiv : Nat.card rho.range ∣ 2 := hPcard ▸ rho.range.card_subgroup_dvd_card
  have hcard : Nat.card rho.range = 1 :=
    Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right dvd_rfl hdiv
  have hrange : rho.range = ⊥ := Subgroup.card_eq_one.mp hcard
  have hfix : ∀ u ∈ U, ∀ d ∈ Delta, pointRightCosetMul H d u = d := by
    intro u hu d hd
    have hperm : rho (⟨u, hu⟩ : U)⁻¹ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hrange]
      exact ⟨_, rfl⟩
    have he := congrArg (fun f : Equiv.Perm Delta => f (⟨d, hd⟩ : Delta)) hperm
    have heval := congrArg Subtype.val he
    change pointRightCosetMul H d ((u⁻¹)⁻¹) = d at heval
    simpa only [inv_inv] using heval
  intro u hu
  refine ⟨(mem_point_right_stabilizer_iff H a u).mpr ?_,
    (mem_point_right_stabilizer_iff H b u).mpr ?_⟩
  · apply hfix u hu a
    change a ∈ pointFixedSet H X
    rw [hpair]
    exact Set.mem_insert a {b}
  · apply hfix u hu b
    change b ∈ pointFixedSet H X
    rw [hpair]
    exact Set.mem_insert_of_mem a rfl

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
