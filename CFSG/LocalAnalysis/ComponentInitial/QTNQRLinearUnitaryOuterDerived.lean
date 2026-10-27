module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary
public import CFSG.LocalAnalysis.ComponentInitial.PerfectCentralQuotientOuter
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OuterDerived

open Matrix LinearFlag CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem exists_comap_of_injective {G H : Type*} [Group G] [Group H] {ι : G →* H}
    (hι : Function.Injective ι) {N : Subgroup H} {d : ℕ} (hN : IsCyclic N) (hNd : Nat.card N ∣ d)
    (hcomm : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ N) :
    ∃ M : Subgroup G, IsCyclic M ∧ Nat.card M ∣ d ∧ ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ M := by
  refine ⟨N.comap ι, isCyclic_of_injective _ (ι.subgroupComap_injective N hι),
    (Subgroup.card_comap_dvd_of_injective N ι hι).trans hNd, fun a b => ?_⟩
  rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hcomm _ _

theorem derived_of_commutator_mem {G : Type*} [Group G] {N : Subgroup G} {d : ℕ}
    (hN : IsCyclic N) (hNd : Nat.card N ∣ d) (hcomm : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N) :
    IsCyclic (commutator G) ∧ Nat.card (commutator G) ∣ d ∧
      ∃ (_ : N.Normal), ∀ x y : G ⧸ N, x * y = y * x := by
  have hle : commutator G ≤ N := by
    change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ N
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  have hnormal : N.Normal := ⟨fun x hx g => by
    simpa only [inv_mul_cancel_right] using mul_mem (hcomm g x) hx⟩
  refine ⟨isCyclic_of_injective _ (Subgroup.inclusion_injective hle),
    (Subgroup.card_dvd_of_le hle).trans hNd, hnormal, fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  convert hcomm b⁻¹ a⁻¹ using 1
  group

theorem outer_comp_injective (J : Type*) [Group J] [Group.IsPerfect J] {T : Type*} [Group T]
    (e : J ⧸ Subgroup.center J ≃* T) :
    Function.Injective ((equivalence e).toMonoidHom.comp (outerCenterQuotientHom J)) :=
  (equivalence e).injective.comp (perfect_central_quotient_Schreier J).1

theorem linear_perfect_cover_outer_derived_diagonal_bound (J : Type) [Group J]
    [Group.IsPerfect J] (n p f : ℕ) (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL n p f) :
    IsCyclic (commutator (Outer J)) ∧ Nat.card (commutator (Outer J)) ∣ Nat.gcd n (p ^ f - 1) ∧
      (∃ (N : Subgroup (Outer J)) (_ : N.Normal), IsCyclic N ∧
        Nat.card N ∣ Nat.gcd n (p ^ f - 1) ∧ ∀ x y : Outer J ⧸ N, x * y = y * x) ∧
      (n = 2 → ∀ a b : Outer J, a * b = b * a) := by
  obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have h2 : n = 2 → ∀ a b : Outer J, a * b = b * a := by
    rintro rfl a b
    refine outer_comp_injective J
      (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm) ?_
    rw [map_mul, map_mul, outer_psl2_mul_comm]
  obtain ⟨M, hMcyc, hMcard, hMcomm⟩ : ∃ M : Subgroup (Outer J), IsCyclic M ∧
      Nat.card M ∣ Nat.gcd n (p ^ f - 1) ∧ ∀ a b : Outer J, a * b * a⁻¹ * b⁻¹ ∈ M := by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · refine ⟨⊥, isCyclic_of_subsingleton, by rw [Subgroup.card_bot]; exact one_dvd _,
        fun a b => ?_⟩
      rw [h2 rfl a b, Subgroup.mem_bot]
      group
    · obtain ⟨N, hcyc, hcard, hcomm⟩ := exists_linear_outer_diagonal (K := K) h3
      rw [hK] at hcard
      exact exists_comap_of_injective (outer_comp_injective J (e.trans
        ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)))) hcyc hcard hcomm
  obtain ⟨h1, hd, hMn, hMq⟩ := derived_of_commutator_mem hMcyc hMcard hMcomm
  exact ⟨h1, hd, ⟨M, hMn, hMcyc, hMcard, hMq⟩, h2⟩

theorem unitary_perfect_cover_outer_derived_diagonal_bound (J : Type) [Group J]
    [Group.IsPerfect J] (n p f : ℕ) (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSU n p f) :
    IsCyclic (commutator (Outer J)) ∧ Nat.card (commutator (Outer J)) ∣ Nat.gcd n (p ^ f + 1) ∧
      ∃ (N : Subgroup (Outer J)) (_ : N.Normal), IsCyclic N ∧
        Nat.card N ∣ Nat.gcd n (p ^ f + 1) ∧ ∀ x y : Outer J ⧸ N, x * y = y * x := by
  obtain ⟨⟨hp, hf, hn, h32⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h3, h2⟩ => h32 (by rw [h3, h2])
  obtain ⟨⟨eT⟩, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order hU hn hq
  obtain ⟨N, hcyc, hcard, hcomm⟩ := exists_unitary_outer_diagonal hU hn hq
  obtain ⟨M, hMcyc, hMcard, hMcomm⟩ := exists_comap_of_injective
    (outer_comp_injective J ((e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm))
    hcyc hcard hcomm
  obtain ⟨h1, hd, hMn, hMq⟩ := derived_of_commutator_mem hMcyc hMcard hMcomm
  exact ⟨h1, hd, M, hMn, hMcyc, hMcard, hMq⟩

theorem linear_unitary_perfect_cover_outer_derived_diagonal_bound (J : Type) [Group J]
    [Group.IsPerfect J] (t : StatedLieTag) (n p f : ℕ) (ε : ℤ)
    (hε : t = .PSL ∧ ε = 1 ∨ t = .PSU ∧ ε = -1)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) t n p f) :
    IsCyclic (commutator (Outer J)) ∧
      Nat.card (commutator (Outer J)) ∣ Int.gcd n ((p : ℤ) ^ f - ε) ∧
      (∃ (N : Subgroup (Outer J)) (_ : N.Normal), IsCyclic N ∧
        Nat.card N ∣ Int.gcd n ((p : ℤ) ^ f - ε) ∧ ∀ x y : Outer J ⧸ N, x * y = y * x) ∧
      (t = .PSL → n = 2 → ∀ a b : Outer J, a * b = b * a) := by
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hd : Int.gcd n ((p : ℤ) ^ f - 1) = Nat.gcd n (p ^ f - 1) := by
      rw [← Int.gcd_natCast_natCast, Nat.cast_sub (Nat.one_le_pow _ _ h.1.1.pos), Nat.cast_pow,
        Nat.cast_one]
    rw [hd]
    obtain ⟨h1, h2, h3, h4⟩ := linear_perfect_cover_outer_derived_diagonal_bound J n p f h
    exact ⟨h1, h2, h3, fun _ => h4⟩
  · have hd : Int.gcd n ((p : ℤ) ^ f - -1) = Nat.gcd n (p ^ f + 1) := by
      rw [← Int.gcd_natCast_natCast, sub_neg_eq_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    rw [hd]
    obtain ⟨h1, h2, h3⟩ := unitary_perfect_cover_outer_derived_diagonal_bound J n p f h
    exact ⟨h1, h2, h3, fun ht => by cases ht⟩

end CFSG.LocalAnalysis.ComponentInitial.OuterDerived
