module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Parts

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

private theorem exists_sq_eq_one_mk_eq {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hN : Odd (Nat.card N)) (u : G ⧸ N) (hu : u ^ 2 = 1) :
    ∃ s : G, s ^ 2 = 1 ∧ (s : G ⧸ N) = u := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  have hg2 : g ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hu
  refine ⟨g ^ Nat.card N, ?_, ?_⟩
  · have h1 : (⟨g ^ 2, hg2⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← pow_mul, mul_comm, pow_mul]
    exact h2
  · obtain ⟨k, hk⟩ := hN
    rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, hu, one_pow, one_mul]

theorem sec6TwoRankHolds : Sec6TwoRankHolds := by
  intro X _ _ n t hS
  obtain ⟨-, ⟨t₀, L, ht₀, ⟨hLc, ht₀L, -, -⟩, hLn⟩, -⟩ := hS.maxdeg
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu2, huZ⟩ :
      ∃ u : ↥L ⧸ pPrimeCore 2 ↥L, u ^ 2 = 1 ∧ u ∉ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rcases hS.deg with rfl | rfl
    · exact CFSG.GH74.GLS.Stage12.McLRec.exists_noncentral_involution_of_doubleCover hLn
    · exact CFSG.Sporadic.Recognition.LyonsSims.exists_noncentral_involution_of_doubleCover_eleven
        hLn
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨s, hs2, hsu⟩ := exists_sq_eq_one_mk_eq (pPrimeCore 2 ↥L) hodd u hu2
  have ht₀Z : (⟨t₀, ht₀L⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hLc g.2) t₀ (Set.mem_singleton t₀)).symm
  have hmkZ : ∀ x : ↥L, x ∈ center ↥L →
      (x : ↥L ⧸ pPrimeCore 2 ↥L) ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := fun x hx =>
    Subgroup.map_center_le_center (f := QuotientGroup.mk' (pPrimeCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hx)
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply huZ
    rw [← hsu, QuotientGroup.mk_one]
    exact Subgroup.one_mem _
  have hsord : orderOf (s : X) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hs2 hs1
  have hne : (s : X) ≠ t₀ := by
    intro h
    have hs : s = ⟨t₀, ht₀L⟩ := Subtype.ext h
    apply huZ
    rw [← hsu, hs]
    exact hmkZ _ ht₀Z
  have hcomm : Commute (s : X) t₀ :=
    (Subgroup.mem_centralizer_iff.mp (hLc s.2) t₀ (Set.mem_singleton t₀)).symm
  exact CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions X (s : X) t₀ hsord
    ht₀ hne hcomm

end CFSG.OddStandard.Solomon75
