module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Global
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.CentralPElem
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.Sporadic.Recognition.J3MultiplierCert

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

theorem not_sq_dvd_card_J3 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 50232960 := by
  intro h
  have hc2 : Nat.Coprime p (2 ^ 7 * 3 ^ 5) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 h2))
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).2 h3))
  have h' : p ^ 2 ∣ (2 ^ 7 * 3 ^ 5) * 1615 := by norm_num; exact h
  have h1615 : p ^ 2 ∣ 1615 := (Nat.Coprime.pow_left 2 hc2).dvd_of_dvd_mul_left h'
  have hp1615 : p ∣ 5 * (17 * 19) := by
    have : p ∣ 1615 := (dvd_pow_self p two_ne_zero).trans h1615
    norm_num; exact this
  rcases (Nat.Prime.dvd_mul hp).1 hp1615 with h5 | h
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5
    subst this; norm_num at h1615
  · rcases (Nat.Prime.dvd_mul hp).1 h with h17 | h19
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h17
      subst this; norm_num at h1615
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h19
      subst this; norm_num at h1615

theorem isCyclic_of_isPGroup_J3 {p : ℕ} [hp : Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) (S : Subgroup NativeSporadic.J3) (hS : IsPGroup p S) :
    IsCyclic S := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS
  have hdvd : Nat.card S ∣ 50232960 := by
    rw [← CFSG.Sporadic.J3.card_J3]; exact Subgroup.card_subgroup_dvd_card S
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · haveI : Subsingleton S := (Nat.card_eq_one_iff_unique.1 (by simpa using hk)).1
      infer_instance
    · exact isCyclic_of_prime_card (by simpa using hk)
  · exfalso
    apply not_sq_dvd_card_J3 p hp.1 h2 h3
    rw [hk] at hdvd
    exact (pow_dvd_pow p hk2).trans hdvd

theorem not_isSolvable_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hc : ¬ (Nat.card Q).Prime) : ¬ Group.IsSolvable Q := by
  intro hs
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.2 hs
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  exact hc (IsSimpleGroup.prime_card (α := Q))

theorem theta_eq_bot_aux {L : Type*} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    {Q : Type*} [Group Q] [IsSimpleGroup Q] (e : L ⧸ center L ≃* Q) (hQ : ¬ Group.IsSolvable Q)
    (hodd : Odd (Nat.card (center L)))
    (hcyc : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → ∀ S : Subgroup Q, IsPGroup p S →
      IsCyclic S) : aschbacherSolvableCore 3 L = ⊥ := by
  obtain ⟨π, hπs, hπker⟩ : ∃ π : L →* Q, Function.Surjective π ∧ π.ker = center L :=
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center L)),
      e.surjective.comp (QuotientGroup.mk'_surjective _), by
        ext x
        simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]⟩
  obtain ⟨hsolv, -, h3T, -⟩ := solvable_prime_complement_core_characterization
    (H := L) Nat.prime_three
  have hTc : aschbacherSolvableCore 3 L ≤ center L := by
    have hN : ((aschbacherSolvableCore 3 L).map π).Normal :=
      Subgroup.Normal.map inferInstance π hπs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((aschbacherSolvableCore 3 L).map π) with
      h0 | h1
    · intro x hx
      rw [← hπker, MonoidHom.mem_ker]
      exact (Subgroup.mem_bot.1 (h0 ▸ Subgroup.mem_map_of_mem π hx))
    · exfalso
      have hsolv' : Group.IsSolvable ((aschbacherSolvableCore 3 L).map π) :=
        solvable_of_surjective (π.subgroupMap_surjective _)
      rw [h1] at hsolv'
      exact hQ (solvable_of_surjective (f := (Subgroup.topEquiv (G := Q)).toMonoidHom)
        (Subgroup.topEquiv (G := Q)).surjective)
  by_contra hne
  have hcard : Nat.card (aschbacherSolvableCore 3 L) ≠ 1 := fun h1 =>
    hne (Subgroup.card_eq_one.1 h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hxT : (x : L) ∈ aschbacherSolvableCore 3 L := x.2
  have hxo : orderOf (x : L) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hxc : (x : L) ∈ center L := hTc hxT
  by_cases hp3 : p = 3
  · exact h3T (hp3 ▸ hpd)
  by_cases hp2 : p = 2
  · subst hp2
    have h2d : 2 ∣ Nat.card (center L) := by
      have := Subgroup.orderOf_dvd_natCard _ hxc
      rwa [hxo] at this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2d)
  · have := eq_one_of_mem_center_of_cyclic_quotient hperf π hπker.le
      (fun S hS => hcyc p hp2 hp3 S hS) hxc hxo
    rw [this, orderOf_one] at hxo
    exact hp.one_lt.ne hxo

variable {G : Type} [Group G] [Finite G]

section Main

set_option linter.unusedSectionVars false

theorem not_isSolvable_J3 : ¬ Group.IsSolvable NativeSporadic.J3 := by
  haveI : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
  haveI : Finite NativeSporadic.J3 := (CFSG.Sporadic.J3.fam_j3_simplicity).1
  apply not_isSolvable_of_simple
  rw [CFSG.Sporadic.J3.card_J3]
  norm_num

theorem sec217ThetaOne_holds : Sec217ThetaOne (G := G) := by
  intro A E U c L h
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hperf : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  obtain ⟨e⟩ := h.quot
  have hs : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hodd : Odd (Nat.card (center ↥L)) :=
    CFSG.ComponentClassification.RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
      CFSG.Sporadic.Recognition.J3Multiplier.noPerfectDoubleCover_nativeJ3_of_certificate
      ↥L (Group.isPerfect_def.1 hperf) ⟨e⟩
  have hcyc : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → ∀ S : Subgroup NativeSporadic.J3,
      IsPGroup p S → IsCyclic S := fun p _ h2 h3 S hS => isCyclic_of_isPGroup_J3 h2 h3 S hS
  exact @theta_eq_bot_aux ↥L _ _ hperf NativeSporadic.J3 _ hs e not_isSolvable_J3 hodd hcyc

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
