module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Local.PLengthOneNarrowSylowNormalComplement
import CFSG.FeitThompson.Local.RankTwoComplementPrimeNormalizerBound
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.MinimalSimpleProperSubgroupPLengthOne
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem isNormalPComplement_inf_commutator_of_isCoatom [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {L : Subgroup G} (hL : IsCoatom L)
    {p : ℕ} (hp : p.Prime) (hpL : p ∣ Nat.card ↥L) (hrank : elementaryAbelianPRank p ↥L = 2) :
    IsNormalPComplement p
      ((pComplCore p ↥L ⊓ commutator ↥L).subgroupOf (commutator ↥L)) := by
  have hfp := Fact.mk hp
  have hsolvL : Group.IsSolvable ↥L := hsolv L hL.1
  have hoddL : Odd (Nat.card ↥L) := hodd.of_dvd_nat L.card_subgroup_dvd_card
  let P : Sylow p ↥L := Classical.arbitrary _
  have hPcard : Nat.card ↥(P : Subgroup ↥L) = p ^ (Nat.card ↥L).factorization p :=
    P.card_eq_multiplicity
  have hnarrow : IsPNarrow p ↥(P : Subgroup ↥L) :=
    isPNarrow_of_elementaryAbelianPRank_le_two
      (by rw [← hrank]; exact elementaryAbelianPRank_subgroup_le hp.one_lt _)
  have halt := isCyclic_or_maximal_plane_of_isPNarrow hp (hoddL.of_dvd_nat hpL)
    (IsPGroup.of_card hPcard) hnarrow
  have hV : ¬ p ∣ (pComplPCore p ↥L).index :=
    hasPLengthLeOne_iff_not_dvd_index_pComplPCore.1
      (hasPLengthLeOne_of_isCoatom hna hodd hsolv hL hp)
  exact isNormalPComplement_inf_commutator (P := (P : Subgroup ↥L)) hp hoddL hpL hPcard hV halt

theorem exists_isPGroup_two_le_elementaryAbelianPRank_inf_normalizer [Finite G] {L : Subgroup G}
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hrank : elementaryAbelianPRank p ↥L = 2)
    {D : Subgroup ↥L} [D.Normal] (hDp : ¬ p ∣ Nat.card ↥D) (hqD : q ∣ Nat.card ↥D) :
    ∃ Y : Subgroup G, Y ≤ L ∧ Y ≠ ⊥ ∧ IsPGroup q ↥Y ∧
      2 ≤ elementaryAbelianPRank p ↥(L ⊓ normalizer (Y : Set G) : Subgroup G) := by
  have hfp := Fact.mk hp
  have hfq := Fact.mk hq
  let S : Sylow q ↥D := Classical.arbitrary _
  set Y₀ : Subgroup ↥L := (S : Subgroup ↥D).map D.subtype with hY₀
  have hY₀D : Y₀ ≤ D := Subgroup.map_subtype_le _
  have hY₀card : Nat.card ↥Y₀ = q ^ (Nat.card ↥D).factorization q := by
    rw [hY₀, Subgroup.card_subtype, S.card_eq_multiplicity]
  have hfrat : normalizer (Y₀ : Set ↥L) ⊔ D = ⊤ :=
    normalizer_sup_eq_top_of_normal (p := q) hY₀D hY₀card
  set N : Subgroup ↥L := normalizer (Y₀ : Set ↥L) with hN
  have hidx : N.index ∣ Nat.card ↥D := by
    have h := index_subgroupOf_inf_eq_index (K := D) (L := N) (by rw [sup_comm]; exact hfrat)
    rw [← h]
    exact Subgroup.index_dvd_card _
  have hpidx : ¬ p ∣ N.index := fun hd => hDp (hd.trans hidx)
  have hfac : (Nat.card ↥N).factorization p = (Nat.card ↥L).factorization p := by
    have hh := congrArg (fun n => n.factorization p) (Subgroup.card_mul_index N)
    simp only [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx] at hh
    simpa using hh
  let Q : Sylow p ↥N := Classical.arbitrary _
  set Qm : Subgroup ↥L := (Q : Subgroup ↥N).map N.subtype with hQm
  have hQmcard : Nat.card ↥Qm = p ^ (Nat.card ↥L).factorization p := by
    rw [hQm, Subgroup.card_subtype, Q.card_eq_multiplicity, hfac]
  have hQrank : elementaryAbelianPRank p ↥Qm = elementaryAbelianPRank p ↥L :=
    elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp hQmcard
  have h2N : 2 ≤ elementaryAbelianPRank p ↥N := by
    rw [← hrank, ← hQrank]
    exact elementaryAbelianPRank_le_of_le hp.one_lt (Subgroup.map_subtype_le _)
  refine ⟨Y₀.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  ·
    intro hbot
    have hone : Nat.card ↥(Y₀.map L.subtype) = 1 := by rw [hbot]; simp
    rw [Subgroup.card_subtype, hY₀card] at hone
    have hq1 : 1 ≤ (Nat.card ↥D).factorization q :=
      Nat.Prime.factorization_pos_of_dvd hq Nat.card_pos.ne' hqD
    have := Nat.one_lt_pow (by omega : (Nat.card ↥D).factorization q ≠ 0) hq.one_lt
    omega
  · exact IsPGroup.of_card (n := (Nat.card ↥D).factorization q)
      (by rw [Subgroup.card_subtype, hY₀card])
  · have hle : N.map L.subtype ≤ (L ⊓ normalizer ((Y₀.map L.subtype : Subgroup G) : Set G)) := by
      rintro x ⟨n, hn, rfl⟩
      exact ⟨n.2, mem_normalizer_map_subtype hn⟩
    calc 2 ≤ elementaryAbelianPRank p ↥N := h2N
      _ = elementaryAbelianPRank p ↥(N.map L.subtype) :=
        elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
          (N.equivMapOfInjective L.subtype L.subtype_injective)
      _ ≤ _ := elementaryAbelianPRank_le_of_le hp.one_lt hle

theorem notMem_tauTwoPrimes_of_commutator_ne_bot [Finite G]
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (hG : IsFBGAmbient G) {M L E : Subgroup G} {p : ℕ}
    (hsetup : IsNonconjugateSetup M L E p)
    (hne : ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ ≠ ⊥) :
    p ∉ tauTwoPrimes L := by
  intro hpτ
  have hsimple := hG.isSimpleGroup
  have : Fintype G := Fintype.ofFinite G
  have hGmin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hM, hL, hnc, hEM, hsd, hp, hpE, hpL⟩ := hsetup
  have hfp := Fact.mk hp
  obtain ⟨hHallOf, -, -⟩ := h₁ G hGmin M hM
  have hpσ : p ∉ sigmaPrimes M := by
    have h := hHallOf.2.notMem_of_mem_primeFactors_index
    rw [index_subgroupOf_left_eq hsd] at h
    exact h p (Nat.mem_primeFactors.2 ⟨hp, hpE, Nat.card_pos.ne'⟩)
  set R : Subgroup G := ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ with hR
  have hnormML : (M ⊓ L : Subgroup G) ≤ normalizer ((sigmaCore M ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf (le_trans inf_le_left (le_normalizer_sigmaCore M))
      (le_trans inf_le_right Subgroup.le_normalizer)
  have hRS : R ≤ sigmaCore M :=
    (commutator_le_left_of_le_normalizer hnormML).trans inf_le_left
  have hRcomm : R ≤ (⁅L, L⁆ : Subgroup G) := Subgroup.commutator_mono inf_le_right inf_le_right
  obtain ⟨q, hq, hqR⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥R)
    (fun h1 => hne (Subgroup.card_eq_one.1 h1))
  have hqσ : q ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q
      (Nat.mem_primeFactors.2 ⟨hq, hqR.trans (Subgroup.card_dvd_of_le hRS), Nat.card_pos.ne'⟩)
  have hqp : q ≠ p := fun h => hpσ (h ▸ hqσ)
  have hqL' : q ∣ Nat.card ↥(commutator ↥L) := by
    rw [natCard_commutator_subtype]
    exact hqR.trans (Subgroup.card_dvd_of_le hRcomm)
  set D : Subgroup ↥L := pComplCore p ↥L ⊓ commutator ↥L with hD
  have hDnormal : D.Normal := by rw [hD]; exact Subgroup.normal_inf_normal _ _
  have hDp : ¬ p ∣ Nat.card ↥D :=
    fun hd => not_dvd_natCard_pComplCore hp ↥L (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨n, hn⟩ :=
    (isNormalPComplement_inf_commutator_of_isCoatom hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable hL hp (dvd_natCard_of_mem_tauTwoPrimes hpτ)
      (elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ)).exists_index_eq_pow
  have hqD : q ∣ Nat.card ↥D := by
    have hmul := Subgroup.card_mul_index (D.subgroupOf (commutator ↥L))
    rw [natCard_subgroupOf (inf_le_right : D ≤ commutator ↥L), hn] at hmul
    rcases (Nat.Prime.dvd_mul hq).1 (hmul ▸ hqL') with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)) hqp
  obtain ⟨Y, hYL, hYne, hYq, h2⟩ :=
    have := hDnormal
    exists_isPGroup_two_le_elementaryAbelianPRank_inf_normalizer hp hq
      (elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ) hDp hqD
  have hbound := elementaryAbelianPRank_inf_normalizer_le_one_of_mem_tauTwoPrimes h₂ h₃ hGmin
    hM hL hnc hsd hp hpE hpτ hq hqσ hYL hYne hYq
  omega

theorem FBG_nonconjugate_intersection_excludes_tau_two
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u}) :
    Statements.FBG_nonconjugate_intersection_excludes_tau_two.{u} := by
  intro G _ _ hG M L E p hsetup hne
  exact notMem_tauTwoPrimes_of_commutator_ne_bot h₁ h₂ h₃ hG hsetup hne

end

end CFSG.FeitThompson.Proofs
