module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcMain
public import CFSG.RankThree.PartOne.SEITZX.F4Two
public import CFSG.RankThree.PartOne.KF.F4ParabolicSums
public import CFSG.LieType.SeitzGeneration.ExcParabolicCard
public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

namespace F4Two

theorem eq_five_or_seven_of_dvd {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : n = 2835 ∨ n = 63) (hdvd : p ∣ n) : p = 5 ∨ p = 7 := by
  have hn' : n ∣ 3 ^ 4 * 5 * 7 := by rcases hn with rfl | rfl <;> norm_num
  rcases (Nat.Prime.dvd_mul hp).1 (hdvd.trans hn') with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
      omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem two_le_pRank_of_pair {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {A B : G} (hA : A ^ p = 1) (hB : B ^ p = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1)
    (hBA : ∀ j < p, B ≠ A ^ j) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  classical
  have hB1 : B ≠ 1 := by simpa using hBA 0 hp.out.pos
  have hAo : orderOf A = p := orderOf_eq_prime hA hA1
  have hBo : orderOf B = p := orderOf_eq_prime hB hB1
  refine CFSG.GroupTheory.two_le_pRank_of_commute (Subgroup.mem_top A) (Subgroup.mem_top B) hAo
    hBo hAB fun hmem => ?_
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hmem
  obtain ⟨j, hj, hjB⟩ := hmem
  exact hBA j (by simpa [hAo] using hj) hjB.symm

theorem exists_mask_of_ne_univ {J : Set (Fin Tag.F4.rank)} (hJ : J ≠ Set.univ) :
    ∃ m : ℕ, (m = 7 ∨ m = 11 ∨ m = 13 ∨ m = 14) ∧
      J ⊆ (CFSG.Timmesfeld.ExceptionalOrders.maskSet .F4 m : Set (Fin Tag.F4.rank)) := by
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hcases : ∀ i : Fin 4, (![14, 13, 11, 7] i : ℕ) = 7 ∨
      (![14, 13, 11, 7] i : ℕ) = 11 ∨ (![14, 13, 11, 7] i : ℕ) = 13 ∨
        (![14, 13, 11, 7] i : ℕ) = 14 := by
    decide
  have hcover : ∀ i k : Fin Tag.F4.rank, k ≠ i →
      k ∈ CFSG.Timmesfeld.ExceptionalOrders.maskSet .F4 (![14, 13, 11, 7] i) := by
    decide
  exact ⟨![14, 13, 11, 7] i, hcases i, fun k hk => by
    exact_mod_cast hcover i k (fun h => hi (h ▸ hk))⟩

end F4Two

variable {K : Type} [Field K]


namespace F4Two

theorem exists_proper_parabolic_of_normalizer_le {τ : Tag} [Finite K] [CharP K 2]
    {K₀ : Subgroup ↥(adjointGroup τ K)}
    (hN : normalizer (((posUnipotent τ K).subgroupOf (adjointGroup τ K) :
      Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) ≤ K₀) (hne : K₀ ≠ ⊤) :
    ∃ J : Set (Fin τ.rank), J ≠ Set.univ ∧
      K₀.map (adjointGroup τ K).subtype = parabolicSubgroup τ K J := by
  classical
  haveI : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  have hBK₀ : (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤ K₀ :=
    borel_subgroupOf_le_normalizer.trans hN
  have hBP : borelGroup τ K ≤ K₀.map (adjointGroup τ K).subtype := fun x hx =>
    ⟨⟨x, borelGroup_le_adjointGroup' hx⟩, hBK₀ hx, rfl⟩
  have hPG : K₀.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ K₀.map (adjointGroup τ K).subtype}
  have hPJ : K₀.map (adjointGroup τ K).subtype = parabolicSubgroup τ K J :=
    (borel_overgroup_classification (τ := τ) (K := K)).1 _ hBP hPG
  refine ⟨J, fun hJu => hne ?_, hPJ⟩
  have h1 : K₀.map (adjointGroup τ K).subtype = adjointGroup τ K := by
    rw [hPJ, hJu]
    exact (standard_parabolic_cells τ K).2.2.2.2.2.1
  rw [eq_top_iff]
  intro x _
  have hx : (x : ModGL τ K) ∈ K₀.map (adjointGroup τ K).subtype := by
    rw [h1]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← Subtype.ext hyx]

theorem prime_eq_five_or_seven_of_dvd_card_parabolic [Finite K] (hK : Nat.card K = 2)
    {J : Set (Fin Tag.F4.rank)} (hJ : J ≠ Set.univ) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hdvd : p ∣ Nat.card (parabolicSubgroup .F4 K J)) : p = 5 ∨ p = 7 := by
  classical
  obtain ⟨m, hm, hsub⟩ := exists_mask_of_ne_univ hJ
  have hle : parabolicSubgroup .F4 K J ≤ parabolicSubgroup .F4 K
      (CFSG.Timmesfeld.ExceptionalOrders.maskSet .F4 m : Set (Fin Tag.F4.rank)) :=
    ((standard_parabolic_cells .F4 K).2.2.2.1 J _).2 hsub
  have hdvd' := hdvd.trans (Subgroup.card_dvd_of_le hle)
  rw [(standard_parabolic_cells .F4 K).2.2.2.2.2.2] at hdvd'
  haveI : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_F4,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4, hK,
    CFSG.LieType.SeitzGeneration.finsum_parabolicWeylGroup_eq] at hdvd'
  have hcop : Nat.Coprime p (2 ^ 24) :=
    Nat.Coprime.pow_right 24 ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
  have h1 : p ∣ CFSG.Timmesfeld.ExceptionalOrders.parabolicSum .F4
      (CFSG.Timmesfeld.ExceptionalOrders.maskSet .F4 m : Set (Fin Tag.F4.rank)) 2 := by
    rw [show (2 - 1 : ℕ) ^ 4 = 1 by norm_num, one_mul] at hdvd'
    exact hcop.dvd_of_dvd_mul_left hdvd'
  refine eq_five_or_seven_of_dvd hp hp5 ?_ h1
  rcases hm with rfl | rfl | rfl | rfl
  · rw [CFSG.RankThree.PartOne.KFU.parabolicSum_F4_two_B3]
    exact Or.inl rfl
  · rw [CFSG.RankThree.PartOne.KFU.parabolicSum_F4_two_A2A1]
    exact Or.inr rfl
  · rw [CFSG.RankThree.PartOne.KFU.parabolicSum_F4_two_A1A2]
    exact Or.inr rfl
  · rw [CFSG.RankThree.PartOne.KFU.parabolicSum_F4_two_C3]
    exact Or.inl rfl

theorem two_le_pRank_top_F4_two [CharP K 2] [Finite K] {p : ℕ}
    (hp : p = 5 ∨ p = 7) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup .F4 K)) := by
  have hc := (Certificates.certificate14997 :
    CFSG.RankThree.PartOne.SEITZX.cert5.check = true ∧
      CFSG.RankThree.PartOne.SEITZX.cert7.check = true)
  rcases hp with rfl | rfl
  · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨hAp, hBp, hAB, hA1, hBA, -⟩ :=
      CFSG.RankThree.PartOne.SEITZX.PlaneCert.facts (K := K)
        CFSG.RankThree.PartOne.SEITZX.cert5 hc.1
    exact two_le_pRank_of_pair hAp hBp hAB hA1 hBA
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨hAp, hBp, hAB, hA1, hBA, -⟩ :=
      CFSG.RankThree.PartOne.SEITZX.PlaneCert.facts (K := K)
        CFSG.RankThree.PartOne.SEITZX.cert7 hc.2
    exact two_le_pRank_of_pair hAp hBp hAB hA1 hBA

end F4Two

theorem leviSubAt_adjointGroup_F4_two [Finite K] [CharP K 2]
    (h2 : Nat.card K = 2) : LeviSubAt ↥(adjointGroup .F4 K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ : ∃ P : Sylow 2 ↥(adjointGroup .F4 K),
      (P : Subgroup ↥(adjointGroup .F4 K)) =
        (posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K) :=
    (RootWeightDatum.ordinary (K := K) .F4).exists_sylow_eq_unipotent 2
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => ?_
  intro _ hp h5 hrank _ hne hsyl
  exfalso
  rw [hT₀] at hN
  obtain ⟨J, hJ, hPJ⟩ := F4Two.exists_proper_parabolic_of_normalizer_le hN hne
  have hcard : Nat.card K₀ = Nat.card (parabolicSubgroup .F4 K J) := by
    rw [← hPJ, Subgroup.card_map_of_injective (adjointGroup .F4 K).subtype_injective]
  have hp57 := F4Two.prime_eq_five_or_seven_of_dvd_card_parabolic h2 hJ hp h5
    (hcard ▸ dvd_card_of_sylow_hyp hp hsyl)
  have := F4Two.two_le_pRank_top_F4_two (K := K) hp57
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
