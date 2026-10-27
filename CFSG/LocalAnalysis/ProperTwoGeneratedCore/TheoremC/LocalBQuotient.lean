module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Config

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normalizer_ne_top_of_not_le_twoCore {V : Subgroup X} (hV : IsPGroup 2 V)
    (hVO : ¬ V ≤ CFSG.Open.pCore 2 X) : Subgroup.normalizer (V : Set X) ≠ ⊤ := fun htop =>
  hVO (le_twoCore (Subgroup.normalizer_eq_top_iff.mp htop) hV)

theorem card_quotient_subgroup_lt {N : Subgroup X} (hN : N ≠ ⊤) (K : Subgroup N) :
    Nat.card (N ⧸ K) < Nat.card X := by
  have h₁ : Nat.card (N ⧸ K) ≤ Nat.card N :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card K)
  have h₂ := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hN)
  rw [Subgroup.card_top] at h₂
  omega

theorem exists_sylow_eq_subgroupOf_of_card_max {N R : Subgroup X} (hRN : R ≤ N)
    (hR : IsPGroup 2 R)
    (hmax : ∀ R' : Subgroup X, R' ≤ N → IsPGroup 2 R' → Nat.card R' ≤ Nat.card R) :
    ∃ S : Sylow 2 N, (S : Subgroup N) = R.subgroupOf N := by
  obtain ⟨S, hS⟩ := (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm).exists_le_sylow
  refine ⟨S, (Subgroup.eq_of_le_of_card_ge hS ?_).symm⟩
  have h := hmax _ (Subgroup.map_subtype_le _) (S.isPGroup'.map N.subtype)
  rwa [Subgroup.card_map_of_injective N.subtype_injective,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv] at h

theorem pRank_le_twoRank_of_le {N R : Subgroup X} (hRN : R ≤ N) :
    CFSG.Open.pRank 2 R ≤ twoRank N := by
  have h := subgroup_image_two_rank_eq N (R.subgroupOf N)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRN] at h
  rw [h]
  exact CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 2 (by decide) le_top

theorem rankThree_quotient_coreConfig {Y : Subgroup X} {u z : X} (hc : CoreConfig Y u z)
    {N R : Subgroup X} (huN : u ∈ N) (hNY : ¬ N ≤ Y) (hRN : R ≤ N) (hRY : R ≤ Y)
    (hR : IsPGroup 2 R)
    (hmax : ∀ R' : Subgroup X, R' ≤ N → IsPGroup 2 R' → Nat.card R' ≤ Nat.card R)
    {z' : X} (hz'R : z' ∈ R) (hz'c : ∀ r ∈ R, Commute r z') (hz' : orderOf z' = 2)
    (hne : z' ≠ u) (hRrank : 3 ≤ CFSG.Open.pRank 2 R) :
    pPrimeCore 2 N ≤ Y.subgroupOf N ∧
      CoreConfig ((Y.subgroupOf N).map (QuotientGroup.mk' (pPrimeCore 2 N)))
        (QuotientGroup.mk' (pPrimeCore 2 N) ⟨u, huN⟩)
        (QuotientGroup.mk' (pPrimeCore 2 N) ⟨z', hRN hz'R⟩) := by
  obtain ⟨P, hPY, hcore, -, -⟩ := hc.sylow
  obtain ⟨S, hS⟩ := exists_sylow_eq_subgroupOf_of_card_max hRN hR hmax
  have hKodd : Odd (Nat.card (pPrimeCore 2 N)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  have hSY : (S : Subgroup N) ≤ Y.subgroupOf N := by
    rw [hS]
    intro g hg
    exact Subgroup.mem_subgroupOf.mpr (hRY (Subgroup.mem_subgroupOf.mp hg))
  have hSY' : (S : Subgroup N).map N.subtype ≤ Y := by
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hSY hg)
  have hΓ : properTwoGenCoreGamma (S : Subgroup N) 2 ≤ Y.subgroupOf N :=
    centralizer_full_core_le_overgroup P Y hPY hcore N S hSY'
  have hYN : Y.subgroupOf N ≠ ⊤ := by
    intro htop
    apply hNY
    intro g hg
    have hmem : (⟨g, hg⟩ : N) ∈ Y.subgroupOf N := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have hucenter : (⟨u, huN⟩ : N) ∈ Subgroup.center N :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc.commute_center g).eq
  have huorder : orderOf (⟨u, huN⟩ : N) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hc.order
  have hz'N : orderOf (⟨z', hRN hz'R⟩ : N) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz'
  obtain ⟨hKΓ, hΓimage, -, -, hrank, hodd, hucen, huord, -⟩ :=
    central_involution_proper_core_local_structure (hRrank.trans (pRank_le_twoRank_of_le hRN))
      _ hucenter huorder S (fun htop => hYN (top_le_iff.mp (htop ▸ hΓ)))
  have hKY : pPrimeCore 2 N ≤ Y.subgroupOf N := hKΓ.trans hΓ
  refine ⟨hKY, hodd, hucen, huord, ?_, ⟨S.mapSurjective (QuotientGroup.mk'_surjective _), ?_,
    ?_, ?_, ?_⟩, hrank, ?_, ?_⟩
  · intro htop
    apply hYN
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' (pPrimeCore 2 N))) htop
    rwa [Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk']), Subgroup.comap_top] at h
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSY
  · rw [← hΓimage]
    exact Subgroup.map_mono hΓ
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem _ (hS ▸ Subgroup.mem_subgroupOf.mpr hz'R)
  · rw [Sylow.coe_mapSurjective]
    rintro _ ⟨s, hs, rfl⟩
    have hsR : (s : X) ∈ R := Subgroup.mem_subgroupOf.mp (hS ▸ hs)
    exact (show Commute s ⟨z', hRN hz'R⟩ from Subtype.ext (hz'c _ hsR).eq).map _
  · exact orderOf_mk_eq_two hKodd hz'N
  · intro heq
    apply hne
    have hz'z' : (⟨z', hRN hz'R⟩ : N) * ⟨z', hRN hz'R⟩ = 1 := by
      rw [← pow_two, ← hz'N, pow_orderOf_eq_one]
    have huu : (⟨u, huN⟩ : N) * ⟨u, huN⟩ = 1 := by
      rw [← pow_two, ← huorder, pow_orderOf_eq_one]
    have h := eq_of_mk_eq_of_commute hKodd
      (fun n _ => (Subgroup.mem_center_iff.mp hucenter n).symm) huu hz'z' heq.symm
    exact (congrArg Subtype.val h).symm

end CFSG.ProperTwoGeneratedCore.TheoremC
