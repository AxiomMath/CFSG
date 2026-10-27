module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIConfigO2
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem ThreeFourSolvThreeNoneAt.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : ThreeFourSolvThreeNoneAt X) : ThreeFourSolvThreeNoneAt X' := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hK hKX
  obtain ⟨f⟩ := hKX
  exact h Y K Y₀ E R I₀ σ hK ⟨f.trans e.symm⟩

theorem ThreeFourSolvThreeLeAt.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : ThreeFourSolvThreeLeAt X) : ThreeFourSolvThreeLeAt X' := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hK hKX
  obtain ⟨f⟩ := hKX
  exact h Y K Y₀ E R I₀ σ hK ⟨f.trans e.symm⟩

theorem ThreeFourSolvThreeNoneAt.of_lt_pRank {X : Type*} [Group X] [Finite X]
    (hX : 3 < CFSG.pRank 3 X) : ThreeFourSolvThreeNoneAt X := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ _ hKX _ hrk
  exfalso
  obtain ⟨e⟩ := hKX
  have h1 : CFSG.pRank 3 ↥K = CFSG.pRank 3 X := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
  have h2 : CFSG.pRank 3 ↥K ≤ CFSG.pRank 3 ↥(⊤ : Subgroup Y) := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact CFSG.SectionRank.pRank_mono (by norm_num) le_top
  omega

theorem normalizer_sylow_le_threeFourCore {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (R : Sylow p Y) {E : Subgroup Y} (hER : E ≤ R)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    normalizer ((R : Subgroup Y) : Set Y) ≤ if 3 ≤ CFSG.pRank p (R : Subgroup Y) then
      GLBWeakCore p (R : Subgroup Y) else GLBCore p 1 E := by
  haveI : Fact p.Prime := ⟨hp⟩
  split_ifs with h3
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    exact CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore_of_rank p hp _ h3
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    have h2 : CFSG.Open.pRank p (R : Subgroup Y) ≤ 2 := by omega
    have hcen : ∀ w : Y, w ∈ (R : Subgroup Y) → w ^ p = 1 →
        (∀ g ∈ (R : Subgroup Y), g * w = w * g) → w ∈ E := fun w hwR hwp hwc =>
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free.mem_of_central_of_pRank_le_two hp h2 hER
        hE hEc hwR hwp hwc
    set F : Subgroup Y :=
      E ⊓ (Subgroup.center ↥(R : Subgroup Y)).map (R : Subgroup Y).subtype with hF
    have hmemF : ∀ w : Y, w ∈ F ↔ w ∈ E ∧ w ∈ (R : Subgroup Y) ∧
        ∀ g ∈ (R : Subgroup Y), g * w = w * g := by
      intro w
      constructor
      · rintro ⟨hwE, ⟨v, hv, rfl⟩⟩
        refine ⟨hwE, v.2, fun g hg => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hv ⟨g, hg⟩)
      · rintro ⟨hwE, hwR, hwc⟩
        refine ⟨hwE, ⟨w, hwR⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
        exact hwc g g.2
    have hconj : ∀ g ∈ normalizer ((R : Subgroup Y) : Set Y), ∀ w ∈ F, g * w * g⁻¹ ∈ F := by
      intro g hg w hw
      obtain ⟨hwE, hwR, hwc⟩ := (hmemF w).mp hw
      have hgR : ∀ r : Y, r ∈ (R : Subgroup Y) ↔ g * r * g⁻¹ ∈ (R : Subgroup Y) :=
        Subgroup.mem_normalizer_iff.mp hg
      have hwR' : g * w * g⁻¹ ∈ (R : Subgroup Y) := (hgR w).mp hwR
      have hwp : (g * w * g⁻¹) ^ p = 1 := by
        rw [conj_pow, hE.2 w hwE, mul_one, mul_inv_cancel]
      have hwc' : ∀ r ∈ (R : Subgroup Y), r * (g * w * g⁻¹) = g * w * g⁻¹ * r := by
        intro r hr
        have hr' : g⁻¹ * r * g ∈ (R : Subgroup Y) := by
          rw [hgR]
          simpa [mul_assoc] using hr
        have := hwc _ hr'
        calc r * (g * w * g⁻¹) = g * ((g⁻¹ * r * g) * w) * g⁻¹ := by group
          _ = g * (w * (g⁻¹ * r * g)) * g⁻¹ := by rw [this]
          _ = g * w * g⁻¹ * r := by group
      exact (hmemF _).mpr ⟨hcen _ hwR' hwp hwc', hwR', hwc'⟩
    have hNF : normalizer ((R : Subgroup Y) : Set Y) ≤ normalizer (F : Set Y) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hconj g hg w, fun h => ?_⟩
      have := hconj g⁻¹ (Subgroup.inv_mem _ hg) _ h
      simpa [mul_assoc] using this
    have hpR : p ∣ Nat.card (R : Subgroup Y) :=
      (dvd_pow_self p two_ne_zero).trans (by rw [← hEc]; exact card_dvd_of_le hER)
    haveI : Group.IsNilpotent (R : Subgroup Y) := R.isPGroup'.isNilpotent
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' p (Group.IsNilpotent.prime_dvd_card_center hpR)
    set z : Y := ((x : (R : Subgroup Y)) : Y) with hz
    have hzR : z ∈ (R : Subgroup Y) := (x : (R : Subgroup Y)).2
    have hzo : orderOf z = p := by rw [hz, orderOf_coe, orderOf_coe, hx]
    have hzp : z ^ p = 1 := hzo ▸ pow_orderOf_eq_one z
    have hzc : ∀ g ∈ (R : Subgroup Y), g * z = z * g := fun g hg =>
      congrArg Subtype.val (mem_center_iff.mp x.2 ⟨g, hg⟩)
    have hzF : z ∈ F := (hmemF z).mpr ⟨hcen z hzR hzp hzc, hzR, hzc⟩
    have hrank : 1 ≤ CFSG.Open.pRank p F :=
      CFSG.SectionRank.le_pRank hp.one_lt (zpowers_le.mpr hzF) (CFSG.Open.isElemAbelian_zpowers hzp)
        (by rw [Nat.card_zpowers, hzo, pow_one])
    exact hNF.trans (le_sSup ⟨F, inf_le_left, hrank, rfl⟩)

section J

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

theorem cube_mem_pCore_two (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) :
    ∀ g ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀),
      g ^ 3 ∈ CFSG.pCore 2 I₀ := by
  intro g hg
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 I₀) g ∈
      CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) := by
    have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 I₀)) hg
    rwa [SUPair.map_oUpperTwo, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)] at h
  have h3 := IsSymThreeOrSUThreeTwo.cube kFactSUThreeTwoShape_holds hb _ h1
  rw [← QuotientGroup.eq_one_iff]
  simpa using h3

theorem normal_map_subgroupOf_range (σ : I₀ →* Y) {N : Subgroup I₀} (hN : N.Normal) :
    ((N.map σ).subgroupOf σ.range).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_le_range σ N)]
  rintro _ ⟨h, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨h * n * h⁻¹, hN.conj_mem n hn h, by simp⟩
  · rintro ⟨n, hn, hx⟩
    refine ⟨h⁻¹ * n * h, by simpa using hN.conj_mem n hn h⁻¹, ?_⟩
    rw [map_mul, map_mul, hx, map_inv]
    group

theorem oUpperTwo_map_le {Y₀ : Subgroup Y} (σ : I₀ →* Y) (hσY : σ.range ≤ Y₀) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ Y₀ :=
  (Subgroup.map_le_range σ _).trans hσY

theorem normal_oUpperTwo_top :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := CFSG.ComponentClassification.RankTwoHypIIClassical.oUpperTwo_conj_mem
    (Subgroup.mem_top g) hn
  simpa using h

theorem isSubnormal_oUpperTwo_map {Y₀ : Subgroup Y} (σ : I₀ →* Y)
    (hσs : IsSubnormal σ.range Y₀) :
    IsSubnormal ((CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ) Y₀ :=
  IsSubnormal.step (Subgroup.map_le_range σ _)
    (normal_map_subgroupOf_range σ normal_oUpperTwo_top) hσs

theorem map_pCore_two_le_pCoreOf {Y₀ : Subgroup Y} (σ : I₀ →* Y)
    (hσs : IsSubnormal σ.range Y₀) : (CFSG.pCore 2 I₀).map σ ≤ pCoreOf 2 Y₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal ?_
    (CFSG.pCore_isPGroup.map σ)
  exact IsSubnormal.step (Subgroup.map_le_range σ _)
    (normal_map_subgroupOf_range σ inferInstance) hσs

theorem cube_mem_of_pCoreOf_le {Y₀ C : Subgroup Y} (σ : I₀ →* Y)
    (hσs : IsSubnormal σ.range Y₀) (hO2 : pCoreOf 2 Y₀ ≤ C)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) :
    ∀ x ∈ (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ, x ^ 3 ∈ C := by
  rintro _ ⟨g, hg, rfl⟩
  rw [← map_pow]
  exact hO2 (map_pCore_two_le_pCoreOf σ hσs
    (Subgroup.mem_map_of_mem σ (cube_mem_pCore_two hb g hg)))

end J

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
