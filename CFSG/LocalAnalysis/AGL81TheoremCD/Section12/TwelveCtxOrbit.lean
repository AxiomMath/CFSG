module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenBlockNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOrbit
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.ComponentClassification.AS76b (oUpperTwo)

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_oUpperTwo_of_pRank_three_le_three {X I₀ : Subgroup G}
    (hI₀ : I₀ ∈ cZero X) (h3 : 3 ∣ Nat.card (oUpperTwo I₀))
    (hm3 : CFSG.Open.pRank 3 X ≤ 3) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    {B : Subgroup G} (hB : IsPGroup d B) (hBX : B ≤ Subgroup.normalizer (X : Set G)) :
    B ≤ Subgroup.normalizer (oUpperTwo I₀ : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hmove
  obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
  have hk' : b ^ d ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h4 : 4 ≤ CFSG.Open.pRank 3 X :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.TenTenClaimOrbit.rank_of_cZero_orbit
      hI₀ h3 (hBX hb) hd hk' hmove).2 hd5
  omega

theorem le_normalizer_of_isTwoPrimeComponent_of_isPGroup {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (ht : ∃ t ∈ barM M L, orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) {B : Subgroup G} (hB : IsPGroup d B) (hBM : B ≤ M) :
    B ≤ Subgroup.normalizer (L : Set G) := by
  refine hL.le_normalizer (S := B) ?_ hBM
  exact le_normalizer_barM_of_isPGroup hL hm3 ht hd hd5 (hB.comap_subtype.map _)

theorem oPPrimeHull_le_normalizer_of_isTwoPrimeComponent {M A L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (ht : ∃ t ∈ barM M L, orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hAM : A ≤ M) :
    oPPrimeHull d A ≤ Subgroup.normalizer (L : Set G) := by
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨hxA, k, hk⟩
  have hB : IsPGroup d (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  exact le_normalizer_of_isTwoPrimeComponent_of_isPGroup hL hm3 ht hd hd5 hB
    (Subgroup.zpowers_le.mpr (hAM hxA)) (Subgroup.mem_zpowers x)

theorem oPPrimeHull_le_normalizer_oUpperTwo {M H L I₀ : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (ht : ∃ t ∈ barM M L, orderOf t = 3 ∧
      t ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hI₀ : I₀ ∈ cZero (H ⊓ L))
    (h3 : 3 ∣ Nat.card (oUpperTwo I₀)) :
    oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (oUpperTwo I₀ : Set G) := by
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨hxHM, k, hk⟩
  have hB : IsPGroup d (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hzL : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isTwoPrimeComponent_of_isPGroup hL hm3 ht hd hd5 hB
      (Subgroup.zpowers_le.mpr hxHM.2)
  have hzH : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxHM.1
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (H ⊓ L : Set G) :=
    (le_inf (hzH.trans Subgroup.le_normalizer) hzL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hm3' : CFSG.Open.pRank 3 (H ⊓ L) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
      (inf_le_right.trans hL.le)).trans hm3
  exact le_normalizer_oUpperTwo_of_pRank_three_le_three hI₀ h3 hm3' hd hd5 hB hzN
    (Subgroup.mem_zpowers x)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
