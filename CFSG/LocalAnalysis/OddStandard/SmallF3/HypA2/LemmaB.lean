module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypUVert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypUDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesV

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem false_of_datum_typU (hI : Phase1Inputs) (hA7 : TwoA7RankOne) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) → Assembly.KProper Catalog G → ¬ Catalog G →
    ∀ (q₀ : ℕ), Odd q₀ → 5 ≤ q₀ →
    ∀ (v : G) (K N : Subgroup G) (c : G),
      GS82PumpInputs.IsDatum q₀ v K N c → TypU ↥K → False := by
  intro G _ _ _ hnonab hKP hcat q₀ hq₀ hq5 v K N c hdatum hTypK
  have hKg : ∀ u : G, orderOf u = 2 →
      SectionRank.IsKGroupCat ↥(centralizer ({u} : Set G)) :=
    fun u hu => CFSG.ComponentClassification.GSThmB.isKGroupCat_of_ne_top' hKP
      (Helpers.centralizer_ne_top_of_involution G hnonab u hu)
  obtain ⟨w, J, N', hJd, hwJ, hTypJ⟩ :=
    hI.dPrime TypU q₀ hq₀ hq5 (verticalCentral_typU hI) coreInvariant_typU
      (diagonalTransfer_typU hI.griess hI.schur q₀) G hKg v K N c hdatum hTypK
  obtain ⟨hw, hJw, hJc, hN'J, -, hN'SL, -, hwN', -, hwZ⟩ := hJd
  have hJ : HarrisLit.IsTwoComponentIn J (centralizer ({w} : Set G)) :=
    (HarrisLit.isTwoComponentIn_iff hJw).mpr hJc
  have hSLJ : HarrisLit.IsSLTwoOver q₀
      (↥(N'.subgroupOf J) ⧸ pPrimeCore 2 ↥(N'.subgroupOf J)) :=
    CFSG.ComponentClassification.GSThmB.HConfig.isSLTwoOver_of_mulEquiv
      (subgroupOfEquivOfLe hN'J).symm hN'SL
  have hcZ : (⟨w, hwJ⟩ : ↥J) ∈ Open.fusionZStar ↥J := by
    obtain ⟨k, hk, hkw⟩ := hwZ
    have : k = ⟨w, hwJ⟩ := Subtype.ext hkw
    rwa [← this]
  have hcw2 : orderOf (⟨w, hwJ⟩ : ↥J) = 2 := by rw [Subgroup.orderOf_mk]; exact hw
  have hcwN : (⟨w, hwJ⟩ : ↥J) ∈ N'.subgroupOf J := mem_subgroupOf.mpr hwN'
  rcases hTypJ with ⟨q, hqodd, hq9, hSL⟩ | ⟨r, hr, hr2, hChev⟩ | hpsp | ⟨n, hn7, hDC⟩
  ·
    obtain ⟨p, k, hp, hkpos, hpk⟩ :=
      (isPrimePow_nat_iff q).mp (isPrimePow_of_isSLTwoOver hSL)
    have hqpk : Odd (p ^ k) := by rw [hpk]; exact hqodd
    have hpodd : Odd p := (Nat.odd_pow_iff hkpos.ne').mp hqpk
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hpodd
      omega
    have hSL' : HarrisLit.IsSLTwoOver (p ^ k) (↥J ⧸ pPrimeCore 2 ↥J) := by
      rw [hpk]; exact hSL
    exact hI.noSL2 G hnonab hcat hw hJ hwJ hp hp2 hSL'
  ·
    have hM := hI.p4 ↥J hJ.2.2 r hr hr2 hChev.1 (N'.subgroupOf J) q₀ hq₀ hq5 hSLJ
      ⟨w, hwJ⟩ hcw2 hcwN hcZ
    exact HarrisLit.not_isMTypeSchur_of_kProper
      (HarrisLit.harris82Theorem1KProper_of_simpleKProperOdd hI.harris)
      hnonab hKP hcat hw hJ hwJ hr hr2 hM
  ·
    have hchev : HarrisLit.IsSimpleChevalleyOver 3 (↥J ⧸ Open.fusionZStar ↥J) :=
      ⟨.PSp, 2, 1, hpsp⟩
    have hM := hI.p4 ↥J hJ.2.2 3 (by norm_num) (by norm_num) hchev (N'.subgroupOf J) q₀
      hq₀ hq5 hSLJ ⟨w, hwJ⟩ hcw2 hcwN hcZ
    exact HarrisLit.not_isMTypeSchur_of_kProper
      (HarrisLit.harris82Theorem1KProper_of_simpleKProperOdd hI.harris)
      hnonab hKP hcat hw hJ hwJ (by norm_num) (by norm_num) hM
  ·
    by_cases hn : n = 7
    ·
      subst n
      obtain ⟨τ, m, p, f, -, -, -, hm⟩ :=
        hI.classical G hnonab hw hJw hJc hwJ (hA7 ↥J hDC)
      exact hcat (Blueprint.lieModel_catalog G τ m p f hm)
    ·
      have hn8 : 8 ≤ n := by omega
      have hperf : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) := hDC.1.1
      have hcard : Nat.card (center (↥J ⧸ pPrimeCore 2 ↥J)) = 2 := hDC.2.1
      obtain ⟨ealt⟩ := hDC.2.2
      rcases hI.solomon G w hw J n hn8 hJw hJc hwJ hperf hcard ⟨ealt⟩ with
        hMcL | hLy
      · obtain ⟨eMcL⟩ := hMcL
        exact hcat (.inr (.inr (.inr (.inr ⟨.McL, ⟨eMcL⟩⟩))))
      · obtain ⟨eLy⟩ := hLy
        exact hcat (.inr (.inr (.inr (.inr ⟨.Ly, ⟨eLy⟩⟩))))

end CFSG.OddStandard.SmallF3.HypA2
