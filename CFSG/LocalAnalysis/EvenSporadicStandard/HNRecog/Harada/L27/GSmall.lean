module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.Data
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

@[expose] def SmallSimpleLookup : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], CFSG.Blueprint.Catalog T →
    (∃ a b : T, a * b ≠ b * a) → Nat.card T ∣ 348364800 → Nat.card T ≤ 16200 →
      Nat.card T ∈ smallSimpleOrders

theorem smallSections_of_kGroup {X : Type} [Group X] [Finite X]
    (hX : CFSG.SectionRank.IsKGroupCat X)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog)
    (hL : SmallSimpleLookup) (hdvd : Nat.card X ∣ 348364800) (hle : Nat.card X ≤ 16200) :
    SmallSections X := by
  intro K L hLnorm hsimple hnonab
  haveI : L.Normal := hLnorm
  haveI : IsSimpleGroup (K ⧸ L) := hsimple
  have hCat : CFSG.Blueprint.Catalog (K ⧸ L) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hX K (QuotientGroup.mk' L)
      (QuotientGroup.mk'_surjective L)
  have hdvdQ : Nat.card (K ⧸ L) ∣ Nat.card X :=
    (Subgroup.card_quotient_dvd_card L).trans (Subgroup.card_subgroup_dvd_card K)
  refine ⟨hL (K ⧸ L) hCat hnonab (hdvdQ.trans hdvd)
    (le_trans (Nat.le_of_dvd Nat.card_pos hdvdQ) hle), hS (K ⧸ L) hnonab hCat⟩

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem Ngrp_ne_top [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : Setting25 G t z z₁ ι zv R0 F) : Ngrp h ≠ ⊤ := by
  intro hN
  have hnorm : (Rgrp h).Normal := Subgroup.normalizer_eq_top_iff.mp hN
  haveI : (Rgrp h).Normal := hnorm
  rcases Subgroup.Normal.eq_bot_or_eq_top (Rgrp h) with hbot | htop
  · exact h.z_ne_one (Subgroup.mem_bot.mp (hbot ▸ z_mem_Rgrp h))
  · have hcard : Nat.card G = 2 ^ 9 := by
      rw [← Subgroup.card_top (G := G), ← htop]
      exact card_Rgrp h
    have hpG : IsPGroup 2 G := IsPGroup.of_card hcard
    haveI : Group.IsNilpotent G := hpG.isNilpotent
    have hsolv : Group.IsSolvable G := inferInstance
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv a b)

theorem isKGroupCat_Xgrp [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (h : Setting25 G t z z₁ ι zv R0 F) : CFSG.SectionRank.IsKGroupCat ↥(Xgrp h) := by
  have hAll : CFSG.KCore.KProperAllSimple CFSG.Blueprint.Catalog G :=
    CFSG.KCore.KProperNonab.kProperAllSimple CFSG.SectionRank.catalog_isoInvariant
      CFSG.SectionRank.catalog_containsAbelianSimple hKP
  have hN : CFSG.SectionRank.IsKGroupCat ↥(Ngrp h) := hAll (Ngrp h) (Ngrp_ne_top hnonab h)
  exact CFSG.SectionRank.IsKGroupCat.of_surjective hN (rho0 h).rangeRestrict
    (rho0 h).rangeRestrict_surjective

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
