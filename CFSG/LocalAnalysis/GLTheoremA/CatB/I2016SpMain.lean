module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpCase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsSp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpGap

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.CatB CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8
  CFSG.LocalAnalysis.GLTheoremA.I2016 CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts

theorem noT_sp8 (hGap : FpfIrrGap) [IsSimpleGroup (StatedSp 4 (ZMod 2))]
    {g : StatedSp 4 (ZMod 2)} (hg3 : g ^ 3 = 1)
    {I A T : Subgroup (StatedSp 4 (ZMod 2))}
    (hI : CFSG.Open.IsSubnormal I (Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2)))))
    (hq : QuotU4 I) (hA : A ≤ Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))))
    (hA6 : HasA6Quot A) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTg : ∀ t ∈ T, g⁻¹ * t * g ∈ T)
    (hAT : A ≤ Subgroup.normalizer (T : Set (StatedSp 4 (ZMod 2)))) : False := by
  by_cases hg1 : g = 1
  · subst hg1
    have htop : Subgroup.centralizer ({(1 : StatedSp 4 (ZMod 2))} : Set (StatedSp 4 (ZMod 2))) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [htop] at hI
    rcases CFSG.Open.IsSubnormal.eq_bot_or_top hI with rfl | rfl
    · have h1 := quotU4_le hq
      rw [Subgroup.card_bot] at h1
      omega
    · obtain ⟨N, hN, hcard⟩ := quotU4_kernel hq
      haveI : IsSimpleGroup ↥(⊤ : Subgroup (StatedSp 4 (ZMod 2))) :=
        Subgroup.topEquiv.isSimpleGroup
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
      · rw [Subgroup.card_bot, Subgroup.card_top] at hcard
        have hdvd := Nat.ordProj_dvd (Nat.card (StatedSp 4 (ZMod 2))) 3
        rw [card3_sp82] at hdvd
        rw [show Nat.card (StatedSp 4 (ZMod 2)) = 25920 by omega] at hdvd
        norm_num at hdvd
      · simp only [Subgroup.card_top] at hcard
        have hpos : 0 < Nat.card (StatedSp 4 (ZMod 2)) := Nat.card_pos
        omega
  · obtain ⟨A₀, A₁, hC⟩ := sp8Class_m4_of_quotU4 hg3 hg1 hI hq
    exact noT_of_fpf hGap hg3 hg1 hC hA hA6 hT1 hT2 hTg hAT

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
