module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Numerics
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.Sporadic.Recognition.LyonsSims CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.HardMathSupport.Solomon.Coordinator

section


theorem ly_noL3Comp {S : Type} [Group S] [Finite S] (eT : S ≃* NativeSporadic.Carrier .Ly)
    {s : S} (hs : orderOf s = 3) : NoL3Comp (Subgroup.centralizer ({s} : Set S)) := by
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly ⟨eT⟩)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hord := LyCore.lyThreeBOrder_thm S ⟨eT⟩ t ρ D x₁ x₂ x₃ St
  rcases (lemma45_classes_of_certificate D St).1 s hs with hc | hc
  · refine noL3Comp_centralizer_of_isConj hc.symm ?_
    have hx3 : orderOf (x₁ : S) = 3 := by
      obtain ⟨c, hcx⟩ := isConj_iff.1 hc
      rw [← hs, ← hcx]
      exact MulEquiv.orderOf_eq (MulAut.conj c) s
    have hperf := D.isPerfect_centralizer St
    have hcen := D.center_centralizer St
    have hc3 := D.card_center_centralizer St
    obtain ⟨eM⟩ := D.centQuot_mcl St.pow₁ St.rho₁
    have e : ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) ≃* NativeSporadic.McL :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans eM
    have hsimple : IsSimpleGroup (↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({(x₁ : S)} : Set S))) :=
      @MulEquiv.isSimpleGroup _ _ NativeSporadic.McL _ CFSG.Sporadic.McL.isSimpleGroup_McL e
    have hcard : Nat.card ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)) = 2694384000 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(Subgroup.centralizer ({(x₁ : S)} : Set S)))
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, hc3] at h1
      omega
    exact noL3Comp_of_quasisimple ⟨hperf.commutator_eq_top, hsimple⟩
      (oPrimeCoreTrivialAt_Ly_three S ⟨eT⟩ (x₁ : S) hx3)
      (by rw [hcard]; exact noL3Eq_2694384000)
  · refine noL3Comp_centralizer_of_isConj hc.symm (noL3Comp_of_noDvd ?_)
    have hQC : QE (x₁ : S) (x₂ : S) ≤
        Subgroup.centralizer ({(x₁ : S) * (x₂ : S)} : Set S) := by
      intro g hg
      rw [mem_QE] at hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * ((x₁ : S) * (x₂ : S)) = (g * (x₁ : S)) * (x₂ : S) := by group
        _ = ((x₁ : S) * g) * (x₂ : S) := by rw [hg.1]
        _ = (x₁ : S) * (g * (x₂ : S)) := by group
        _ = (x₁ : S) * ((x₂ : S) * g) := by rw [hg.2]
        _ = (x₁ : S) * (x₂ : S) * g := by group
    have hQc : Nat.card ↥(QE (x₁ : S) (x₂ : S)) = 87480 := D.card_QE St
    have hdvd : 87480 ∣ Nat.card ↥(Subgroup.centralizer ({(x₁ : S) * (x₂ : S)} : Set S)) :=
      hQc ▸ Subgroup.card_dvd_of_le hQC
    obtain ⟨k, hk⟩ := hdvd
    have hpos := Nat.card_pos (α := ↥(Subgroup.centralizer ({(x₁ : S) * (x₂ : S)} : Set S)))
    have hk2 : k ≤ 2 := by omega
    have hk0 : 0 < k := by omega
    interval_cases k
    · rw [hk]; exact noL3Dvd_87480
    · rw [hk]; exact noL3Dvd_174960

theorem sporL3DownInner_Ly (hbr : SporadicBridges) : SporL3DownInner .Ly := by
  haveI : Finite (NativeSporadic.Carrier .Ly) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.Ly ≠ 0
      rw [CFSG.Sporadic.Ly.card_Ly]
      norm_num)
  refine sporL3DownInner_of_comp (NativeSporadic.Carrier .Ly) (hbr .Ly) ?_ ?_
  · show NoL3Eq (Nat.card NativeSporadic.Ly)
    rw [CFSG.Sporadic.Ly.card_Ly]
    exact noL3Eq_51765179004000000
  · intro x hx
    exact ly_noL3Comp (MulEquiv.refl _) hx

end

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
