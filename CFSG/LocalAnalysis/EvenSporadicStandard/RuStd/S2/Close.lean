module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseKernel
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseU43
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseA
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseB

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

namespace ProdSplit

variable {G : Type*} [Group G] {N A B : Subgroup G}

theorem eq_one_of_central (h : ProdSplit N A B) {x : G} (hx : x ∈ N)
    (hc : ∀ n ∈ N, x * n = n * x) : x = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.prod x hx
  have h1 : a = 1 := by
    refine h.isA.nonabSimple.center_eq_one a ha fun y hy => ?_
    have h2 : a * y * b = y * a * b :=
      calc a * y * b = a * (y * b) := mul_assoc _ _ _
        _ = a * (b * y) := by rw [h.comm y hy b hb]
        _ = a * b * y := (mul_assoc _ _ _).symm
        _ = y * (a * b) := hc y (h.le_A hy)
        _ = y * a * b := (mul_assoc _ _ _).symm
    exact mul_right_cancel h2
  have h3 : b = 1 := by
    refine h.isB.nonabSimple.center_eq_one b hb fun y hy => ?_
    have h2 : a * (b * y) = a * (y * b) :=
      calc a * (b * y) = a * b * y := (mul_assoc _ _ _).symm
        _ = y * (a * b) := hc y (h.le_B hy)
        _ = y * a * b := (mul_assoc _ _ _).symm
        _ = a * y * b := by rw [(h.comm a ha y hy).symm]
        _ = a * (y * b) := mul_assoc _ _ _
    exact mul_left_cancel h2
  rw [h1, h3, one_mul]

end ProdSplit

variable {X : Type} [Group X] [Finite X]

theorem false_of_prod (d : ThreeLocalData X) (kd : KernelData d) (hM10 : Nat.card M10 = 720)
    {N A B : Subgroup (X ⧸ CFSG.oddCore X)} (hN : N.Normal) (hP : ProdSplit N A B)
    (hC : ∀ x : X ⧸ CFSG.oddCore X, (∀ n ∈ N, x * n = n * x) → x = 1)
    (hodd : ∀ g : X ⧸ CFSG.oddCore X, Odd (orderOf g) → g ∈ N) : False := by
  have hKt : kd.Kt.Normal := kd.Kt_normal
  have hMn : ∀ n ∈ N, ∀ m ∈ kd.Kt ⊓ N, n * m * n⁻¹ ∈ kd.Kt ⊓ N := fun n hn m hm =>
    ⟨hKt.conj_mem m hm.1 n, N.mul_mem (N.mul_mem hn hm.2) (N.inv_mem hn)⟩
  have hMN : kd.Kt ⊓ N ≤ N := inf_le_right
  have hMne : kd.Kt ⊓ N ≠ ⊥ := kd.inf_ne_bot hN hC
  have hdich : ∀ A' B' : Subgroup (X ⧸ CFSG.oddCore X), ProdSplit N A' B' →
      (kd.Kt ⊓ N) ⊓ A' = ⊥ ∨ (kd.Kt ⊓ N) ⊓ A' = A' := fun A' B' hP' =>
    hP'.isA.nonabSimple.eq_bot_or_eq_self _ inf_le_right fun a ha s hs =>
      ⟨hMn a (hP'.le_A ha) s hs.1, A'.mul_mem (A'.mul_mem ha hs.2) (A'.inv_mem ha)⟩
  have caseA : ∀ A' B' : Subgroup (X ⧸ CFSG.oddCore X), ProdSplit N A' B' →
      (kd.Kt ⊓ N) ⊓ A' = A' → (kd.Kt ⊓ N) ⊓ B' = ⊥ → False := by
    intro A' B' hP' hA hB
    have hAM : A' ≤ kd.Kt ⊓ N := (le_of_eq hA.symm).trans inf_le_left
    have hMA : kd.Kt ⊓ N = A' := hP'.eq_of_le_of_inf_eq_bot hMN hAM hB
    have hAn : A'.Normal := by
      rw [← hMA]
      have := hN
      exact inferInstance
    have hBn : B'.Normal := ⟨fun b hb g =>
      hP'.conj_mem_other (fun g n hn => hN.conj_mem n hn g) (fun g a ha => hAn.conj_mem a ha g)
        g b hb⟩
    refine false_of_case_a d kd hM10 hAn hBn hP'.comm hP'.isA.nonabSimple.perfect
      (by rw [hP'.isA.card]; norm_num) hP'.isB.card (hMA ▸ inf_le_left) ?_
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ (kd.Kt ⊓ N) ⊓ B' := ⟨⟨hx.2, hP'.le_B hx.1⟩, hx.1⟩
    rw [hB] at hx'
    exact hx'
  rcases hdich A B hP with hA | hA <;> rcases hdich B A hP.swap with hB | hB
  · apply hMne
    refine eq_bot_iff.2 fun m hm => ?_
    exact Subgroup.mem_bot.2 (hC m (hP.eq_bot_of_inf_eq_bot hMN hMn hA hB m hm))
  · exact caseA B A hP.swap hB hA
  · exact caseA A B hP hA hB
  · have hAM : A ≤ kd.Kt ⊓ N := (le_of_eq hA.symm).trans inf_le_left
    have hBM : B ≤ kd.Kt ⊓ N := (le_of_eq hB.symm).trans inf_le_left
    have hNK : N ≤ kd.Kt := (hP.le_of_le hAM hBM).trans inf_le_left
    have hf5 : (QuotientGroup.mk d.f : X ⧸ CFSG.oddCore X) ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have := pow_orderOf_eq_one d.f
      rw [d.f_ord] at this
      rw [this, QuotientGroup.mk_one]
    have hfodd : Odd (orderOf (QuotientGroup.mk d.f : X ⧸ CFSG.oddCore X)) :=
      Odd.of_dvd_nat (by decide : Odd 5) (orderOf_dvd_of_pow_eq_one hf5)
    exact false_of_case_b d kd hP hNK (hodd _ hfodd)

end CFSG.EvenSporadicStandard.RuStd.S2.Close

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

theorem closing_core
    (hGH1 : GHLemma53_1) (hOut : OutU43TwoGroup)
    (hM10 : Nat.card M10 = 720) {X : Type} [Group X] [Finite X]
    (hKX : CFSG.SectionRank.IsKGroupCat X) (d : ThreeLocalData X) : False := by
  obtain ⟨K, hKn, hOK, hcm, hKK⟩ := Close.exists_kernel d
  let kd : Close.KernelData d := ⟨K, hKn, hOK, hcm, hKK⟩
  have hdisj := hGH1 (X ⧸ CFSG.oddCore X) (hKX.quotient _) (Close.oddCore_quotient_eq_bot X) _
    (Close.orderOf_mk_oddCore_eq_two d.t_ord) d.t_noncentral d.cen_iso
  have hN : (fStar (X ⧸ CFSG.oddCore X)).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal _
  have hcen : ∀ x : X ⧸ CFSG.oddCore X, (∀ n ∈ fStar (X ⧸ CFSG.oddCore X), x * n = n * x) →
      x ∈ fStar (X ⧸ CFSG.oddCore X) := fun x hx =>
    CFSG.ComponentClassification.GeneralizedFitting.centralizer_le _
      (Subgroup.mem_centralizer_iff.2 fun n hn => (hx n hn).symm)
  rcases hdisj with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hNS := Close.u43_nonabSimple e
    have hC : ∀ x : X ⧸ CFSG.oddCore X, (∀ n ∈ fStar (X ⧸ CFSG.oddCore X), x * n = n * x) →
        x = 1 := fun x hx => hNS.center_eq_one x (hcen x hx) hx
    exact Close.false_of_u43 d kd hN e hC
      fun g hg => Close.mem_of_odd_orderOf_u43 hOut e hC hg
  · obtain ⟨A, B, hP⟩ := Close.exists_prodSplit e
    have hC : ∀ x : X ⧸ CFSG.oddCore X, (∀ n ∈ fStar (X ⧸ CFSG.oddCore X), x * n = n * x) →
        x = 1 := fun x hx => hP.eq_one_of_central (hcen x hx) hx
    exact Close.false_of_prod d kd hM10 hN hP hC
      fun g hg => Close.mem_of_odd_orderOf_prod hP hC hg

theorem closing_abstract
    (hGH1 : GHLemma53_1) (hOut : OutU43TwoGroup)
    (hM10 : Nat.card M10 = 720) {X : Type} [Group X] [Finite X]
    (hKX : CFSG.SectionRank.IsKGroupCat X) (d : ThreeLocalData X) : False :=
  closing_core hGH1 hOut hM10 hKX d

end CFSG.EvenSporadicStandard.RuStd.S2
