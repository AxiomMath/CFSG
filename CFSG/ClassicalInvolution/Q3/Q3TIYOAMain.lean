module

public import CFSG.ClassicalInvolution.Q3.Q3TIYOALie
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAGrp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups

section Statement


end Statement

section Main


theorem oddAutLayerRigid3 :
    ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClass3 Λ → LieSystemMod3 Λ →
      classicalInvolutionOddCore Y = ⊥ →
      ∀ (K : Subgroup Y) (z : Y), K ∈ Λ → IsClassicalMember3 K z →
        ∀ α : MulAut Y, Odd (orderOf α) → (∀ c : Y, c * z = z * c → α c = c) → α = 1 := by
  intro Y _ _ Λ hΛ hLie hO K z hK hKz α hodd hfix
  obtain ⟨ι, hι, ⟨D⟩⟩ := lieSystem3_of_lieSystemMod3_corefree hO hLie
  obtain ⟨j, R, hR, hKR⟩ := D.fundamental K hK
  subst hKR
  have hzK : z ∈ (D.hom j).range := Subgroup.map_le_range _ _ hKz.mem
  have hFix : ∀ i, i ≠ j → ∀ y ∈ (D.hom i).range, α y = y := by
    intro i hij y hy
    apply hfix
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨w, hw⟩ := hzK
    rw [← hw]
    exact D.commute i j hij x w
  have hQ : ∀ q ∈ (D.hom j).range, α q = q := by
    by_cases hA1 : IsA1Comp3 D j
    ·
      have hRtop : R = ⊤ := eq_top_of_mem_fund_sl23 hA1 hR
      have hKC : R.map (D.hom j) ≤ Subgroup.centralizer ({z} : Set Y) :=
        isSubnormal_le hKz.subnormal
      intro q hq
      rw [← Subgroup.map_top, ← hRtop] at hq
      exact hfix q (Subgroup.mem_centralizer_singleton_iff.mp (hKC hq))
    ·
      have hq : CFSG.Open.IsQuasisimple (D.kind j).G := isQuasisimple_of_not_a1 D hA1
      have hfc : ∀ R ∈ (D.kind j).fund, ∀ g : (D.kind j).G, conjSub g R ∈ (D.kind j).fund := by
        rcases kind_cases_of_not_a1 D hA1 with ⟨t, n, -, -, hk⟩ | hk
        · exact fun R hR g => conjSub_mem_fund_of_not_a1 (Or.inl ⟨t, n, hk⟩) hR g
        · exact fun R hR g => conjSub_mem_fund_of_not_a1 (Or.inr hk) hR g
      set Q : Subgroup Y := (D.hom j).range with hQdef
      have : Q.Normal := range_normal3 D j
      have hQq : CFSG.Open.IsQuasisimple Q := isQuasisimple_range3 D j hq
      set A : Subgroup Y := ⨆ i, ⨆ (_ : i ≠ j), (D.hom i).range with hAdef
      have hAfix : ∀ a ∈ A, α a = a := by
        intro a ha
        have hle : A ≤ MonoidHom.eqLocus (α : Y →* Y) (MonoidHom.id Y) :=
          iSup_le fun i => iSup_le fun hij y hy => hFix i hij y hy
        exact hle ha
      have hAc : A ≤ Subgroup.centralizer (Q : Set Y) := by
        refine iSup_le fun i => iSup_le fun hij y hy => ?_
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨w, rfl⟩
        obtain ⟨x, rfl⟩ := hy
        exact D.commute j i (Ne.symm hij) w x
      have hQA : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q := fun q hq a ha =>
        Subgroup.mem_centralizer_iff.mp (hAc ha) q hq
      have hgen : Q ⊔ A = ⊤ := by
        rw [eq_top_iff, ← D.generate]
        refine iSup_le fun i => ?_
        by_cases hij : i = j
        · rw [hij]
          exact le_sup_left
        · exact le_sup_of_le_right (le_iSup_of_le i (le_iSup_of_le hij le_rfl))
      have hperf : ⁅Q, Q⁆ = Q := commutator_subgroup_eq_self hQq.1
      have hαQ : ∀ q ∈ Q, α q ∈ Q := apply_mem_of_perfect_of_fixed hQA hgen hperf α hAfix
      have hαm : α ^ orderOf α = 1 := pow_orderOf_eq_one α
      have hβm : restrictAut Q α hαQ ^ orderOf α = 1 := restrictAut_pow_eq_one Q α hαQ hαm
      have hβfix : ∀ c : Q, c * (⟨z, hzK⟩ : Q) = ⟨z, hzK⟩ * c → restrictAut Q α hαQ c = c := by
        intro c hc
        apply Subtype.ext
        exact hfix (c : Y) (congrArg Subtype.val hc)
      have hXq : CFSG.Open.IsQuasisimple (Q ⧸ Subgroup.center Q) :=
        CFSG.ComponentClassification.Quasisimple.central_quotient hQq (Subgroup.center Q) le_rfl
      have hXZ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ :=
        Q3NM.center_quotient_center_eq_bot_of_isQuasisimple hQq
      obtain ⟨Λ', K', hΛ', hLie', hK'Λ', hcl'⟩ :=
        exists_centerQuotient_system D j hq hfc hR hK hKz hzK
      have hoddX : Odd (orderOf (centerQuotAut (restrictAut Q α hαQ))) :=
        Odd.of_dvd_nat hodd
          (orderOf_dvd_of_pow_eq_one (centerQuotAut_pow_eq_one _ hβm))
      have hhyp : ∀ c ∈ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center Q) ⟨z, hzK⟩} : Set (Q ⧸ Subgroup.center Q)),
          c⁻¹ * centerQuotAut (restrictAut Q α hαQ) c ∈ Balance.oddCoreIn
            (Subgroup.centralizer
              ({QuotientGroup.mk' (Subgroup.center Q) ⟨z, hzK⟩} :
                Set (Q ⧸ Subgroup.center Q))) := by
        intro c hc
        obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
        exact cocycle_mem_oddCoreIn (restrictAut Q α hαQ) hodd hβm hβfix c' hc
      have hrigid : centerQuotAut (restrictAut Q α hαQ) = 1 :=
        Q3T.modelOddAutRigid_proved (Q ⧸ Subgroup.center Q) hXq hXZ Λ' hΛ' hLie'
          (QuotientGroup.mk' (Subgroup.center Q) ⟨z, hzK⟩) K' hK'Λ' hcl'
          (centerQuotAut (restrictAut Q α hαQ)) hoddX hhyp
      have hβ1 : restrictAut Q α hαQ = 1 := by
        refine eq_one_of_perfect_of_central_ratio hQq.1 _ fun q => ?_
        have h1 : centerQuotAut (restrictAut Q α hαQ) (QuotientGroup.mk' (Subgroup.center Q) q) =
            QuotientGroup.mk' (Subgroup.center Q) q := by
          rw [hrigid]
          rfl
        rw [centerQuotAut_mk] at h1
        have h2 : QuotientGroup.mk' (Subgroup.center Q) (q⁻¹ * restrictAut Q α hαQ q) = 1 := by
          rw [map_mul, map_inv, h1, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h2
      intro q hq'
      have h3 : restrictAut Q α hαQ ⟨q, hq'⟩ = ⟨q, hq'⟩ := by
        rw [hβ1]
        rfl
      exact congrArg Subtype.val h3
  have hall : ∀ y : Y, α y = y := by
    have hle : (⨆ i, (D.hom i).range : Subgroup Y) ≤
        MonoidHom.eqLocus (α : Y →* Y) (MonoidHom.id Y) := by
      refine iSup_le fun i => ?_
      by_cases hij : i = j
      · rw [hij]
        exact fun y hy => hQ y hy
      · exact fun y hy => hFix i hij y hy
    intro y
    have hy : y ∈ (⨆ i, (D.hom i).range : Subgroup Y) := by
      rw [D.generate]
      trivial
    exact hle hy
  ext y
  exact hall y

end Main

end CFSG.ClassicalInvolution.Q3.Q3TIY
