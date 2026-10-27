module

public import CFSG.Timmesfeld.Bridge.Asc72NoPolar
public import CFSG.CGT.T75I.BenderInput

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.CGT.Timmesfeld75


theorem aschbacherDisconnectedInput_of_repo : AschbacherDisconnectedInput := by
  intro G _ _ D hcls hord hgen hrad hdisc hclosed hcomm
  have hN : IsNormalSet D := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro g x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    refine isConj_iff.2 ⟨g * c, ?_⟩
    rw [← hc]
    group
  have hsq : ∀ d ∈ D, d * d = 1 := fun d hd => by
    have h := pow_orderOf_eq_one d
    rwa [hord d hd, pow_two] at h
  have hnp : Moufang.NoPolar D := fun x hx y hy hxy hne => hclosed x hx y hy hxy.eq hne
  have hdisc' : Disconnected D := by
    obtain ⟨x, hx, y, hy, h⟩ := hdisc
    exact ⟨x, hx, y, hy, fun hh => h hh⟩
  obtain ⟨x, hx, -⟩ := id hdisc'
  have hSE := (fusionStronglyEmbedded_iff _).2
    (asc73For_of CFSG.ShultStronglyClosedTI.theoremTwo schurNarrowInput G D hN hord hgen hnp hdisc'
      x hx)
  obtain ⟨u, hu, v, hv, huv, hc⟩ := hcomm
  have hns : ¬ Group.IsSolvable G := by
    intro hsol
    have htop : (⊤ : Subgroup G) = ⊥ :=
      hrad ⊤ inferInstance (Group.isSolvable_of_isSolvable_injective
        (f := (⊤ : Subgroup G).subtype) Subtype.val_injective)
    have h1 : u = 1 := Subgroup.mem_bot.1 (htop ▸ Subgroup.mem_top u)
    have h2 := hord u hu
    rw [h1, orderOf_one] at h2
    omega
  rcases bender_strongly_embedded_normal_series G _ hSE with
    hSyl | ⟨M, N, hM, hNn, hMN, -, hMo, hNo, hB⟩
  · exfalso
    have hNC := noCommutingDistinctInvolutions_of_sylow hSyl
    have heq := hNC ⟨u, hord u hu⟩ ⟨v, hord v hv⟩ hc
    exact huv (congrArg Subtype.val heq)
  · have hM1 : M = ⊥ := hrad M hM (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hMo)
    have hDN : D ⊆ N := fun d hd => mem_of_odd_index hNo (hsq d hd)
    have hNtop : N = ⊤ := eq_top_iff.2 (hgen ▸ (Subgroup.closure_le N).2 hDN)
    have hsub : M.subgroupOf N = ⊥ := by
      rw [hM1, Subgroup.bot_subgroupOf]
    let e₁ : G ≃* N := (Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr hNtop.symm)
    let e₂ : N ≃* N ⧸ M.subgroupOf N :=
      (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hsub.symm)
    exact isBenderGroup_of_mulEquiv (e₁.trans e₂) (isBenderGroup_of_fusionIsBenderGroup hB)

end CFSG.CGT.T75I
