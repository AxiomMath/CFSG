module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Dich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf5Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Distinct





section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secImg_ne_of_twin (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J J' : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hJ' : J' ∈ tqMembers3 Ω c) (hne : J ≠ J')
    {t : G} (ht : IsUniqueInvolution J t) (ht' : IsUniqueInvolution J' t) :
    secImg Ω c J ≠ secImg Ω c J' := by
  intro heq
  have hΛ : HypOmegaGen (restrictFamily (TwinADescent.coreFamily Ω c) (Subgroup.centralizer ({c} : Set G))) :=
    TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hcore_ne : (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≠
      (TwinADescent.coreAt c J').subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
    intro he
    have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set G)).subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J')] at this
    exact hne (eq_of_coreAt_eq hΩ hc2 hJ hJ' this)
  exact TwinExitPf2.false_of_imgOf_eq hΛ
    (subgroupOf_mem_restrictFamily (TwinADescent.coreAt_mem_coreFamily hJ)
      (TwinADescent.coreAt_le_centralizer c J))
    (subgroupOf_mem_restrictFamily (TwinADescent.coreAt_mem_coreFamily hJ')
      (TwinADescent.coreAt_le_centralizer c J'))
    hcore_ne
    (isUniqueInvolution_subgroupOf (isUniqueInvolution_coreAt_of_tq hΩ hc2 hJ ht)
      (TwinADescent.coreAt_le_centralizer c J))
    (isUniqueInvolution_subgroupOf (isUniqueInvolution_coreAt_of_tq hΩ hc2 hJ' ht')
      (TwinADescent.coreAt_le_centralizer c J'))
    (le_coreHull hJ) (le_coreHull hJ') heq

end Gen

section Std

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem v3_secImg_ne (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄) :
    secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
  have hd := hStd.datum
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  exact secImg_ne_of_twin hd.hyp hc2 hmem hmem4 (Ne.symm hF.2.2.2.1) hd.hzK₃
    (isUniqueInvolution_of_mem_twinSet hd.hz hF.1)

end Std

end Distinct

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
