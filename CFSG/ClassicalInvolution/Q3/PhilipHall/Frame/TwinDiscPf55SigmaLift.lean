module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf54SecConn

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc


section FixLift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem exists_fixed_lift_coreHull (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    {c : G} (hcu : c ∈ Subgroup.centralizer ({u} : Set G)) (hcc : c * c = 1)
    {q : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)}
    (hq : secAct hΩ hc2 ⟨c, hcu⟩ q = q) :
    ∃ g : ↥(coreHull Ω u),
      (g : ↥(Subgroup.centralizer ({u} : Set G))) * ⟨c, hcu⟩ =
        ⟨c, hcu⟩ * (g : ↥(Subgroup.centralizer ({u} : Set G))) ∧
      (QuotientGroup.mk g : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) = q := by
  haveI := TwinPerpV3.Pf93.normal_coreHull hΩ hc2
  have hg₀2 : (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) * ⟨c, hcu⟩ = 1 :=
    Subtype.ext hcc
  have hinv : (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G)))⁻¹ = ⟨c, hcu⟩ :=
    inv_eq_of_mul_eq_one_right hg₀2
  have hσσ' : ∀ y : ↥(coreHull Ω u),
      (MulAut.conjNormal (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) :
        MulAut ↥(coreHull Ω u))
        ((MulAut.conjNormal (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) :
          MulAut ↥(coreHull Ω u)) y) = y := by
    intro y
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, hinv]
    calc (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) *
          (⟨c, hcu⟩ * (y : ↥(Subgroup.centralizer ({u} : Set G))) * ⟨c, hcu⟩) * ⟨c, hcu⟩
        = ((⟨c, hcu⟩ * ⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) *
            (y : ↥(Subgroup.centralizer ({u} : Set G)))) * (⟨c, hcu⟩ * ⟨c, hcu⟩) := by group
      _ = (y : ↥(Subgroup.centralizer ({u} : Set G))) := by rw [hg₀2]; group
  have hσσ : (MulAut.conjNormal (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) :
      MulAut ↥(coreHull Ω u)) * MulAut.conjNormal ⟨c, hcu⟩ = 1 := MulEquiv.ext hσσ'
  have hσN : (classicalInvolutionOddCore ↥(coreHull Ω u)).map
      ((MulAut.conjNormal (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) :
        MulAut ↥(coreHull Ω u)) : ↥(coreHull Ω u) →* ↥(coreHull Ω u)) =
      classicalInvolutionOddCore ↥(coreHull Ω u) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  have hq' : q ∈ Q3NM.fixedSubgroup (Q3NM.quotAut (classicalInvolutionOddCore ↥(coreHull Ω u))
      (MulAut.conjNormal (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G)))) hσN) := by
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective q
    rw [← hy] at hq ⊢
    show Q3NM.quotAut _ _ hσN (QuotientGroup.mk y) = QuotientGroup.mk y
    rw [Q3NM.quotAut_mk]
    rw [secAct_mk] at hq
    exact hq
  obtain ⟨y, hy, hyq⟩ := Q3NM.exists_fixed_lift (classicalInvolutionOddCore ↥(coreHull Ω u))
    (CFSG.ComponentClassification.OddCore.odd_card _) _ hσσ hσN hq'
  refine ⟨y, ?_, hyq⟩
  have h0 : (MulAut.conjNormal (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) :
      MulAut ↥(coreHull Ω u)) y = y := hy
  have h2 : (((MulAut.conjNormal (⟨c, hcu⟩ : ↥(Subgroup.centralizer ({u} : Set G))) :
      MulAut ↥(coreHull Ω u)) y : ↥(coreHull Ω u)) : ↥(Subgroup.centralizer ({u} : Set G))) =
      ⟨c, hcu⟩ * (y : ↥(Subgroup.centralizer ({u} : Set G))) * ⟨c, hcu⟩⁻¹ := by
    rw [MulAut.conjNormal_apply]
  rw [h0] at h2
  calc (y : ↥(Subgroup.centralizer ({u} : Set G))) * ⟨c, hcu⟩
      = (⟨c, hcu⟩ * (y : ↥(Subgroup.centralizer ({u} : Set G))) * ⟨c, hcu⟩⁻¹) * ⟨c, hcu⟩ := by
        rw [← h2]
    _ = ⟨c, hcu⟩ * (y : ↥(Subgroup.centralizer ({u} : Set G))) := by group

end FixLift


section P5

theorem coreLayer_le_sigmaGen_of_transitive_gen
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {z t u : G}
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K)
    (ht : IsUniqueInvolution J t)
    (hOdd : ∀ m ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G)),
      m ∈ Subgroup.centralizer ({z} : Set G))
    (hzC : z ∈ Subgroup.centralizer ({u} : Set G)) (htC : t ∈ Subgroup.centralizer ({u} : Set G))
    (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u} : Set G))) ∈ coreHull Ω u)
    {tb : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)}
    (htb : tb = QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull Ω u)))
    (hJtq : J ∈ tqMembers3 Ω u)
    (hH : ∀ N ∈ secFam Ω u,
      ∃ g ∈ Subgroup.closure
        ({q | secAct hΩ hc2 ⟨z, hzC⟩ q = q} ∪ {q | tb * q = q * tb}),
        conjSub g (secImg Ω u J) = N) :
    coreLayer Ω u ≤ sigmaGen Ω K := by
  have hJd : J ∈ dComp Ω K := T7A.mem_dComp_of_mem_omegaNbr hJ
  have heq := T7A.dComp_eq_of_mem hK hJd
  have hNz : ∀ g : G, g ∈ Subgroup.centralizer ({z} : Set G) → ∀ M ∈ dComp Ω K,
      conjSub g M ∈ dComp Ω K := fun g hg M hM =>
    conjSub_mem_dComp_of_comm hΩ hK hz (Subgroup.mem_centralizer_singleton_iff.mp hg) hM
  have hNt : ∀ g : G, g ∈ Subgroup.centralizer ({t} : Set G) → ∀ M ∈ dComp Ω K,
      conjSub g M ∈ dComp Ω K := by
    intro g hg M hM
    rw [← heq] at hM ⊢
    exact conjSub_mem_dComp_of_comm hΩ hJ.1 ht (Subgroup.mem_centralizer_singleton_iff.mp hg) hM
  let good : Set (Subgroup (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u))) :=
    {N | ∃ M ∈ tqMembers3 Ω u, M ∈ dComp Ω K ∧ N = secImg Ω u M}
  have hJgood : secImg Ω u J ∈ good := ⟨J, hJtq, hJd, rfl⟩
  have hinvA : ∀ g : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u),
      secAct hΩ hc2 ⟨z, hzC⟩ g = g → ∀ N ∈ good, conjSub g N ∈ good := by
    intro g hg N hN
    obtain ⟨M, hM, hMd, rfl⟩ := hN
    obtain ⟨g', hg'c, hg'⟩ := exists_fixed_lift_coreHull hΩ hc2 hzC hz.sq hg
    have hg'u : (((g' : ↥(Subgroup.centralizer ({u} : Set G))) : G)) ∈
        Subgroup.centralizer ({u} : Set G) := (g' : ↥(Subgroup.centralizer ({u} : Set G))).2
    have hg'z : (((g' : ↥(Subgroup.centralizer ({u} : Set G))) : G)) ∈
        Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg'c)
    refine ⟨conjSub (((g' : ↥(Subgroup.centralizer ({u} : Set G))) : G)) M,
      conjSub_mem_tqMembers3 hΩ.conjInvariant hg'u hM, hNz _ hg'z M hMd, ?_⟩
    rw [← hg', ← secAct_map_secImg hΩ hc2 (g' : ↥(Subgroup.centralizer ({u} : Set G))),
      secAct_of_mem hΩ hc2 g'.2]
    rfl
  have hinvB : ∀ g : ↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u),
      tb * g = g * tb → ∀ N ∈ good, conjSub g N ∈ good := by
    intro g hg N hN
    obtain ⟨M, hM, hMd, rfl⟩ := hN
    have hfix : secAct hΩ hc2 ⟨t, htC⟩ g = g := by
      rw [secAct_of_mem hΩ hc2 htY, ← htb, MulAut.conj_apply, hg]
      group
    obtain ⟨g', hg'c, hg'⟩ := exists_fixed_lift_coreHull hΩ hc2 htC ht.sq hfix
    have hg'u : (((g' : ↥(Subgroup.centralizer ({u} : Set G))) : G)) ∈
        Subgroup.centralizer ({u} : Set G) := (g' : ↥(Subgroup.centralizer ({u} : Set G))).2
    have hg't : (((g' : ↥(Subgroup.centralizer ({u} : Set G))) : G)) ∈
        Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg'c)
    refine ⟨conjSub (((g' : ↥(Subgroup.centralizer ({u} : Set G))) : G)) M,
      conjSub_mem_tqMembers3 hΩ.conjInvariant hg'u hM, hNt _ hg't M hMd, ?_⟩
    rw [← hg', ← secAct_map_secImg hΩ hc2 (g' : ↥(Subgroup.centralizer ({u} : Set G))),
      secAct_of_mem hΩ hc2 g'.2]
    rfl
  have hclos : ∀ g ∈ Subgroup.closure
      ({q | secAct hΩ hc2 ⟨z, hzC⟩ q = q} ∪ {q | tb * q = q * tb}),
      (∀ N ∈ good, conjSub g N ∈ good) ∧ (∀ N ∈ good, conjSub g⁻¹ N ∈ good) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · refine ⟨hinvA x hx, hinvA x⁻¹ ?_⟩
        rw [map_inv, hx]
      · refine ⟨hinvB x hx, hinvB x⁻¹ ?_⟩
        have hx' : tb * x = x * tb := hx
        calc tb * x⁻¹ = x⁻¹ * (x * tb) * x⁻¹ := by group
          _ = x⁻¹ * (tb * x) * x⁻¹ := by rw [hx']
          _ = x⁻¹ * tb := by group
    | one =>
      refine ⟨fun N hN => ?_, fun N hN => ?_⟩ <;> simpa using hN
    | mul x y _ _ hx hy =>
      refine ⟨fun N hN => ?_, fun N hN => ?_⟩
      · rw [conjSub_mul]
        exact hx.1 _ (hy.1 N hN)
      · rw [mul_inv_rev, conjSub_mul]
        exact hy.2 _ (hx.2 N hN)
    | inv x _ hx => exact ⟨hx.2, by simpa using hx.1⟩
  have hall : ∀ N ∈ secFam Ω u, N ∈ good := by
    intro N hN
    obtain ⟨g, hg, rfl⟩ := hH N hN
    exact (hclos g hg).1 _ hJgood
  refine coreLayer_le_of_forall fun M hM => ?_
  obtain ⟨M₁, hM₁, hM₁d, hM₁eq⟩ := hall _ (secImg_mem_secFam hM)
  obtain ⟨m, hm, rfl⟩ := exists_conj_of_secImg_eq_gen hΩ hc2 hM₁ hM hM₁eq.symm
  have hmd : conjSub m M₁ ∈ dComp Ω K := hNz m (hOdd m hm) M₁ hM₁d
  exact (TwinADescent.coreAt_le_left u _).trans (le_iSup₂_of_le _ hmd le_rfl)

end P5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
