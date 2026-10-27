module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCore
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoData
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDih
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoStr
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCov
public import CFSG.GH74.GLS.Stage2.Local.P27.Leaf27DatumPlus

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

theorem lemma5_2Two_thm
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) : Lemma5_2Two := by
  refine lemma5_2Two_of_dbar ?_
  intro G _ _ z k S ctx T Tstar p H P hctx hnt _hnc
  obtain ⟨hPH, hPp, hTP, hcov⟩ := hctx.maxi.1
  obtain ⟨U, hUS, hU4, hzU, ⟨t₁, ht₁U, hsw₁c⟩, hT, hTS, hTstar⟩ :
      ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ z ∈ U ∧ (∃ t ∈ U, SwapsComps z t) ∧
        IsSylowOf 2 T (centralizer (U : Set G)) ∧ T ≤ S ∧
        Tstar = pLayerOf 2 (centralizer (U : Set G)) ⊔ T := by
    rcases hctx.T5 with ⟨h, -, -⟩ | ⟨-, h⟩
    · exact absurd h hnt
    · exact h
  obtain ⟨hcl, q, L₁, L₂, x₀, hP₁₂, hx, hpat⟩ := L52Two.two_class_pattern (hfld G z k S ctx) ctx hnt
  obtain ⟨L₁', L₂', hne', hcomps', hsw'⟩ := hsw₁c
  have hsw₁ : Swaps z t₁ L₁ L₂ :=
    L52Two.swaps_transport hne' (hcomps'.symm.trans hP₁₂.comps) hsw'
  obtain ⟨t, htS, hu, hUeq, hD, hq, hcls⟩ :=
    L52Two.data52_of_pattern ctx.central ctx.sylow hP₁₂ hx hpat hUS hU4 hzU ht₁U hsw₁
  subst hUeq
  have hSC : S ≤ Cen z := Psp4Stage1.S_le_Cen ctx.sylow
  have hUT : L52Two.U4 z t ≤ T := L52Two.le_of_isSylowOf_centralizer hu.isPGroup_U4 hu.comm_U4 hT
  have hzH : z ∈ H := hctx.T_le (hUT (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)))
  have htH : t ∈ H := hctx.T_le (hUT (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  have hUH : L52Two.U4 z t ≤ H := hUT.trans hctx.T_le
  have hx₀ : ∃ x₀' ∈ Cen z, IsNonCentralInvolution x₀' :=
    ⟨x₀, hSC hx.x_mem, hx.x_inv, hx.x_nonCentral⟩
  obtain ⟨x₁, hDP⟩ := leaf_p27datumPlus_of_ctx (Ctx := Stage2Ctx) hfld
    (fun _ _ _ _ _ _ c => c.data) (fun _ _ _ _ _ _ c => c.central)
    (fun _ _ _ _ _ _ c => c.sylow) (fun _ _ _ _ _ _ c => c.std.kgh) hSch G z k S ctx hcl hx₀
  have hx1nc : IsNonCentralInvolution x₁ := by
    obtain ⟨T₀, D₁, D₂, U₀, T₁, q₀, n, t', hC, -, -, -⟩ := hDP
    exact hC.x_nc
  have hDQ : DihQuot (z * t) := by
    obtain ⟨c, hc⟩ := isConj_iff.1 (hcls x₁ hx1nc)
    rw [← hc]
    exact (dihQuot_of_datumPlus hDP).conj c
  have hrank : L52Two.NoE32 G := L52Two.noE32_of_pRank_le_four ctx.std.rank.2
  have hstr : L52Two.Hstr z t :=
    L52Two.hstr_of_ctx hu
      (fun s hs => (Subgroup.mem_centralizer_iff.1 (hSC hs) z (Set.mem_singleton z)).symm)
      (hUS (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))) htS hT hTS hD
  have hcov' := L52Two.covering_L0 hTstar hT.isPGroup hT.le hcov
  obtain ⟨I₁, hI⟩ := L52Two.exists_goodI1 hu.isPGroup_U4 hUH hq hcov'
  exact L52Two.dbar_core hu hctx.prime hctx.odd hzH htH hPp (fun u hu' => hTP (hUT hu')) hI
    (fun W hW2 hWI hUW => L52Two.centralizer_W_le hrank hu.isPGroup_U4 hU4 hUH hstr hI hW2 hWI hUW)
    (fun W hW2 hUW hWC => L52Two.W_cyclic_or_dihedral hu hzH htH hDQ hW2 hUW hWC)

end CFSG.GH74.GLS.Stage2.Signalizer
