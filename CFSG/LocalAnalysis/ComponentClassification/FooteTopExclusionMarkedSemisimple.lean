module

import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedComponentTools
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedSemisimpleTools
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPMatch
public import CFSG.LocalAnalysis.ComponentClassification.FooteTopExclusionMarkedNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedPure
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedSignalizer
public import CFSG.Adapters.CatalogAgree
public import CFSG.Assembly.OpenBridges

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open CFSG.ComponentClassification.FooteMarked
open CFSG.ComponentClassification.Sol76.Sig

@[expose] def FooteMarkedVanishing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (𝓢 : Set (Subgroup G)),
    FooteSwapSetting G t L 𝓢 →
    ∀ N : Subgroup G, FooteMarked.IsMarkedChoice 𝓢 (L ⧸ Open.fusionZStar L) N →
    ∀ K₁ ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N,
    ∀ K₂ ∈ FooteMarked.markedComponents 𝓢 (L ⧸ Open.fusionZStar L) N, K₁ ≠ K₂ →
    ∀ V E : Subgroup G, V ≤ K₁ → E ≤ K₂ → IsKleinFour ↥V → IsKleinFour ↥E →
      E ≤ centralizer (V : Set G) → ∀ e ∈ E, e ≠ 1 → Sol76.Sig.theta V e = ⊥

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem choiceSemisimple_of_vanishing {T : Type} [Group T] [IsSimpleGroup T]
    {𝓢 : Set (Subgroup G)} (hFam : FooteMarked.IsomorphicFamily 𝓢 T) {N : Subgroup G}
    (hN : FooteMarked.Balanced 𝓢 T N) (hT4 : ∃ V : Subgroup T, IsKleinFour ↥V)
    (hV : ∀ K₁ ∈ FooteMarked.markedComponents 𝓢 T N, ∀ K₂ ∈ FooteMarked.markedComponents 𝓢 T N,
      K₁ ≠ K₂ → ∀ V E : Subgroup G, V ≤ K₁ → E ≤ K₂ → IsKleinFour ↥V → IsKleinFour ↥E →
      E ≤ centralizer (V : Set G) → ∀ e ∈ E, e ≠ 1 → Sol76.Sig.theta V e = ⊥) :
    (∀ K ∈ FooteMarked.markedComponents 𝓢 T N, CFSG.IsQuasisimple ↥K) ∧
      ∀ K ∈ FooteMarked.markedComponents 𝓢 T N, ∀ b ∈ K, orderOf b = 2 →
        ∀ K' ∈ FooteMarked.markedComponents 𝓢 T N, K' ≠ K →
          IsTwoComponentIn K' (centralizer ({b} : Set G)) := by
  classical
  have hST := FooteMarked.markedST_of_isomorphicFamily hFam
  have h2 : 1 < (FooteMarked.markedComponents 𝓢 T N).ncard := hN.1
  have hsimpM : ∀ {M : Subgroup G}, FooteMarked.Marked 𝓢 T M →
      IsSimpleGroup (↥M ⧸ pPrimeCore 2 ↥M) := fun hM => by
    obtain ⟨e⟩ := hM.2.1
    exact e.isSimpleGroup
  have hfour : ∀ K ∈ FooteMarked.markedComponents 𝓢 T N,
      ∃ V : Subgroup G, V ≤ K ∧ IsKleinFour ↥V := by
    intro K hK
    obtain ⟨e⟩ := hK.2.2.1
    exact FooteMarked.exists_isKleinFour_le_of_sup_oddCoreIn le_rfl
      (sup_eq_left.mpr (map_subtype_le _)) e hT4
  have hcomm : ∀ K₁ ∈ FooteMarked.markedComponents 𝓢 T N,
      ∀ K₂ ∈ FooteMarked.markedComponents 𝓢 T N, K₁ ≠ K₂ → ∀ V E : Subgroup G, V ≤ K₁ →
      E ≤ K₂ → IsKleinFour ↥V → IsKleinFour ↥E → E ≤ centralizer (V : Set G) → ∀ e ∈ E,
      e ≠ 1 → V ≤ centralizer (oddCoreIn (centralizer ({e} : Set G)) : Set G) := by
    intro K₁ hK₁ K₂ hK₂ hne V E hV₁ hE₂ hV4 hE4 hEV e he he1
    have h := (Sol76.Sig.theta_eq_bot_iff.mp
      (hV K₁ hK₁ K₂ hK₂ hne V E hV₁ hE₂ hV4 hE4 hEV e he he1)).1
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
  have hquasi : ∀ K ∈ FooteMarked.markedComponents 𝓢 T N, CFSG.IsQuasisimple ↥K := by
    intro K hK
    obtain ⟨K', hK', hK'K⟩ := Set.exists_ne_of_one_lt_ncard h2 K
    obtain ⟨B₀, hB₀K', hB₀⟩ := hfour K' hK'
    have hB₀C : B₀ ≤ UnbalancedLayer.coreActionKernel K :=
      hB₀K'.trans (GSThmB.B5a.le_coreActionKernel_of_ne hK.1.1 hK'.1.1 hK.1.2 hK'.1.2
        (Ne.symm hK'K))
    obtain ⟨hcov, -, -⟩ := FooteMarked.fixedShadow_cover_quotient
      (FooteMarked.Marked.quotient_quasisimple hFam hK.2) (FooteMarked.isPGroup_of_isKleinFour hB₀)
      hB₀C
    obtain ⟨e⟩ := hK.2.2.1
    obtain ⟨V, hVP, hV4⟩ := FooteMarked.exists_isKleinFour_le_of_sup_oddCoreIn
      (FooteMarked.fixedShadow_le K B₀) hcov e hT4
    have hVB₀ : B₀ ≤ centralizer (V : Set G) :=
      le_centralizer_iff.mp ((hVP.trans (FooteMarked.fixedShadow_le_inf K B₀)).trans inf_le_right)
    have hshadow : ∀ b ∈ B₀, b ≠ 1 →
        FooteMarked.fixedShadowAt K b = FooteMarked.fixedShadow K B₀ ∧
          CFSG.IsQuasisimple ↥(FooteMarked.fixedShadowAt K b) := by
      intro b hb hb1
      have hbK : b ∈ UnbalancedLayer.coreActionKernel K := hB₀C hb
      obtain ⟨J, hJ, hJm, -, hJcov⟩ := hST K hK.2 (zpowers b)
        ((FooteMarked.isPGroup_of_isKleinFour hB₀).to_le (zpowers_le.mpr hb)) (zpowers_le.mpr hbK)
        (zpowers_ne_bot.mpr hb1)
      rw [FooteMarked.fixedShadow_zpowers] at hJcov
      rw [UnbalancedLayer.centralizer_zpowers_eq] at hJ
      have hVb : V ≤ FooteMarked.fixedShadowAt K b :=
        hVP.trans (FooteMarked.fixedShadow_le_fixedShadowAt _ hb)
      obtain ⟨hPJ, hJc⟩ := FooteMarked.eq_and_le_centralizer_oddCoreIn hJ (hsimpM hJm) hJcov
        (FooteMarked.fixedShadowAt_perfect K b) hVb
        hV4 (hcomm K hK K' hK' (Ne.symm hK'K) V B₀
          (hVP.trans (FooteMarked.fixedShadow_le K B₀)) hB₀K' hV4 hB₀ hVB₀ b hb hb1)
      have hOJ : oddCoreIn J ≤ centralizer (J : Set G) :=
        (GSThmB.Seven.oddCoreIn_le_of_isPComponent hJ.1 hJ.2).trans (le_centralizer_iff.mp hJc)
      rw [hPJ] at hVb ⊢
      have hJq : CFSG.IsQuasisimple ↥J :=
        FooteMarked.isQuasisimple_of_oddCoreIn_le_centralizer hJm.1 (hsimpM hJm) hOJ
      have hB₀J : B₀ ≤ centralizer (J : Set G) := fun β hβ =>
        FooteMarked.mem_centralizer_of_mem_coreActionKernel (hPJ ▸ FooteMarked.fixedShadowAt_le K b)
          hJm.1 hOJ
          (hPJ ▸ FooteMarked.mem_normalizer_fixedShadowAt
            (UnbalancedLayer.mem_coreActionKernel.mp (hB₀C hβ)).1
            (mul_comm_of_exponent_two hB₀.exponent_two ⟨b, hb⟩ ⟨β, hβ⟩ |> congrArg Subtype.val))
          (hB₀C hβ)
      have hle : J ≤ FooteMarked.fixedShadow K B₀ :=
        FooteMarked.le_fixedShadow_of_perfect hJm.1
          (le_inf (hPJ ▸ FooteMarked.fixedShadowAt_le K b) (le_centralizer_iff.mp hB₀J))
      exact ⟨le_antisymm hle (hPJ ▸ FooteMarked.fixedShadow_le_fixedShadowAt _ hb), hJq⟩
    have hOK : oddCoreIn K ≤ normalizer (FooteMarked.fixedShadow K B₀ : Set G) := by
      have hCN : UnbalancedLayer.coreActionKernel K ≤ normalizer (K : Set G) := fun x hx =>
        (UnbalancedLayer.mem_coreActionKernel.mp hx).1
      refine le_of_isKleinFour_inf_centralizer_le hB₀
        ((hB₀C.trans hCN).trans fun _ hx => mem_normalizer_oddCoreIn hx) (odd_card_oddCoreIn K)
        fun b hb hb1 => ?_
      intro x hx
      rw [← (hshadow b hb hb1).1]
      exact FooteMarked.mem_normalizer_fixedShadowAt
        (le_normalizer ((map_subtype_le _) hx.1))
        (mem_centralizer_singleton_iff.mp hx.2).symm
    have hKP := FooteMarked.eq_of_sup_oddCoreIn_eq_of_le_normalizer hK.2.1 hcov hOK
    obtain ⟨b, hb, hb1⟩ := FooteMarked.exists_ne_one_of_isKleinFour hB₀
    rw [← hKP, ← (hshadow b hb hb1).1]
    exact (hshadow b hb hb1).2
  refine ⟨hquasi, ?_⟩
  intro K hK b hbK hb K' hK' hK'K
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hb
  obtain ⟨E, hEK, hE4, hbE⟩ :=
    FooteMarked.exists_isKleinFour_mem_of_orderOf_eq_two (hfour K hK) hbK hb
  have hKK' : K' ≤ centralizer (K : Set G) :=
    FooteMarked.le_centralizer_of_isTwoComponentIn hK.1 (hquasi K hK) hK'.1 (Ne.symm hK'K)
  have hOK' : K' ≤ centralizer (oddCoreIn (centralizer ({b} : Set G)) : Set G) :=
    FooteMarked.le_of_forall_isKleinFour_le (hquasi K' hK') (hsimpM hK'.2) (hfour K' hK')
      fun V hVK' hV4 =>
      hcomm K' hK' K hK hK'K V E hVK' hEK hV4 hE4
        (hEK.trans (le_centralizer_iff.mp (hVK'.trans hKK'))) b hbE hb1
  have hK'b : K' ≤ centralizer ((zpowers b : Subgroup G) : Set G) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hKK' hy) b hbK).symm
  obtain ⟨J, hJ, hJm, -, hJcov⟩ := hST K' hK'.2 (zpowers b)
    ((FooteMarked.isPGroup_of_isKleinFour hE4).to_le (zpowers_le.mpr hbE))
    (GSLit.mem_coreActionKernel_of_le_centralizer
      (by rw [← UnbalancedLayer.centralizer_zpowers_eq]; exact hK'b) |> zpowers_le.mpr)
    (zpowers_ne_bot.mpr hb1)
  rw [UnbalancedLayer.centralizer_zpowers_eq] at hJ
  have hfs : FooteMarked.fixedShadow K' (zpowers b) = K' :=
    le_antisymm (FooteMarked.fixedShadow_le K' _)
      (FooteMarked.le_fixedShadow_of_perfect hK'.2.1 (le_inf le_rfl hK'b))
  rw [hfs] at hJcov
  have hJK' : K' = J :=
    FooteMarked.eq_of_sup_oddCoreIn_eq_of_le_normalizer hJm.1 hJcov
      (((GSThmB.Seven.oddCoreIn_le_of_isPComponent hJ.1 hJ.2).trans
        (le_centralizer_iff.mp hOK')).trans (centralizer_le_normalizer _))
  rw [hJK']
  exact hJ

end Assembly
theorem footeMarkedChoiceSemisimple_of_vanishing (hV : FooteMarkedVanishing) :
    FooteMarkedChoiceSemisimple := by
  intro G _ _ t L 𝓢 hset N hNc
  haveI : IsSimpleGroup (L ⧸ Open.fusionZStar L) :=
    (GrSLit.fusionZStar_quotient_of_isPComponent hset.2.1.1.2.2.1.2.1
      hset.2.1.1.2.2.1.2.2).1
  exact choiceSemisimple_of_vanishing hset.2.2.2.2.1 hNc.balanced
    (FooteMarked.exists_isKleinFour_of_footeFamilyType hset.2.1.1.2.2.2.2.1) (hV G t L 𝓢 hset N hNc)


section Certificates



theorem footeMarkedVanishing_of_absorption_of_factorCover
    (hA : FooteMarkedAbsorption) (hF : FooteMarkedFactorCover) :
    FooteMarkedVanishing := by
  intro G _ _ t L S hset N hN K1 hK1 K2 hK2 hne V E hVK1 hEK2 hV4 hE4 hEV e he he1
  classical
  let T := L ⧸ Open.fusionZStar L
  haveI hTsimple : IsSimpleGroup T := footeSwapSetting_top_simple hset
  haveI hGsimp : IsSimpleGroup G := hset.2.2.1
  have hTnonab : ∃ a b : T, a * b ≠ b * a := footeSwapSetting_top_nonabelian hset
  have hFam : FooteMarked.IsomorphicFamily S T := hset.2.2.2.2.1
  have hTop : GSThmB.IsSmallAltOrL2 T := by
    rcases footeCounterexample_familyType hset.2.1 with h | ⟨p, f, hp, hp2, hf, hp5, hlm⟩
    · obtain ⟨e7⟩ := h
      exact Or.inl ⟨7, Or.inr (Or.inr rfl), ⟨e7⟩⟩
    · exact Or.inr ⟨p, f, hp, hp2, hf, hp5, hlm⟩
  have hKproper : CFSG.Open.IsKProper G := by
    have hImp : CFSG.Assembly.CatalogImp Blueprint.Catalog CFSG.Assembly.InCatalog :=
      fun X _ _ _ _ h => CFSG.Open.QTFaithfulEmptyTauCeti.inCatalog_of_catalog X h
    exact (CFSG.Assembly.kProper_inCatalog_iff_isKProper G).1
      (CFSG.Assembly.KProper.of_catalogImp hImp (footeSwapSetting_kProper hset))
  obtain ⟨Sz, z, hESz, hFSz, hzSz, hzQ, hz2, hzC, hzNotPair, hBzElem, hBzCard,
      hBzKj, hBzSz, hBzKiKern, hBzC, hBzCent, hBzSylow⟩ :=
    exists_central_sylow_admissible_pair (family := S) (T := T) (N := N)
      (Ki := K1) (Kj := K2) (E := E) (F := V)
      hFam hN.balanced hK1 hK2 hne hE4 hV4 hEK2 hVK1 hEV
  let B : Subgroup G := E ⊔ Subgroup.zpowers z
  let W : Subgroup G := wGroup B V
  let H : Subgroup G := Subgroup.normalizer (W : Set G)
  have hEB : E ≤ B := le_sup_left
  have hBF : B ≤ centralizer (V : Set G) := hBzC
  have hB : CFSG.Open.IsElemAbelian 2 B := hBzElem
  have hBcard : Nat.card B = 8 := hBzCard
  have hBKi : B ≤ UnbalancedLayer.coreActionKernel K1 := hBzKiKern
  have hWBF : W = wGroup B V := rfl
  have hHdef : H = Subgroup.normalizer (W : Set G) := rfl
  have hVK2kern : V ≤ UnbalancedLayer.coreActionKernel K2 :=
    hVK1.trans (CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne
      hK2.1 hK1.1 hne.symm)
  have h8 : 2 ^ 3 ∣ Nat.card B := by
    rw [hBcard]
    norm_num
  have hWodd : Odd (Nat.card W) := by
    rw [hWBF]
    exact Nat.coprime_two_left.mp
      (wGroup_spec_of_isomorphicFamily hFam hK1.2 hK2.2 hE4 hV4 hEB hBF hB
        hVK1 hEK2 hBKi hVK2kern h8).1
  obtain ⟨e0, he0E, he01⟩ := Sol76.Sig.exists_mem_ne_one_of_isKleinFour hE4
  have he02 : orderOf e0 = 2 := FooteMarked.orderOf_eq_two_of_isKleinFour hE4 he0E he01
  have hWbot : W = ⊥ := by
    by_contra hWne
    have hHproper : H < ⊤ := by
      rw [hHdef]
      exact lt_top_iff_ne_top.mpr
        (CFSG.ComponentClassification.GrSLit.GrS4.normalizer_ne_top_of_odd hWne hWodd he02)
    have hbaseN : base N ≤ H := by
      rw [hHdef, hWBF]
      exact base_le_normalizer_wGroup_of_balanced hFam hK1.2 hK2.2 hE4 hV4 hEB hBF hB
        hVK1 hEK2 hBKi hVK2kern hK1.1 hK2.1 hne hN.balanced
    have hLift : ∀ K ∈ markedComponents S T N, ∃ J ∈ markedComponents S T H,
        K ⊔ oddCoreIn J = J :=
      hF G t L S hset N H hN.balanced hbaseN hHproper.ne
    obtain ⟨⟨-, hHcore, hrec⟩, hBal, hPure, hSchreier⟩ :=
      original_core_recovery hKproper hFam hTop hN hK1 hK2 hne hE4 hV4 hEK2 hVK1 hEV
        hB hBcard hEB hBF hBKi hWBF hWne hHdef hLift
    have hNormD : Subgroup.normalizer (markedLayer S T H : Set G) = H :=
      original_markedLayer_normalizer hKproper hFam hTop hN hK1 hK2 hne hE4 hV4 hEK2 hVK1 hEV
        hB hBcard hEB hBF hBKi hWBF hWne hHdef hLift
    have hST : MarkedST S T := markedST_of_isomorphicFamily hFam
    have h2 : 1 < (markedComponents S T H).ncard := hBal.1
    have hCentLe : ∀ Kx ∈ markedComponents S T H, ∀ x ∈ Kx, orderOf x = 2 →
        centralizer ({x} : Set G) ≤ H := by
      intro Kx hKx x hxKx hx2 g hg
      obtain ⟨Kopp, hKopp, hOppNe⟩ := Set.exists_ne_of_one_lt_ncard h2 Kx
      have hxKopp : x ∈ UnbalancedLayer.coreActionKernel Kopp :=
        (CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne
          hKopp.1 hKx.1 hOppNe) hxKx
      obtain ⟨J, hJ⟩ := exists_fixedShadowHull hST hKopp.2
        (isPGroup_zpowers_of_orderOf_eq_two hx2) (Subgroup.zpowers_le.mpr hxKopp)
        (FooteMarked.zpowers_ne_bot_of_orderOf_eq_two hx2)
      have hJC : J ∈ markedComponents S T (centralizer ({x} : Set G)) := by
        refine ⟨?_, hJ.marked⟩
        have hcomp := hJ.isTwoComponentIn
        rwa [CFSG.GroupTheory.centralizer_zpowers_eq] at hcomp
      have hJCg : CFSG.conjugate J g ∈ markedComponents S T (centralizer ({x} : Set G)) :=
        (markedComponents_conjugate_iff hFam (centralizer ({x} : Set G)) ⟨g, hg⟩ J).mp hJC
      have hJH : J ≤ H :=
        ((le_twoLayerIn_of_isTwoComponentIn hJC.1).trans le_sup_right).trans
          (hPure Kx hKx x hxKx hx2).2
      have hJgH : CFSG.conjugate J g ≤ H :=
        ((le_twoLayerIn_of_isTwoComponentIn hJCg.1).trans le_sup_right).trans
          (hPure Kx hKx x hxKx hx2).2
      have hJxC : J ≤ centralizer ({x} : Set G) := hJC.1.1
      have hJgxC : CFSG.conjugate J g ≤ centralizer ({x} : Set G) := hJCg.1.1
      have hxJ : x ∈ centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hJxC hy)
      have hxJg : x ∈ centralizer (CFSG.conjugate J g : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hJgxC hy)
      have hxKernelJ : x ∈ UnbalancedLayer.coreActionKernel J :=
        FooteLit.centralizer_le_coreActionKernel' J hxJ
      have hxKernelJg : x ∈ UnbalancedLayer.coreActionKernel (CFSG.conjugate J g) :=
        FooteLit.centralizer_le_coreActionKernel' (CFSG.conjugate J g) hxJg
      obtain ⟨Km, hKm, hJKm⟩ :=
        hA G t L S hset H J hHproper.ne hBal hJ.marked hJH
          ⟨x, hKx.1.1 hxKx, hx2, hxKernelJ⟩
      obtain ⟨KmG, hKmG, hJgKmG⟩ :=
        hA G t L S hset H (CFSG.conjugate J g) hHproper.ne hBal hJCg.2 hJgH
          ⟨x, hKx.1.1 hxKx, hx2, hxKernelJg⟩
      have hnotJ : ¬ J ≤ Kx :=
        not_le_of_full_oddCoreQuotient_of_involution_centralizes hTnonab hJ.marked.2.1
          hKx.2.2.1 hxKx hx2 hJxC
      have hnotJg : ¬ CFSG.conjugate J g ≤ Kx :=
        not_le_of_full_oddCoreQuotient_of_involution_centralizes hTnonab hJCg.2.2.1
          hKx.2.2.1 hxKx hx2 hJgxC
      have hKmNe : Km ≠ Kx := by
        intro h
        exact hnotJ (by simpa [h] using hJKm)
      have hKmGNe : KmG ≠ Kx := by
        intro h
        exact hnotJg (by simpa [h] using hJgKmG)
      have hT4 : ∃ A0 : Subgroup T, IsKleinFour ↥A0 :=
        exists_isKleinFour_of_footeFamilyType (footeCounterexample_familyType hset.2.1)
      obtain ⟨eJ⟩ := hJ.marked.2.1
      obtain ⟨A, hAJ, hA4⟩ := exists_isKleinFour_le_of_sup_oddCoreIn
        (K := J) (X := J) le_rfl (sup_eq_left.mpr (map_subtype_le _)) eJ hT4
      have hAKm : A ≤ Km := hAJ.trans hJKm
      have hAgJg : CFSG.conjugate A g ≤ CFSG.conjugate J g :=
        CFSG.GroupTheory.conjugate_mono g hAJ
      have hAgKmG : CFSG.conjugate A g ≤ KmG := hAgJg.trans hJgKmG
      have hxA : x ∈ centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact Subgroup.mem_centralizer_singleton_iff.mp (hJxC (hAJ ha))
      have hgNormO : g ∈ Subgroup.normalizer (oddCoreIn H : Set G) :=
        (oddCoreIn_conjugate_eq_of_transported_fourgroup hFam hKm hKmG hKx hKmNe hKmGNe
          hA4 hAKm hAgKmG hxKx hx2 hxA hg hPure
          (hSchreier Kx hKx x hxKx hx2)).2
      rw [hHcore]
      exact hgNormO
    have hContra : False :=
      let hEmbed : FooteMarkedEmbeddingExclusion := footeMarkedEmbeddingExclusion_of_absorption hA
      hEmbed G t L S hset H hHproper.ne hBal hNormD hCentLe
    exact hContra
  have hBbot : wGroup B V = ⊥ := by
    simpa [hWBF] using hWbot
  have hEBmono : wGroup E V ≤ wGroup B V := by
    apply iSup_le
    intro e'
    apply iSup_le
    intro he'
    apply iSup_le
    intro he1'
    exact theta_le_wGroup (hEB he') he1'
  have hEbot : wGroup E V = ⊥ :=
    le_antisymm (hEBmono.trans (le_of_eq hBbot)) bot_le
  exact le_antisymm ((theta_le_wGroup he he1).trans (le_of_eq hEbot)) bot_le

end Certificates

end CFSG.ComponentClassification.FooteLit
