module

public import CFSG.GroupTheory.SwappedFactorsOffenders

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedLocalCore
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedSignalizer
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedEmbeddingCover
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSetup

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.Sol76.Sig

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_mem_ne_one_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) :
    ∃ v : G, v ∈ V ∧ v ≠ 1 := by
  have hcard : Nat.card V = 4 := hV.card_four
  by_contra h
  push Not at h
  have hsub : V ≤ (⊥ : Subgroup G) := by
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hx1 (h x hx)
  have hdvd : Nat.card V ∣ Nat.card (⊥ : Subgroup G) := Subgroup.card_dvd_of_le hsub
  rw [Subgroup.card_bot] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

omit [Finite G] in
private theorem exists_mem_ne_one_ne_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V)
    {t : G} (ht : orderOf t = 2) :
    ∃ v : G, v ∈ V ∧ v ≠ 1 ∧ v ≠ t := by
  have hcard : Nat.card V = 4 := hV.card_four
  have hzcard : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  by_contra h
  push Not at h
  have hsub : V ≤ zpowers t := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · rw [h x hx hx1]; exact Subgroup.mem_zpowers t
  have hdvd : Nat.card V ∣ Nat.card (zpowers t) := Subgroup.card_dvd_of_le hsub
  rw [hzcard] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

omit [Finite G] in
private theorem centralizer_inf_centralizer_le_normalizer {E : Subgroup G} {v : G}
    {W H : Subgroup G} (hW : W = wGroup E (zpowers v))
    (hH : H = normalizer (W : Set G)) :
    centralizer (E : Set G) ⊓ centralizer ({v} : Set G) ≤ H := by
  intro g hg
  rw [hH, hW]
  have hgv : g ∈ centralizer ((zpowers v : Subgroup G) : Set G) := by
    rw [CFSG.GroupTheory.centralizer_zpowers_eq]
    exact hg.2
  exact le_normalizer_wGroup
    (Subgroup.centralizer_le_normalizer (E : Set G) hg.1)
    (Subgroup.centralizer_le_normalizer ((zpowers v : Subgroup G) : Set G) hgv)

omit [Finite G] in
private theorem wGroup_eq_of_theta_collapse {E U : Subgroup G} {v : G}
    (h : ∀ e ∈ E, e ≠ 1 → theta U e = theta (zpowers v) e) :
    wGroup E U = wGroup E (zpowers v) := by
  apply le_antisymm
  · refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    rw [h e he he1]
    exact le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)
  · refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    rw [← h e he he1]
    exact le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)

omit [Finite G] in
private theorem oddCoreIn_centralizer_le_of_conj {H : Subgroup G} {s t g : G}
    (hg : g ∈ H) (hst : g⁻¹ * s * g = t)
    (h : oddCoreIn (centralizer ({t} : Set G)) ≤ H) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ H := by
  have hs : s = g * t * g⁻¹ := by rw [← hst]; group
  have hconj : centralizer ({s} : Set G) =
      CFSG.conjugate (centralizer ({t} : Set G)) g⁻¹ := by
    rw [hs]
    simpa using (centralizer_singleton_conjugate t g⁻¹).symm
  calc oddCoreIn (centralizer ({s} : Set G))
      = CFSG.conjugate (oddCoreIn (centralizer ({t} : Set G))) g⁻¹ := by
        rw [hconj, ← oddCoreIn_conjugate]
    _ ≤ H := CFSG.ComponentClassification.FooteMarked.conjugate_le_of_mem h (H.inv_mem hg)

private theorem base_centralizer_le_of_conj {H : Subgroup G} {s t g : G}
    (hg : g ∈ H) (hst : g⁻¹ * s * g = t)
    (h : base (centralizer ({t} : Set G)) ≤ H) :
    base (centralizer ({s} : Set G)) ≤ H := by
  have hs : s = g * t * g⁻¹ := by rw [← hst]; group
  have hconj : centralizer ({s} : Set G) =
      CFSG.conjugate (centralizer ({t} : Set G)) g⁻¹ := by
    rw [hs]
    simpa using (centralizer_singleton_conjugate t g⁻¹).symm
  calc base (centralizer ({s} : Set G))
      = CFSG.conjugate (base (centralizer ({t} : Set G))) g⁻¹ := by
        rw [hconj, ← base_conjugate]
    _ ≤ H := CFSG.ComponentClassification.FooteMarked.conjugate_le_of_mem h (H.inv_mem hg)


theorem allPure_markedComponents
    [IsSimpleGroup G]
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {N Ki Kj E F B W H : Subgroup G}
    (_hKproper : CFSG.Open.IsKProper G)
    (hFam : IsomorphicFamily S T)
    (hTop : GSThmB.IsSmallAltOrL2 T)
    (_hN : IsMarkedChoice S T N)
    (hKi : Ki ∈ markedComponents S T N)
    (hKj : Kj ∈ markedComponents S T N)
    (hKiKj : Ki ≠ Kj)
    (hE4 : IsKleinFour E) (hF4 : IsKleinFour F)
    (hEKj : E ≤ Kj) (hFKi : F ≤ Ki)
    (hEF : E ≤ centralizer (F : Set G))
    (_hB : CFSG.Open.IsElemAbelian 2 B) (_hBcard : Nat.card B = 8)
    (_hEB : E ≤ B) (_hBF : B ≤ centralizer (F : Set G))
    (hWEF : W = wGroup E F) (hWFE : W = wGroup F E) (_hWBF : W = wGroup B F)
    (_hWodd : Odd (Nat.card W)) (_hWne : W ≠ ⊥)
    (hHdef : H = normalizer (W : Set G)) (_hHproper : H < ⊤)
    (hbaseN : base N ≤ H)
    (hAll : AllInvolutionOddCoreLe (E ⊔ F) H)
    (hSeress : ∀ K ∈ markedComponents S T N,
      ∀ (U : Subgroup G), IsKleinFour U → U ≤ coreActionKernel K →
      ∀ b ∈ K, orderOf b = 2 → b ∈ centralizer (U : Set G) →
      ∀ u ∈ U, u ≠ 1 → theta U b = theta (zpowers u) b) :
    ∀ K ∈ markedComponents S T N, ∀ t ∈ K, orderOf t = 2 →
      oddCoreIn (centralizer ({t} : Set G)) ≤ H ∧
      base (centralizer ({t} : Set G)) ≤ H := by
  classical
  have hDonor : ∀ (X H J A : Subgroup G), IsTwoComponentIn J X → J ≤ H →
      oddCoreIn X ≤ H → IsKleinFour A → A ≤ J →
      X ⊓ centralizer (A : Set G) ≤ H → base X ≤ H := by
    intro X H J A hJ hJH hOX hA hAJ hC
    exact base_le_of_actual_component_and_fixedCentralizer hJ hJH hAJ
      (isPGroup_of_isKleinFour hA) hOX hC
  have hAll' : ∀ z : G, z ∈ centralizer ((E ⊔ F : Subgroup G) : Set G) → orderOf z = 2 →
      oddCoreIn (centralizer ({z} : Set G)) ≤ H := by
    intro z hz hz2
    exact hAll z hz hz2
  have hKiH : Ki ≤ H :=
    (le_sSup hKi).trans ((markedLayer_le_base S T N).trans hbaseN)
  have hKjH : Kj ≤ H :=
    (le_sSup hKj).trans ((markedLayer_le_base S T N).trans hbaseN)
  have hKjCoreKi : Kj ≤ coreActionKernel Ki :=
    GSThmB.B5a.le_coreActionKernel_of_ne hKi.1.1 hKj.1.1 hKi.1.2 hKj.1.2 hKiKj
  have hKiCoreKj : Ki ≤ coreActionKernel Kj :=
    GSThmB.B5a.le_coreActionKernel_of_ne hKj.1.1 hKi.1.1 hKj.1.2 hKi.1.2 hKiKj.symm
  have hEcent : ∀ e ∈ E, e ≠ 1 → e ∈ centralizer ((E ⊔ F : Subgroup G) : Set G) := by
    intro e he _
    rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr
        (fun x hx => comm_of_isKleinFour hE4 x hx e he)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => hEF he y hy)
  have hFcent : ∀ v ∈ F, v ≠ 1 → v ∈ centralizer ((E ⊔ F : Subgroup G) : Set G) := by
    intro v hv _
    rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr
        (fun e he => ((Subgroup.mem_centralizer_iff.mp (hEF he)) v hv).symm)
    · exact Subgroup.mem_centralizer_iff.mpr
        (fun y hy => comm_of_isKleinFour hF4 y hy v hv)
  have hCEv : ∀ v ∈ F, v ≠ 1 →
      centralizer (E : Set G) ⊓ centralizer ({v} : Set G) ≤ H := by
    intro v hv hv1
    have hWv : W = wGroup E (zpowers v) := by
      rw [hWEF]
      refine wGroup_eq_of_theta_collapse (fun e he he1 => ?_)
      exact hSeress Kj hKj F hF4 (hFKi.trans hKiCoreKj) e (hEKj he)
        (orderOf_eq_two_of_isKleinFour hE4 he he1) (hEF he) v hv hv1
    exact centralizer_inf_centralizer_le_normalizer hWv hHdef
  have hCFe : ∀ e ∈ E, e ≠ 1 →
      centralizer (F : Set G) ⊓ centralizer ({e} : Set G) ≤ H := by
    intro e he he1
    have hWe : W = wGroup F (zpowers e) := by
      rw [hWFE]
      refine wGroup_eq_of_theta_collapse (fun v hv hv1 => ?_)
      exact hSeress Ki hKi E hE4 (hEKj.trans hKjCoreKi) v (hFKi hv)
        (orderOf_eq_two_of_isKleinFour hF4 hv hv1)
        (Subgroup.mem_centralizer_iff.mpr
          (fun x hx => ((Subgroup.mem_centralizer_iff.mp (hEF hx)) v hv).symm))
        e he he1
    exact centralizer_inf_centralizer_le_normalizer hWe hHdef
  have hEcase : ∀ e ∈ E, e ≠ 1 →
      oddCoreIn (centralizer ({e} : Set G)) ≤ H ∧
      base (centralizer ({e} : Set G)) ≤ H := by
    intro e he he1
    have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE4 he he1
    have heCore : e ∈ coreActionKernel Ki := hKjCoreKi (hEKj he)
    have hOe : oddCoreIn (centralizer ({e} : Set G)) ≤ H := hAll' e (hEcent e he he1) he2
    obtain ⟨J, hJ, hJH⟩ := exists_fixedShadowHull_le_of_source_le
      (S := S) (T := T) (markedST_of_isomorphicFamily hFam) hKi.2 he2 heCore hOe hKiH
    have hFJ : F ≤ J := by
      refine (B0_le_fixedShadow (S := S) (T := T) hKi.2 he2 heCore hFKi
        (isPGroup_of_isKleinFour hF4) ?_).trans hJ.fixedShadow_le
      exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hEF he y hy)
    have hJX : IsTwoComponentIn J (centralizer ({e} : Set G)) := by
      have h := hJ.isTwoComponentIn
      rwa [CFSG.GroupTheory.centralizer_zpowers_eq] at h
    have hCent : centralizer ({e} : Set G) ⊓ centralizer (F : Set G) ≤ H := by
      simpa [inf_comm] using hCFe e he he1
    exact ⟨hOe, hDonor (centralizer ({e} : Set G)) H J F hJX hJH hOe hF4 hFJ hCent⟩
  have hFcase : ∀ v ∈ F, v ≠ 1 →
      oddCoreIn (centralizer ({v} : Set G)) ≤ H ∧
      base (centralizer ({v} : Set G)) ≤ H := by
    intro v hv hv1
    have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hF4 hv hv1
    have hvCore : v ∈ coreActionKernel Kj := hKiCoreKj (hFKi hv)
    have hOv : oddCoreIn (centralizer ({v} : Set G)) ≤ H := hAll' v (hFcent v hv hv1) hv2
    obtain ⟨J, hJ, hJH⟩ := exists_fixedShadowHull_le_of_source_le
      (S := S) (T := T) (markedST_of_isomorphicFamily hFam) hKj.2 hv2 hvCore hOv hKjH
    have hEJ : E ≤ J := by
      refine (B0_le_fixedShadow (S := S) (T := T) hKj.2 hv2 hvCore hEKj
        (isPGroup_of_isKleinFour hE4) ?_).trans hJ.fixedShadow_le
      exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hEF hy)) v hv).symm
    have hJX : IsTwoComponentIn J (centralizer ({v} : Set G)) := by
      have h := hJ.isTwoComponentIn
      rwa [CFSG.GroupTheory.centralizer_zpowers_eq] at h
    have hCent : centralizer ({v} : Set G) ⊓ centralizer (E : Set G) ≤ H := by
      simpa [inf_comm] using hCEv v hv hv1
    exact ⟨hOv, hDonor (centralizer ({v} : Set G)) H J E hJX hJH hOv hE4 hEJ hCent⟩
  have hSmallQuot : ∀ {K : Subgroup G}, K ∈ markedComponents S T N →
      GSThmB.IsSmallAltOrL2 (↥K ⧸ pPrimeCore 2 ↥K) := by
    intro K hK
    obtain ⟨eK⟩ := hK.2.2.1
    exact GSThmB.isSmallAltOrL2_of_mulEquiv eK.symm hTop
  have hConjIn : ∀ {K : Subgroup G}, K ∈ markedComponents S T N →
      ∀ s t' : ↥K ⧸ pPrimeCore 2 ↥K, orderOf s = 2 → orderOf t' = 2 →
        ∃ g : ↥K ⧸ pPrimeCore 2 ↥K, g⁻¹ * s * g = t' := by
    intro K hK s t' hs ht'
    exact GSThmB.cfSmallInv (↥K ⧸ pPrimeCore 2 ↥K) (hSmallQuot hK) s t' hs ht'
  intro K hK t htK ht2
  by_cases hKiK : K = Ki
  ·
    rw [hKiK] at hK htK
    obtain ⟨f, hfF, hf1⟩ := exists_mem_ne_one_of_isKleinFour hF4
    have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hF4 hfF hf1
    have hfKi : f ∈ Ki := hFKi hfF
    have hY := hConjIn hK
    have htk : orderOf (⟨t, htK⟩ : ↥Ki) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact ht2
    have hfk : orderOf (⟨f, hfKi⟩ : ↥Ki) = 2 := by
      rw [Subgroup.orderOf_mk, hf2]
    obtain ⟨g, hg⟩ := GSThmB.involutions_conj_of_quotient (Y := ↥Ki) hY htk hfk
    have hgG : ((g : ↥Ki) : G) ∈ H := hKiH g.2
    have hg' : ((g : ↥Ki) : G)⁻¹ * t * ((g : ↥Ki) : G) = f := by
      have h := congrArg Subtype.val hg
      simpa using h
    exact ⟨oddCoreIn_centralizer_le_of_conj hgG hg' (hFcase f hfF hf1).1,
      base_centralizer_le_of_conj hgG hg' (hFcase f hfF hf1).2⟩
  · by_cases hKjK : K = Kj
    ·
      rw [hKjK] at hK htK
      obtain ⟨e, heE, he1⟩ := exists_mem_ne_one_of_isKleinFour hE4
      have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE4 heE he1
      have heKj : e ∈ Kj := hEKj heE
      have hY := hConjIn hK
      have htk : orderOf (⟨t, htK⟩ : ↥Kj) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact ht2
      have hek : orderOf (⟨e, heKj⟩ : ↥Kj) = 2 := by
        rw [Subgroup.orderOf_mk, he2]
      obtain ⟨g, hg⟩ := GSThmB.involutions_conj_of_quotient (Y := ↥Kj) hY htk hek
      have hgG : ((g : ↥Kj) : G) ∈ H := hKjH g.2
      have hg' : ((g : ↥Kj) : G)⁻¹ * t * ((g : ↥Kj) : G) = e := by
        have h := congrArg Subtype.val hg
        simpa using h
      exact ⟨oddCoreIn_centralizer_le_of_conj hgG hg' (hEcase e heE he1).1,
        base_centralizer_le_of_conj hgG hg' (hEcase e heE he1).2⟩
    ·
      have hKmKi : K ≠ Ki := hKiK
      have hKmKj : K ≠ Kj := hKjK
      have hKCoreKi : K ≤ coreActionKernel Ki :=
        GSThmB.B5a.le_coreActionKernel_of_ne hKi.1.1 hK.1.1 hKi.1.2 hK.1.2 hKmKi.symm
      have hKCoreKj : K ≤ coreActionKernel Kj :=
        GSThmB.B5a.le_coreActionKernel_of_ne hKj.1.1 hK.1.1 hKj.1.2 hK.1.2 hKmKj.symm
      have hKiCoreK : Ki ≤ coreActionKernel K :=
        GSThmB.B5a.le_coreActionKernel_of_ne hK.1.1 hKi.1.1 hK.1.2 hKi.1.2 hKmKi
      have hKjCoreK : Kj ≤ coreActionKernel K :=
        GSThmB.B5a.le_coreActionKernel_of_ne hK.1.1 hKj.1.1 hK.1.2 hKj.1.2 hKmKj
      have hKCoreK : K ≤ K := le_rfl
      have hKH : K ≤ H :=
        (le_sSup hK).trans ((markedLayer_le_base S T N).trans hbaseN)
      have hEFCoreK : E ⊔ F ≤ coreActionKernel K :=
        sup_le (hEKj.trans hKjCoreK) (hFKi.trans hKiCoreK)
      have hEF2 : IsPGroup 2 ↥(E ⊔ F) := by
        have hFE : F ≤ centralizer (E : Set G) := (Subgroup.le_centralizer_iff).mp hEF
        exact IsPGroup.to_sup_of_normal_left'
          (isPGroup_of_isKleinFour hE4) (isPGroup_of_isKleinFour hF4)
          (hFE.trans (Subgroup.centralizer_le_normalizer _))
      have hcover : ∀ x ∈ K, ∃ i ∈ fixedShadow K (E ⊔ F), ∃ n ∈ oddCoreIn K, x = i * n :=
        fixedShadow_cover_of_perfect hK.2.1 hEF2 hEFCoreK
      have hsup : fixedShadow K (E ⊔ F) ⊔ oddCoreIn K = K :=
        fixedShadow_sup_oddCoreIn_eq_of_cover hcover
      obtain ⟨o, hoO, hot⟩ :=
        exists_oddCore_conj_mem_of_sup (fixedShadow_le K (E ⊔ F)) hsup htK ht2
      have hOK : oddCoreIn K ≤ K := by
        change (pPrimeCore 2 ↥K).map K.subtype ≤ K
        exact Subgroup.map_subtype_le _
      have hoH : o ∈ H := hKH (hOK hoO)
      set t' : G := o * t * o⁻¹ with ht'def
      have ht'Fix : t' ∈ fixedShadow K (E ⊔ F) := hot
      have ht'K : t' ∈ K := (fixedShadow_le K (E ⊔ F)) ht'Fix
      have ht'C : t' ∈ centralizer ((E ⊔ F : Subgroup G) : Set G) :=
        fixedShadow_le_centralizer K (E ⊔ F) ht'Fix
      have ht'2 : orderOf t' = 2 := by
        rw [ht'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]
      have ht'1 : t' ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at ht'2
        omega
      have hOt' : oddCoreIn (centralizer ({t'} : Set G)) ≤ H := hAll' t' ht'C ht'2
      have hKCoreKi_t' : t' ∈ coreActionKernel Ki := hKCoreKi ht'K
      obtain ⟨e, heE, he1, hene⟩ := exists_mem_ne_one_ne_of_isKleinFour hE4 ht'2
      have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE4 heE he1
      have heCore : e ∈ coreActionKernel Ki := hKjCoreKi (hEKj heE)
      have hU4 : IsKleinFour ↥(zpowers e ⊔ zpowers t') :=
        CFSG.Goldschmidt75.isKleinFour_sup he2 ht'2 hene
          ((Subgroup.mem_centralizer_iff.mp ht'C) e (Subgroup.mem_sup_left heE))
      have hUcore : zpowers e ⊔ zpowers t' ≤ coreActionKernel Ki :=
        sup_le (Subgroup.zpowers_le.mpr heCore) (Subgroup.zpowers_le.mpr hKCoreKi_t')
      have hvU : ∀ v ∈ F, v ≠ 1 →
          v ∈ centralizer ((zpowers e ⊔ zpowers t' : Subgroup G) : Set G) := by
        intro v hv _
        rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
        refine ⟨?_, ?_⟩
        · rw [CFSG.GroupTheory.centralizer_zpowers_eq]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hEF heE v hv)
        · rw [CFSG.GroupTheory.centralizer_zpowers_eq]
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (ht'C v (Subgroup.mem_sup_right hv))
      have hvE : ∀ v ∈ F, v ≠ 1 → v ∈ centralizer (E : Set G) := by
        intro v hv _
        exact Subgroup.mem_centralizer_iff.mpr
          (fun x hx => ((Subgroup.mem_centralizer_iff.mp (hEF hx)) v hv).symm)
      have htheta1 : ∀ v ∈ F, v ≠ 1 → theta E v = theta (zpowers e ⊔ zpowers t') v := by
        intro v hv hv1
        have h1 : theta E v = theta (zpowers e) v :=
          hSeress Ki hKi E hE4 (hEKj.trans hKjCoreKi) v (hFKi hv)
            (orderOf_eq_two_of_isKleinFour hF4 hv hv1) (hvE v hv hv1)
            e heE he1
        have h2 : theta (zpowers e ⊔ zpowers t') v = theta (zpowers e) v :=
          hSeress Ki hKi (zpowers e ⊔ zpowers t') hU4 hUcore v (hFKi hv)
            (orderOf_eq_two_of_isKleinFour hF4 hv hv1) (hvU v hv hv1)
            e (Subgroup.mem_sup_left (Subgroup.mem_zpowers e)) he1
        exact h1.trans h2.symm
      have htheta2 : ∀ v ∈ F, v ≠ 1 →
          theta (zpowers e ⊔ zpowers t') v = theta (zpowers t') v := by
        intro v hv hv1
        exact hSeress Ki hKi (zpowers e ⊔ zpowers t') hU4 hUcore v (hFKi hv)
          (orderOf_eq_two_of_isKleinFour hF4 hv hv1) (hvU v hv hv1)
          t' (Subgroup.mem_sup_right (Subgroup.mem_zpowers t')) ht'1
      have hWt' : W = wGroup F (zpowers t') := by
        rw [hWFE]
        refine wGroup_eq_of_theta_collapse (fun v hv hv1 => ?_)
        exact (htheta1 v hv hv1).trans (htheta2 v hv hv1)
      have hCFt' : centralizer (F : Set G) ⊓ centralizer ({t'} : Set G) ≤ H :=
        centralizer_inf_centralizer_le_normalizer hWt' hHdef
      obtain ⟨J, hJ, hJH⟩ := exists_fixedShadowHull_le_of_source_le
        (S := S) (T := T) (markedST_of_isomorphicFamily hFam) hKi.2 ht'2 hKCoreKi_t' hOt' hKiH
      have hFJ : F ≤ J := by
        refine (B0_le_fixedShadow (S := S) (T := T) hKi.2 ht'2 hKCoreKi_t' hFKi
          (isPGroup_of_isKleinFour hF4) ?_).trans hJ.fixedShadow_le
        exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (ht'C y (Subgroup.mem_sup_right hy))
      have hJX : IsTwoComponentIn J (centralizer ({t'} : Set G)) := by
        have h := hJ.isTwoComponentIn
        rwa [CFSG.GroupTheory.centralizer_zpowers_eq] at h
      have hCent : centralizer ({t'} : Set G) ⊓ centralizer (F : Set G) ≤ H := by
        simpa [inf_comm] using hCFt'
      have hBaseT' : base (centralizer ({t'} : Set G)) ≤ H :=
        hDonor (centralizer ({t'} : Set G)) H J F hJX hJH hOt' hF4 hFJ hCent
      have hoinvH : o⁻¹ ∈ H := H.inv_mem hoH
      have hst : (o⁻¹)⁻¹ * t * o⁻¹ = t' := by
        simpa [inv_inv] using ht'def.symm
      exact ⟨oddCoreIn_centralizer_le_of_conj hoinvH hst hOt',
        base_centralizer_le_of_conj hoinvH hst hBaseT'⟩

theorem original_local_core_and_all_pure_containment
    [IsSimpleGroup G]
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {N Ki Kj E F B W H : Subgroup G}
    (_hKproper : CFSG.Open.IsKProper G)
    (hFam : IsomorphicFamily S T)
    (hTop : GSThmB.IsSmallAltOrL2 T)
    (_hN : IsMarkedChoice S T N)
    (hKi : Ki ∈ markedComponents S T N)
    (hKj : Kj ∈ markedComponents S T N)
    (hKiKj : Ki ≠ Kj)
    (hE4 : IsKleinFour E) (hF4 : IsKleinFour F)
    (hEKj : E ≤ Kj) (hFKi : F ≤ Ki)
    (hEF : E ≤ centralizer (F : Set G))
    (_hB : CFSG.Open.IsElemAbelian 2 B) (_hBcard : Nat.card B = 8)
    (_hEB : E ≤ B) (_hBF : B ≤ centralizer (F : Set G))
    (hWEF : W = wGroup E F) (hWFE : W = wGroup F E) (_hWBF : W = wGroup B F)
    (_hWodd : Odd (Nat.card W)) (_hWne : W ≠ ⊥)
    (hHdef : H = normalizer (W : Set G)) (_hHproper : H < ⊤)
    (hbaseN : base N ≤ H)
    (hAll : AllInvolutionOddCoreLe (E ⊔ F) H)
    (hSeress : ∀ K ∈ markedComponents S T N,
      ∀ (U : Subgroup G), IsKleinFour U → U ≤ coreActionKernel K →
      ∀ b ∈ K, orderOf b = 2 → b ∈ centralizer (U : Set G) →
      ∀ u ∈ U, u ≠ 1 → theta U b = theta (zpowers u) b) :
    (∀ K ∈ markedComponents S T N, ∀ t ∈ K, orderOf t = 2 →
      oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H) ∧
    W = oddCoreIn H ∧
      ∀ e ∈ E, e ≠ 1 → theta F e = oddCoreIn H ⊓ centralizer ({e} : Set G) := by
  have hPure := allPure_markedComponents _hKproper hFam hTop _hN hKi hKj hKiKj
    hE4 hF4 hEKj hFKi hEF _hB _hBcard _hEB _hBF hWEF hWFE _hWBF _hWodd _hWne
    hHdef _hHproper hbaseN hAll hSeress
  have hKiH : Ki ≤ H := (le_sSup hKi).trans ((markedLayer_le_base S T N).trans hbaseN)
  have hKjH : Kj ≤ H := (le_sSup hKj).trans ((markedLayer_le_base S T N).trans hbaseN)
  have hEH : E ≤ normalizer (W : Set G) := by
    rw [← hHdef]
    exact hEKj.trans hKjH
  have hFH : F ≤ normalizer (W : Set G) := by
    rw [← hHdef]
    exact hFKi.trans hKiH
  have hbaseE : ∀ e ∈ E, e ≠ 1 →
      base (centralizer ({e} : Set G)) ≤ normalizer (W : Set G) := by
    intro e he he1
    rw [← hHdef]
    exact (hPure Kj hKj e (hEKj he) (orderOf_eq_two_of_isKleinFour hE4 he he1)).2
  obtain ⟨f, hf, hf1⟩ := exists_mem_ne_one_of_isKleinFour hF4
  have hbaseF : base (centralizer ({f} : Set G)) ≤ normalizer (W : Set G) := by
    rw [← hHdef]
    exact (hPure Ki hKi f (hFKi hf) (orderOf_eq_two_of_isKleinFour hF4 hf hf1)).2
  obtain ⟨hcore, hpoint⟩ := oddCoreIn_normalizer_eq_wGroup_of_originalW _hWodd hE4
    (isPGroup_of_isKleinFour hF4) hEH hFH hEF hWEF hbaseE hf hbaseF
  rw [← hHdef] at hcore hpoint
  exact ⟨hPure, hcore.symm, hpoint⟩

theorem original_local_core_and_enlarged_containment
    [IsSimpleGroup G]
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {N Ki Kj E F B W H : Subgroup G}
    (_hKproper : CFSG.Open.IsKProper G)
    (hFam : IsomorphicFamily S T)
    (hTop : GSThmB.IsSmallAltOrL2 T)
    (hN : IsMarkedChoice S T N)
    (hKi : Ki ∈ markedComponents S T N)
    (hKj : Kj ∈ markedComponents S T N)
    (hKiKj : Ki ≠ Kj)
    (hE4 : IsKleinFour E) (hF4 : IsKleinFour F)
    (hEKj : E ≤ Kj) (hFKi : F ≤ Ki)
    (hEF : E ≤ centralizer (F : Set G))
    (_hB : CFSG.Open.IsElemAbelian 2 B) (_hBcard : Nat.card B = 8)
    (_hEB : E ≤ B) (_hBF : B ≤ centralizer (F : Set G))
    (hWEF : W = wGroup E F) (hWFE : W = wGroup F E) (_hWBF : W = wGroup B F)
    (_hWodd : Odd (Nat.card W)) (_hWne : W ≠ ⊥)
    (hHdef : H = normalizer (W : Set G)) (_hHproper : H < ⊤)
    (hbaseN : base N ≤ H)
    (hAll : AllInvolutionOddCoreLe (E ⊔ F) H)
    (hSeress : ∀ K ∈ markedComponents S T N,
      ∀ (U : Subgroup G), IsKleinFour U → U ≤ coreActionKernel K →
      ∀ b ∈ K, orderOf b = 2 → b ∈ centralizer (U : Set G) →
      ∀ u ∈ U, u ≠ 1 → theta U b = theta (zpowers u) b)
    (hLift : ∀ K ∈ markedComponents S T N, ∃ J ∈ markedComponents S T H,
      K ⊔ oddCoreIn J = J) :
    Balanced S T H ∧
      markedCount S T H = markedCount S T N ∧
      markedLayer S T H = oddCoreIn (markedLayer S T H) ⊔ markedLayer S T N ∧
      (∀ J ∈ markedComponents S T H, ∀ t ∈ J, orderOf t = 2 →
        oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H) ∧
      W = oddCoreIn H ∧
      ∀ e ∈ E, e ≠ 1 → theta F e = oddCoreIn H ⊓ centralizer ({e} : Set G) := by
  obtain ⟨hOld, hW, htheta⟩ := original_local_core_and_all_pure_containment
    _hKproper hFam hTop hN hKi hKj hKiKj hE4 hF4 hEKj hFKi hEF _hB _hBcard
    _hEB _hBF hWEF hWFE _hWBF _hWodd _hWne hHdef _hHproper hbaseN hAll hSeress
  have hBal : Balanced S T H :=
    balanced_of_oddCore_covers hFam hN.balanced hbaseN hLift
  obtain ⟨hCount, hLayer⟩ :=
    count_eq_and_markedLayer_eq_of_first_maximum_of_oddCore_covers
      hFam hN.balanced hbaseN hLift (fun X hX => hN.markedCount_le hX)
  have hEnl : ∀ J ∈ markedComponents S T H, ∀ t ∈ J, orderOf t = 2 →
      oddCoreOfCentralizer t ≤ H ∧ base (centralizer ({t} : Set G)) ≤ H :=
    all_pure_containment_of_first_maximum_of_oddCore_covers
      hFam hN.balanced hbaseN hLift (fun X hX => hN.markedCount_le hX) hOld
  exact ⟨hBal, hCount, hLayer, hEnl, hW, htheta⟩



section

theorem original_core_recovery
    [IsSimpleGroup G]
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {N Ki Kj E F B W H : Subgroup G}
    (_hKproper : CFSG.Open.IsKProper G)
    (hFam : IsomorphicFamily S T)
    (hTop : GSThmB.IsSmallAltOrL2 T)
    (hN : IsMarkedChoice S T N)
    (hKi : Ki ∈ markedComponents S T N)
    (hKj : Kj ∈ markedComponents S T N)
    (hKiKj : Ki ≠ Kj)
    (hE4 : IsKleinFour E) (hF4 : IsKleinFour F)
    (hEKj : E ≤ Kj) (hFKi : F ≤ Ki)
    (hEF : E ≤ centralizer (F : Set G))
    (_hB : CFSG.Open.IsElemAbelian 2 B) (_hBcard : Nat.card B = 8)
    (_hEB : E ≤ B) (_hBF : B ≤ centralizer (F : Set G))
    (hBKi : B ≤ coreActionKernel Ki)
    (_hWBF : W = wGroup B F)
    (_hWne : W ≠ ⊥)
    (hHdef : H = normalizer (W : Set G))
    (hLift : ∀ K ∈ markedComponents S T N, ∃ J ∈ markedComponents S T H,
      K ⊔ oddCoreIn J = J) :
    (W = oddCoreIn H ∧ H = normalizer (oddCoreIn H : Set G) ∧
      ∀ (Km Kn Bstar Vstar : Subgroup G),
        Km ∈ markedComponents S T H → Kn ∈ markedComponents S T H → Km ≠ Kn →
        IsKleinFour Bstar → Bstar ≤ Km → CFSG.Open.IsElemAbelian 2 Vstar →
        Vstar ≠ ⊥ → Vstar ≤ Kn → Vstar ≤ centralizer (Bstar : Set G) →
        oddCoreIn H = wGroup Bstar Vstar ∧
          ∀ b ∈ Bstar, b ≠ 1 → theta Vstar b =
            oddCoreIn H ⊓ centralizer ({b} : Set G)) ∧
    Balanced S T H ∧
    (∀ K ∈ markedComponents S T H, ∀ x ∈ K, orderOf x = 2 →
      oddCoreOfCentralizer x ≤ H ∧ base (centralizer ({x} : Set G)) ≤ H) ∧
    (∀ K ∈ markedComponents S T H, ∀ x ∈ K, orderOf x = 2 →
      CFSG.ComponentClassification.LBalance.SchreierSections
        ↥(centralizer ({x} : Set G))) := by
  have hFKj : F ≤ coreActionKernel Kj :=
    hFKi.trans (CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne
      hKj.1 hKi.1 hKiKj.symm)
  have hWEF : W = wGroup E F :=
    _hWBF.trans (wGroup_eq_of_isomorphicFamily hFam hKi.2 hKj.2 hE4 hF4
      _hEB _hBF _hB hFKi hEKj hBKi hFKj)
  have hEFfix : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({v} : Set G)) := by
    intro b hb hb1 v hv hv1
    have hb2 : orderOf b = 2 := orderOf_eq_two_of_isKleinFour hE4 hb hb1
    have hFb : F ≤ centralizer ({b} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp (_hBF (_hEB hb))) w hw)
    exact theta_inf_le_oddCoreIn_of_isomorphicFamily (hfamily := hFam) (hK := hKj.2)
      (hA := hF4) (hAK := hFKj) (hfK := hEKj hb) (hf2 := hb2) (hfA := hFb)
      (hu := hv) (hu1 := hv1)
  have hFEfix : ∀ v ∈ F, v ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      theta E v ⊓ centralizer ({b} : Set G) ≤
        oddCoreIn (centralizer ({b} : Set G)) := by
    intro v hv hv1 b hb hb1
    have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hF4 hv hv1
    have hEv : E ≤ centralizer ({v} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp (_hBF (_hEB he))) v hv).symm
    exact theta_inf_le_oddCoreIn_of_isomorphicFamily (hfamily := hFam) (hK := hKi.2)
      (hA := hE4) (hAK := _hEB.trans hBKi) (hfK := hFKi hv) (hf2 := hv2) (hfA := hEv)
      (hu := hb) (hu1 := hb1)
  have hswap : wGroup E F = wGroup F E :=
    wGroup_eq_swap_of_fixed_bounds hE4 hF4 hEF hEFfix hFEfix
  have hWFE : W = wGroup F E := hWEF.trans hswap
  have h8 : 2 ^ 3 ∣ Nat.card B := by
    rw [_hBcard]
    norm_num
  have hWodd : Odd (Nat.card W) := by
    rw [_hWBF]
    exact Nat.coprime_two_left.mp
      (wGroup_spec_of_isomorphicFamily hFam hKi.2 hKj.2 hE4 hF4 _hEB _hBF _hB
        hFKi hEKj hBKi hFKj h8).1
  obtain ⟨e, heE, he1⟩ := exists_mem_ne_one_of_isKleinFour hE4
  have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE4 heE he1
  have hHproper : H < ⊤ := by
    rw [hHdef]
    exact lt_top_iff_ne_top.mpr
      (CFSG.ComponentClassification.GrSLit.GrS4.normalizer_ne_top_of_odd
        _hWne hWodd he2)
  have hbaseN : base N ≤ H := by
    rw [hHdef, _hWBF]
    exact base_le_normalizer_wGroup_of_balanced hFam hKi.2 hKj.2 hE4 hF4
      _hEB _hBF _hB hFKi hEKj hBKi hFKj hKi.1 hKj.1 hKiKj hN.balanced
  have hAll : AllInvolutionOddCoreLe (E ⊔ F) H := by
    intro v hv _hv2
    have hEs : E ≤ centralizer ({v} : Set G) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hv) e (Subgroup.mem_sup_left he))
    have hFs : F ≤ centralizer ({v} : Set G) := fun f hf =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hv) f (Subgroup.mem_sup_right hf))
    have hvOdd : oddCoreIn (centralizer ({v} : Set G)) ≤
        normalizer (wGroup B F : Set G) :=
      le_normalizer_wGroup_oddCoreIn_centralizer_of_isomorphicFamily hFam hKi.2 hKj.2
        hE4 hF4 _hEB _hBF _hB hFKi hEKj hBKi hFKj hEs hFs
    change oddCoreIn (centralizer ({v} : Set G)) ≤ H
    rw [hHdef, _hWBF]
    exact hvOdd
  have hSeress : ∀ K ∈ markedComponents S T N,
      ∀ (U : Subgroup G), IsKleinFour U → U ≤ coreActionKernel K →
      ∀ b ∈ K, orderOf b = 2 → b ∈ centralizer (U : Set G) →
      ∀ u ∈ U, u ≠ 1 → theta U b = theta (zpowers u) b := by
    intro K hK U hU hUK b hbK hb2 hbU u hu hu1
    have hUb : U ≤ centralizer ({b} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hbU) x hx)
    exact theta_eq_theta_zpowers_of_isomorphicFamily hFam hK.2 hU hUK hbK hb2 hUb hu hu1
  have hSchreier : ∀ K ∈ markedComponents S T H, ∀ v ∈ K, orderOf v = 2 →
      CFSG.ComponentClassification.LBalance.SchreierSections
        ↥(centralizer ({v} : Set G)) := by
    intro K hK v hv hv2
    have hvH : v ∈ H := hK.1.1 hv
    have hCentNeTop : Subgroup.centralizer ({v} : Set G) ≠ ⊤ := by
      intro htop
      have hvCenter : v ∈ Subgroup.center G :=
        (Subgroup.centralizer_eq_top_iff_subset.mp htop) (Set.mem_singleton v)
      have hzNormal : (Subgroup.zpowers v).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hvCenter)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers v) with
        hbot | htopz
      · exact zpowers_ne_bot_of_orderOf_eq_two hv2 hbot
      · have hzH : Subgroup.zpowers v ≤ H := Subgroup.zpowers_le.mpr hvH
        exact hHproper.ne (top_unique (htopz ▸ hzH))
    have hKG : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({v} : Set G)) :=
      CFSG.KCore.KProperNonab.kGroupNonab CFSG.Open.isCatalogGroup_isoInvariant
        _hKproper (Subgroup.centralizer ({v} : Set G)) hCentNeTop
    exact CFSG.ComponentClassification.LBalance.SchreierSections.of_isKGroup
      (fun X _ _ _ hnonab hcat =>
        CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds X hnonab hcat) hKG
  obtain ⟨hBal, -, -, hPure, hW, -⟩ := original_local_core_and_enlarged_containment
    _hKproper hFam hTop hN hKi hKj hKiKj hE4 hF4 hEKj hFKi hEF _hB _hBcard
    _hEB _hBF hWEF hWFE _hWBF hWodd _hWne hHdef hHproper hbaseN hAll hSeress hLift
  refine ⟨⟨hW, ?_, ?_⟩, hBal, hPure, hSchreier⟩
  · simpa only [hW] using hHdef
  intro Km Kn Bstar Vstar hKm hKn hne hBstar hBKm hVstar hVne hVKn hVB
  have : CFSG.IsElementaryAbelian 2 Vstar := hVstar.isElementaryAbelian
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply coreRecovery_of_marked_factors hFam hKm hKn hne hBstar hBKm hVne hVKn hVB hPure
  intro v hv hv1
  exact hSchreier Kn hKn v (hVKn hv) (orderOf_eq_prime (hVstar.2 v hv) hv1)

theorem original_markedLayer_normalizer
    [IsSimpleGroup G]
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {N Ki Kj E F B W H : Subgroup G}
    (_hKproper : CFSG.Open.IsKProper G)
    (hFam : IsomorphicFamily S T)
    (hTop : GSThmB.IsSmallAltOrL2 T)
    (hN : IsMarkedChoice S T N)
    (hKi : Ki ∈ markedComponents S T N)
    (hKj : Kj ∈ markedComponents S T N)
    (hKiKj : Ki ≠ Kj)
    (hE4 : IsKleinFour E) (hF4 : IsKleinFour F)
    (hEKj : E ≤ Kj) (hFKi : F ≤ Ki)
    (hEF : E ≤ centralizer (F : Set G))
    (_hB : CFSG.Open.IsElemAbelian 2 B) (_hBcard : Nat.card B = 8)
    (_hEB : E ≤ B) (_hBF : B ≤ centralizer (F : Set G))
    (hBKi : B ≤ coreActionKernel Ki)
    (_hWBF : W = wGroup B F)
    (_hWne : W ≠ ⊥)
    (hHdef : H = normalizer (W : Set G))
    (hLift : ∀ K ∈ markedComponents S T N, ∃ J ∈ markedComponents S T H,
      K ⊔ oddCoreIn J = J) :
    normalizer (markedLayer S T H : Set G) = H := by
  classical
  let D : Subgroup G := markedLayer S T H
  have hDleH : D ≤ H := markedLayer_le S T H
  have hDnormal : (D.subgroupOf H).Normal := markedLayer_subgroupOf_normal hFam H
  have hcompD : markedComponents S T D = markedComponents S T H := by
    apply Set.Subset.antisymm
    · intro K hK
      exact ⟨⟨hK.1.1.trans hDleH,
        CFSG.ComponentClassification.SolMax.isPComponent_subgroupOf_of_normal
          hDleH hDnormal hK.1⟩, hK.2⟩
    · intro K hK
      exact ⟨isTwoComponentIn_markedLayer hK, hK.2⟩
  obtain ⟨⟨-, hHcore, hrec⟩, -, -, -⟩ := original_core_recovery
    _hKproper hFam hTop hN hKi hKj hKiKj hE4 hF4 hEKj hFKi hEF _hB _hBcard
    _hEB _hBF hBKi _hWBF _hWne hHdef hLift
  have hFKj : F ≤ coreActionKernel Kj :=
    hFKi.trans (CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne
      hKj.1 hKi.1 hKiKj.symm)
  have hbaseN : base N ≤ H := by
    rw [hHdef, _hWBF]
    exact base_le_normalizer_wGroup_of_balanced hFam hKi.2 hKj.2 hE4 hF4
      _hEB _hBF _hB hFKi hEKj hBKi hFKj hKi.1 hKj.1 hKiKj hN.balanced
  obtain ⟨Ji, hJi, hKiJi⟩ := hLift Ki hKi
  obtain ⟨Jj, hJj, hKjJj⟩ := hLift Kj hKj
  have hKiJi_le : Ki ≤ Ji := le_sup_left.trans hKiJi.le
  have hKjJj_le : Kj ≤ Jj := le_sup_left.trans hKjJj.le
  have hJiJj : Ji ≠ Jj := by
    intro h
    have hcover : Ki ⊔ oddCoreIn Jj = Jj := by simpa [h] using hKiJi
    exact hKiKj (eq_of_marked_oddCore_covers hbaseN hKi hKj hJj hcover hKjJj)
  have hEJj : E ≤ Jj := hEKj.trans hKjJj_le
  have hFJi : F ≤ Ji := hFKi.trans hKiJi_le
  have hFea : CFSG.Open.IsElemAbelian 2 F :=
    CFSG.ComponentClassification.Sol76.Sig.isElemAbelian_of_isKleinFour hF4
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hcard := hF4.card_four
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hFE : F ≤ centralizer (E : Set G) :=
    (Subgroup.le_centralizer_iff).mpr hEF
  have hrec0 := hrec Jj Ji E F hJj hJi hJiJj.symm hE4 hEJj hFea hFne hFJi hFE
  have hforward : Subgroup.normalizer (D : Set G) ≤ H := by
    intro g hg
    let φ : G ≃* G := MulAut.conj g⁻¹
    have hginv : g⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      (Subgroup.normalizer (D : Set G)).inv_mem hg
    have hconjD : CFSG.conjugate D g = D := by
      simpa [CFSG.conjugate] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp hginv)
    have hJjD : Jj ∈ markedComponents S T D :=
      ⟨isTwoComponentIn_markedLayer hJj, hJj.2⟩
    have hJiD : Ji ∈ markedComponents S T D :=
      ⟨isTwoComponentIn_markedLayer hJi, hJi.2⟩
    have hJjg : CFSG.conjugate Jj g ∈ markedComponents S T H := by
      have h := mem_markedComponents_conjugate (hFam := hFam) hJjD g
      rw [hconjD] at h
      rwa [hcompD] at h
    have hJig : CFSG.conjugate Ji g ∈ markedComponents S T H := by
      have h := mem_markedComponents_conjugate (hFam := hFam) hJiD g
      rw [hconjD] at h
      rwa [hcompD] at h
    have hJjJig : CFSG.conjugate Jj g ≠ CFSG.conjugate Ji g := by
      intro h
      have h2 := congrArg (fun X : Subgroup G => CFSG.conjugate X g⁻¹) h
      have h2' : Jj = Ji := by
        simpa [CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate_inv] using h2
      exact hJiJj h2'.symm
    have hE4g : IsKleinFour (CFSG.conjugate E g) :=
      CFSG.GorensteinWalter.isKleinFour_map_mulEquiv_cross E hE4 φ
    have hF4g : IsKleinFour (CFSG.conjugate F g) :=
      CFSG.GorensteinWalter.isKleinFour_map_mulEquiv_cross F hF4 φ
    have hFeag : CFSG.Open.IsElemAbelian 2 (CFSG.conjugate F g) :=
      CFSG.ComponentClassification.Sol76.Sig.isElemAbelian_of_isKleinFour hF4g
    have hFneg : CFSG.conjugate F g ≠ ⊥ := by
      intro hbot
      have hcard := hF4g.card_four
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    have hEJjg : CFSG.conjugate E g ≤ CFSG.conjugate Jj g :=
      CFSG.GroupTheory.conjugate_mono g hEJj
    have hFJig : CFSG.conjugate F g ≤ CFSG.conjugate Ji g :=
      CFSG.GroupTheory.conjugate_mono g hFJi
    have hFEg : CFSG.conjugate F g ≤
        centralizer ((CFSG.conjugate E g : Subgroup G) : Set G) := by
      have hmono : CFSG.conjugate F g ≤
          CFSG.conjugate (centralizer (E : Set G)) g :=
        CFSG.GroupTheory.conjugate_mono g hFE
      simpa [centralizer_conjugate] using hmono
    have hrecg := hrec (CFSG.conjugate Jj g) (CFSG.conjugate Ji g)
      (CFSG.conjugate E g) (CFSG.conjugate F g)
      hJjg hJig hJjJig hE4g hEJjg hFeag hFneg hFJig hFEg
    have hmapConj : CFSG.conjugate (wGroup E F) g =
        wGroup (CFSG.conjugate E g) (CFSG.conjugate F g) := by
      simpa only [CFSG.conjugate, φ] using map_wGroup φ E F
    have hconjO : CFSG.conjugate (oddCoreIn H) g = oddCoreIn H := by
      calc
        CFSG.conjugate (oddCoreIn H) g = CFSG.conjugate (wGroup E F) g := by
          rw [hrec0.1]
        _ = wGroup (CFSG.conjugate E g) (CFSG.conjugate F g) := hmapConj
        _ = oddCoreIn H := hrecg.1.symm
    have hginvO : g⁻¹ ∈ Subgroup.normalizer (oddCoreIn H : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
        simpa [CFSG.conjugate] using hconjO)
    have hgO : g ∈ Subgroup.normalizer (oddCoreIn H : Set G) := by
      simpa only [inv_inv] using
        (Subgroup.normalizer (oddCoreIn H : Set G)).inv_mem hginvO
    rw [hHcore]
    exact hgO
  have hreverse : H ≤ Subgroup.normalizer (D : Set G) :=
    markedLayer_le_normalizer hFam H
  simpa only [D] using le_antisymm hforward hreverse

end

end CFSG.ComponentClassification.FooteMarked
