module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTrichotomyLocal
import CFSG.Quasithin.Background.E1Amb

public section

namespace CFSG.GroupTheory

open Subgroup

private theorem inf_normalizer_lt_self_cct {G : Type} [Group G] {L I : Subgroup G}
    (hL : IsGomiChevTwo ↥L) (hIbot : I ≠ ⊥) (hIL : I ≤ L) (hIp : IsPGroup 2 I) :
    L ⊓ Subgroup.normalizer (I : Set G) < L := by
  refine lt_of_le_of_ne inf_le_left fun hEq => hIbot ?_
  have hLY : L ≤ Subgroup.normalizer (I : Set G) := hEq ▸ inf_le_right
  have hnorm : (I.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIL).mpr hLY
  have hp : IsPGroup 2 (I.subgroupOf L) := hIp.comap_subtype
  have hle : I.subgroupOf L ≤ CFSG.pCore 2 ↥L := CFSG.LieType.BorelTits.le_pCore 2 hnorm hp
  have hbot : I.subgroupOf L = ⊥ := by
    rw [hL.2.1] at hle
    exact eq_bot_iff.mpr hle
  calc I = (I.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hIL).symm
    _ = ⊥ := by rw [hbot, Subgroup.map_bot]

private theorem inf_normalizer_inf_normalizer_cct {G : Type} [Group G] {L I : Subgroup G}
    (hcore : CFSG.Open.pCoreOf 2 (L ⊓ Subgroup.normalizer (I : Set G)) = I) :
    L ⊓ Subgroup.normalizer
        ((Subgroup.normalizer (I : Set G) ⊓ L : Subgroup G) : Set G)
      = Subgroup.normalizer (I : Set G) ⊓ L := by
  have hYL : (Subgroup.normalizer (I : Set G) ⊓ L : Subgroup G)
      = L ⊓ Subgroup.normalizer (I : Set G) :=
    inf_comm (Subgroup.normalizer (I : Set G)) L
  rw [hYL]
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
    (L ⊓ Subgroup.normalizer (I : Set G))
  rw [hcore] at h
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans h))
    (le_inf inf_le_left Subgroup.le_normalizer)

private theorem twoResidual_inf_normalizer_le_cct {G : Type} [Group G] [Finite G]
    {L I : Subgroup G}
    (hcore : CFSG.Open.pCoreOf 2 (L ⊓ Subgroup.normalizer (I : Set G)) = I)
    (hrad : CFSG.Quasithin.twoResidual (L ⊓ Subgroup.centralizer (I : Set G)) ≤
      L ⊓ Subgroup.centralizer (L : Set G)) :
    CFSG.Quasithin.twoResidual
        ((Subgroup.normalizer (I : Set G) ⊓ L) ⊓
          Subgroup.centralizer
            (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (I : Set G) ⊓ L) : Set G))
      ≤ L ⊓ Subgroup.centralizer (L : Set G) := by
  have hYL : (Subgroup.normalizer (I : Set G) ⊓ L : Subgroup G)
      = L ⊓ Subgroup.normalizer (I : Set G) :=
    inf_comm (Subgroup.normalizer (I : Set G)) L
  rw [hYL, hcore]
  refine (CFSG.Quasithin.E1.twoResidual_mono
    (inf_le_inf_right (Subgroup.centralizer (I : Set G)) inf_le_left)).trans ?_
  exact hrad

theorem IsGomiParabolicSwap.map_conj {G : Type} [Group G] {S L : Subgroup G} (hL : L.Normal)
    (h : IsGomiParabolicSwap S L) (x : G) :
    IsGomiParabolicSwap (S.map (MulAut.conj x).toMonoidHom) L := by
  obtain ⟨s, hs, P, hSP, hPL, hsP⟩ := h
  have hxL : L.map (MulAut.conj x).toMonoidHom = L := Subgroup.normal_iff_map_conj_eq.mp hL x
  have hxinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hSL : (S.map (MulAut.conj x).toMonoidHom ⊓ L : Subgroup G)
      = (S ⊓ L).map (MulAut.conj x).toMonoidHom := by
    have h1 : (S ⊓ L).map (MulAut.conj x).toMonoidHom
        = S.map (MulAut.conj x).toMonoidHom ⊓ L := by
      rw [Subgroup.map_inf S L (MulAut.conj x).toMonoidHom hxinj, hxL]
    exact h1.symm
  have hN : Subgroup.normalizer
        ((S.map (MulAut.conj x).toMonoidHom ⊓ L : Subgroup G) : Set G)
      = (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).map
          (MulAut.conj x).toMonoidHom := by
    rw [hSL, Subgroup.map_equiv_normalizer_eq]
  have hconj : (L ⊓ (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).map
        (MulAut.conj x).toMonoidHom : Subgroup G)
      = (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).map
          (MulAut.conj x).toMonoidHom := by
    have h1 : (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).map
          (MulAut.conj x).toMonoidHom
        = L.map (MulAut.conj x).toMonoidHom ⊓
            (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).map
              (MulAut.conj x).toMonoidHom :=
      Subgroup.map_inf L _ _ hxinj
    rw [h1, hxL]
  refine ⟨(MulAut.conj x) s, ?_, P.map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_⟩
  · refine ⟨Subgroup.mem_map_of_mem _ hs.1, ?_⟩
    rw [(Subgroup.normalizer_eq_top_iff (H := L)).mpr hL]
    exact Subgroup.mem_top _
  · rw [hN, hconj]
    exact (OrderIso.lt_iff_lt (MulEquiv.mapSubgroup (MulAut.conj x))).mpr hSP
  · simpa only [MulEquiv.coe_mapSubgroup, hxL] using
      (OrderIso.lt_iff_lt (MulEquiv.mapSubgroup (MulAut.conj x))).mpr hPL
  · intro hmem
    rw [← Subgroup.map_equiv_normalizer_eq P (MulAut.conj x)] at hmem
    exact hsP ((Subgroup.mem_map_iff_mem hxinj).mp hmem)

theorem isGomiParabolicSwap_of_mem_normalizer {G : Type} [Group G] [Finite G]
    {L U P : Subgroup G} (hL : L.Normal) (hU : CFSG.ABGLocalTools.IsSylowOf 2 U L) {g : G}
    (hg : IsPGroup 2 (zpowers g)) (hgU : g ∈ normalizer (U : Set G))
    (hUP : L ⊓ normalizer (U : Set G) < P) (hPL : P < L) (hgP : g ∉ normalizer (P : Set G))
    (T : Sylow 2 G) : IsGomiParabolicSwap (T : Subgroup G) L := by
  have hWU : Subgroup.zpowers g ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.zpowers_le_of_mem hgU
  obtain ⟨T₀, hT₀sup, hT₀inf⟩ := exists_sylow_sup_le_inf_eq hL hU hg hWU
  have hswap₀ : IsGomiParabolicSwap (T₀ : Subgroup G) L := by
    refine ⟨g, ?_, P, ?_, hPL, hgP⟩
    · refine ⟨hT₀sup (Subgroup.mem_sup_right (Subgroup.mem_zpowers g)), ?_⟩
      rw [(Subgroup.normalizer_eq_top_iff (H := L)).mpr hL]
      exact Subgroup.mem_top _
    · rw [hT₀inf]
      exact hUP
  have : Finite (Sylow 2 G) :=
    Sylow.finite_of_finiteIndex (Classical.choice (Sylow.nonempty (p := 2) (G := G)))
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G T₀ T
  have hxT : (T : Subgroup G) = (T₀ : Subgroup G).map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul]
    ext y
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    simp only [MulAut.smul_def, MulEquiv.coe_toMonoidHom]
  rw [hxT]
  exact IsGomiParabolicSwap.map_conj hL hswap₀ x

theorem gomiChevCore_of_trichotomy (hIso : GomiChevIsolated) (hTri : GomiChevTrichotomy)
    (hPar : GomiChevParabolic) (hRad : GomiChevRadical) : GomiChevCore := by
  intro G _ _ L X H hLn hL hex hswap hLX hH1 hH hHX h
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [(Subgroup.normalizer_eq_top_iff (H := L)).mpr hLn]
    exact le_top
  rcases hTri G L X H hLn hL hLX hH1 hH hHX h with hiso | hcase2 | hcase3
  · rcases hIso G L H hL hH hHN hiso with htypes | ⟨htypes, hmove⟩
    · exact absurd htypes hex
    · obtain ⟨T, hT⟩ := hswap htypes
      obtain ⟨U₀, hU₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 L
      obtain ⟨U, hU, -, hHU, -⟩ :=
        exists_isSylowOf_le_normalizer (L := L) (P := L) (U₀ := U₀) (H := H)
          le_rfl hU₀ inf_le_left hH hHN
      obtain ⟨a, haH, P, hUP, hPL, haP⟩ := hmove U hU hHU
      exact absurd (isGomiParabolicSwap_of_mem_normalizer hLn hU
        (hH.to_le (Subgroup.zpowers_le_of_mem haH)) (hHU haH) hUP hPL haP T) hT
  · rcases hcase2 with ⟨I, hIbot, hIL, hIp, hcore, hKdata, hIodd⟩
    obtain ⟨K, hHK, hKX, hKsub, hKdvd, hKI⟩ := hKdata
    have hYltL : L ⊓ Subgroup.normalizer (I : Set G) < L :=
      inf_normalizer_lt_self_cct hL hIbot hIL hIp
    have hYne : Subgroup.normalizer (I : Set G) ≠ ⊤ := by
      intro htop
      exact hYltL.ne (inf_eq_left.mpr (by rw [htop]; exact le_top))
    refine ⟨Subgroup.normalizer (I : Set G), hYne, hIodd,
      ⟨K, hHK, hKX, hKsub, hKdvd, hKI⟩, ?_, ?_⟩
    · exact inf_normalizer_inf_normalizer_cct hcore
    · obtain ⟨U, hU, hUN⟩ := hPar G L I hL hIL hIp hcore
      have hrad := (hRad G L U (L ⊓ Subgroup.normalizer (I : Set G)) hL hU hUN hYltL).2
      rw [hcore] at hrad
      exact twoResidual_inf_normalizer_le_cct hcore hrad
  · rcases hcase3 with ⟨htypes, -, -, -, g, hg, U, hU, hgU, P, hUP, hPL, hgP⟩
    obtain ⟨T, hT⟩ := hswap htypes
    exact absurd (isGomiParabolicSwap_of_mem_normalizer hLn hU hg hgU hUP hPL hgP T) hT

end CFSG.GroupTheory

end
