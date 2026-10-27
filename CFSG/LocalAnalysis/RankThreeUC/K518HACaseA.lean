module

public import CFSG.LocalAnalysis.RankThreeUC.K518HAKind
public import CFSG.LocalAnalysis.RankThreeUC.K518HALevi

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open scoped Pointwise
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LeviBlock
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar CFSG.AGLEmbeddingD2.Tits.GN516
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section CaseA

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

private theorem map_posUnipotentExcept_stable (h : BorelQuotient D n H π M) (i : Fin D.rank)
    (c : MulAut Y) (hcR : ((unipJ D {i}).map π).map c.toMonoidHom = (unipJ D {i}).map π) :
    ((posUnipotentExcept D i).map π).map c.toMonoidHom = (posUnipotentExcept D i).map π := by
  set Rb : Subgroup Y := (unipJ D {i}).map π with hRb
  set W : Subgroup Y := (posUnipotentExcept D i).map π with hW
  have hWR : W ≤ Rb := map_posUnipotentExcept_le h i
  have hRn : Rb ≤ Subgroup.normalizer (W : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).1 (map_posUnipotentExcept_normal h i)
  have hNR : W.map c.toMonoidHom ≤ Rb := by
    calc W.map c.toMonoidHom ≤ Rb.map c.toMonoidHom := Subgroup.map_mono hWR
      _ = Rb := hcR
  have hNn : Rb ≤ Subgroup.normalizer ((W.map c.toMonoidHom : Subgroup Y) : Set Y) := by
    have h1 := Subgroup.map_equiv_normalizer_eq W c
    change (Subgroup.normalizer (W : Set Y)).map c.toMonoidHom =
      Subgroup.normalizer ((W.map c.toMonoidHom : Subgroup Y) : Set Y) at h1
    calc Rb = Rb.map c.toMonoidHom := hcR.symm
      _ ≤ (Subgroup.normalizer (W : Set Y)).map c.toMonoidHom := Subgroup.map_mono hRn
      _ = _ := h1
  have hN : ((W.map c.toMonoidHom).subgroupOf Rb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).2 hNn
  have hle : W.map c.toMonoidHom ≤ W :=
    le_map_posUnipotentExcept_of_normal h i hNR hN ((isPGroup_map_posUnipotentExcept h i).map _)
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (f := c.toMonoidHom) (K := W) c.injective).symm)

private theorem rankOne_inf_posUnipotentExcept_eq_bot_of (h : BorelQuotient D n H π M) (i : Fin D.rank)
    (hN : ∀ N : Subgroup ↥(rankOne D.rootGroup i), N.Normal → IsPGroup 2 N → N = ⊥) :
    rankOne D.rootGroup i ⊓ posUnipotentExcept D i = ⊥ := by
  set V : Subgroup K := rankOne D.rootGroup i ⊓ posUnipotentExcept D i with hV
  have hVn : (V.subgroupOf (rankOne D.rootGroup i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hg' : g ∈ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
      rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i hg
    have hgn := Subgroup.mem_normalizer_iff.1 hg'
    constructor
    · rintro ⟨hv1, hv2⟩
      refine ⟨(rankOne D.rootGroup i).mul_mem ((rankOne D.rootGroup i).mul_mem hg hv1)
        ((rankOne D.rootGroup i).inv_mem hg), (hgn v).1 hv2⟩
    · rintro ⟨hv1, hv2⟩
      refine ⟨?_, (hgn v).2 hv2⟩
      have := (rankOne D.rootGroup i).mul_mem ((rankOne D.rootGroup i).mul_mem
        ((rankOne D.rootGroup i).inv_mem hg) hv1) hg
      simpa [mul_assoc] using this
  have hV2 : IsPGroup 2 (V.subgroupOf (rankOne D.rootGroup i)) :=
    ((isPGroup_posUnipotentExcept h i).to_le inf_le_right).comap_subtype
  have h0 := hN _ hVn hV2
  refine eq_bot_iff.2 fun x hx => ?_
  have hxL : x ∈ rankOne D.rootGroup i := hx.1
  have : (⟨x, hxL⟩ : ↥(rankOne D.rootGroup i)) ∈ V.subgroupOf (rankOne D.rootGroup i) :=
    Subgroup.mem_subgroupOf.2 hx
  rw [h0, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem caseA (h : BorelQuotient D n H π M) (hZ : Subgroup.center Y = ⊥) (i : Fin D.rank)
    (hkind : RkKind ↥(rankOne D.rootGroup i)) (hker : π.ker ⊓ rankOne D.rootGroup i = ⊥)
    (h1 : K518RkSL2) (h2 : K518RkSU3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card ↥(rankOne D.rootGroup i))
    (c : MulAut Y) (hc : ∃ k : ℕ, orderOf c = p ^ k)
    (hcR : ((unipJ D {i}).map π).map c.toMonoidHom = (unipJ D {i}).map π)
    (hcInn : c ∉ ((unipJ D {i}).map π).map (MulAut.conj : Y →* MulAut Y)) :
    2 ≤ CFSG.Open.pRank p
      (((unipJ D {i}).map π).map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers c) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hWn := map_posUnipotentExcept_normal h i
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_eq_bot hZ
  have hgood : NodeGood ↥(rankOne D.rootGroup i) p := nodeGood_of_rkKind h1 h2 hkind hp hp2 hpL
  rcases hgood with ⟨hN, hRK, hI⟩ | hr
  · have hLU := rankOne_inf_posUnipotentExcept_eq_bot_of h i hN
    obtain ⟨e⟩ := exists_mulEquiv_levi h i hLU hker
    have hRK' := RKGood.of_mulEquiv e hp hp2 hRK
    have hI' : p ∣ Nat.card (MulAut.conj : (↥((unipJ D {i}).map π) ⧸
        ((posUnipotentExcept D i).map π).subgroupOf ((unipJ D {i}).map π)) →*
          MulAut (↥((unipJ D {i}).map π) ⧸
            ((posUnipotentExcept D i).map π).subgroupOf ((unipJ D {i}).map π))).range := by
      rw [natCard_range_conj_eq e]
      exact hI
    exact autRK hp hp2 ((unipJ D {i}).map π) ((posUnipotentExcept D i).map π)
      (map_posUnipotentExcept_le h i) hRK' hI' c hc hcR
      (map_posUnipotentExcept_stable h i c hcR) hcInn
  · have hπ1 : Function.Injective (π.comp (rankOne D.rootGroup i).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      refine eq_bot_iff.2 fun x hx => ?_
      have hx1 : (x : K) ∈ π.ker ⊓ rankOne D.rootGroup i := ⟨hx, x.2⟩
      rw [hker, Subgroup.mem_bot] at hx1
      rw [Subgroup.mem_bot]
      exact Subtype.ext hx1
    have h3 := CFSG.SectionRank.pRank_le_map hp.one_lt _ hπ1 ⊤
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype] at h3
    have h4 : CFSG.Open.pRank p ((rankOne D.rootGroup i).map π) ≤
        CFSG.Open.pRank p ((unipJ D {i}).map π) :=
      CFSG.SectionRank.pRank_mono hp.one_lt
        (Subgroup.map_mono (rankOne_le_unipJ (Set.mem_singleton i)))
    have h5 := CFSG.SectionRank.pRank_le_map hp.one_lt _ hinj ((unipJ D {i}).map π)
    have h6 : CFSG.Open.pRank p (((unipJ D {i}).map π).map (MulAut.conj : Y →* MulAut Y)) ≤
        CFSG.Open.pRank p
          (((unipJ D {i}).map π).map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers c) :=
      CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left
    omega

end CaseA

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
