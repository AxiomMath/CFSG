module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_le_subgroupOf {A A' H : Subgroup G} (h : A ≤ A') : A.subgroupOf H ≤ A'.subgroupOf H := by
  intro t ht
  exact Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 ht))

theorem commutator_ne_bot_of_map {H : Subgroup G} {M T : Subgroup ↥H} {A C : Subgroup G}
    (hMA : M.map H.subtype = A) (hTC : T.map H.subtype = C) (h : (⁅A, C⁆ : Subgroup G) ≠ ⊥) :
    (⁅M, T⁆ : Subgroup ↥H) ≠ ⊥ := by
  intro h0
  apply h
  rw [← hMA, ← hTC, ← Subgroup.map_commutator, h0, Subgroup.map_bot]

theorem i173At_of_facts (hN : I173FactNoncyc) (hA : I173FactA) (hD : I173FactD) (hTD : I173FactTD)
    (hO : I173FactO) (G : Type) [Group G] [Finite G] : I173At G := by
  classical
  intro p B x L D K hp hp2 hS h4 hq hchev hsplit hstd hb hc
  have hBmax : GLAIsBmax p B := IsSStarMax.bmax hS
  have hBel : IsElemAbelian p B := hBmax.1
  have hxB : x ∈ B := (IsSStarMax.essential hS).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential hS).2.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes hS
  have hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) ↔ b ∈ Subgroup.zpowers x :=
    S172.cent_eq_zpowers hp hS
  have hid : InnerDiagMarking B L := innerDiagMarking_of_split16 hsplit
  obtain ⟨P0, hP0L, hP0p, hP0nc⟩ :=
    hN p G L B x hp hp2 hq hchev hBel h4 hxB hx1 hBN hcent hid
  have hNL : Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    nbr_le_normalizer hp hS ⟨P0, hP0L, hP0p, hP0nc⟩
  have hBC : B ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact isElemAbelian_commute hBel hxB hb'
  have hBNt : B ≤ Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf Subgroup.le_normalizer hBC
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, L ⊔ (Subgroup.normalizer (B : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) = H := ⟨_, rfl⟩
  have hNH : Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H :=
    hH ▸ le_sup_right
  have hLH : L ≤ H := hH ▸ le_sup_left
  have hBH : B ≤ H := hBNt.trans hNH
  have hxH : x ∈ H := hBH hxB
  have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
    hH ▸ sup_le Subgroup.le_normalizer hNL
  have hKL : K ≤ L := by
    rw [hstd.2.2.2.2.1]
    exact (Y10F.glaLayer_le _).trans inf_le_left
  have hDB : D ≤ B := hstd.1
  have hDH : D ≤ H := hDB.trans hBH
  have hKH : K ≤ H := hKL.trans hLH
  have hLnorm : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  have hcycL : CycModSylow p L := IsSStarMax.cycMod hS
  have hcycH : CycModSylow p (L.subgroupOf H) := S265.cycModSylow_subgroupOf hp hLH hHN hcycL
  have hS'map : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hK'map : (K.subgroupOf H).map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  have hN'map : ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)) ⊓
      Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H)).map H.subtype =
        Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    map_normalizer_centralizer_eq hxH hBH hNH
  have hclos : (closureIn (K.subgroupOf H) ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) :
      Set ↥H)) ⊓ Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H))).map H.subtype =
        closureIn K (Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [closureIn_map_subtype, hK'map, hN'map]
  have hb' : ∃ T : Subgroup ↥H, T ≤ L.subgroupOf H ∧ IsPGroup 2 T ∧
      B.subgroupOf H ≤ Subgroup.normalizer (T : Set ↥H) ∧
      (⁅T, B.subgroupOf H⁆ : Subgroup ↥H) ≠ ⊥ := by
    obtain ⟨T₀, hT₀L, hT₀2, hT₀B, hT₀c⟩ := hb
    have hT₀H : T₀ ≤ H := hT₀L.trans hLH
    refine ⟨T₀.subgroupOf H, subgroupOf_le_subgroupOf hT₀L, S265.isPGroup_subgroupOf' hT₀2 hT₀H, ?_, ?_⟩
    · intro b hb''
      exact (mem_normalizer_subgroupOf_iff hT₀H b).2 (hT₀B (Subgroup.mem_subgroupOf.1 hb''))
    · exact commutator_ne_bot_of_map (Subgroup.map_subgroupOf_eq_of_le hT₀H)
        (Subgroup.map_subgroupOf_eq_of_le hBH) hT₀c
  have hc' : ∃ T : Subgroup ↥H, T ≤ L.subgroupOf H ∧ IsPGroup 2 T ∧
      closureIn (K.subgroupOf H) ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)) ⊓
        Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H)) ⊔ B.subgroupOf H ≤
          Subgroup.normalizer (T : Set ↥H) ∧
      (⁅closureIn (K.subgroupOf H) ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)) ⊓
        Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H)), T⁆ : Subgroup ↥H) ≠ ⊥ := by
    obtain ⟨T₀, hT₀L, hT₀2, hT₀C, hT₀c⟩ := hc
    have hT₀H : T₀ ≤ H := hT₀L.trans hLH
    refine ⟨T₀.subgroupOf H, subgroupOf_le_subgroupOf hT₀L, S265.isPGroup_subgroupOf' hT₀2 hT₀H, ?_, ?_⟩
    · apply sup_le
      · intro g hg
        apply (mem_normalizer_subgroupOf_iff hT₀H g).2
        have hgm : (g : G) ∈ closureIn K (Subgroup.normalizer (B : Set G) ⊓
            Subgroup.centralizer ({x} : Set G)) := by
          rw [← hclos]
          exact Subgroup.mem_map_of_mem _ hg
        exact hT₀C (Subgroup.mem_sup_left hgm)
      · intro b hb''
        exact (mem_normalizer_subgroupOf_iff hT₀H b).2
          (hT₀C (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hb'')))
    · exact commutator_ne_bot_of_map hclos (Subgroup.map_subgroupOf_eq_of_le hT₀H) hT₀c
  have hcfg : Cfg173 p (L.subgroupOf H) (B.subgroupOf H)
      ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)) ⊓
        Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H))
      (D.subgroupOf H) (K.subgroupOf H) ⟨x, hxH⟩ := by
    refine
      { prime := hp
        odd := hp2
        normal := hLnorm
        qs := CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH) hq
        chev := ?_
        top := ?_
        hN := rfl
        elem := (Y10F.isElemAbelian_subgroupOf_iff hBH).2 hBel
        bmax := ?_
        four := ?_
        mem := Subgroup.mem_subgroupOf.2 hxB
        ne_one := ?_
        cent := ?_
        cyc := hcycH
        split := splitInnerDiagMarking16_subgroupOf hBH hLH hsplit
        std := ?_
        hb := hb'
        hc := hc' }
    · unfold IsChevSimple at hchev ⊢
      simp only [S172.catalogIs_pSimple_subgroupOf_iff hLH]
      exact hchev
    · apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup, hS'map, hN'map, Subgroup.map_top, Subgroup.range_subtype]
      exact hH
    · obtain ⟨T₀, hT₀L, hT₀2, hT₀B, hT₀c⟩ := hb
      have hT₀H : T₀ ≤ H := hT₀L.trans hLH
      have hT1 : T₀ ≠ ⊥ := by
        rintro rfl
        apply hT₀c
        simp
      exact gLAIsBmax_subgroupOf hp hBmax hBH hT₀H hT₀2 hT1 hT₀B
    · show p ^ 4 ≤ Nat.card ↥(B.subgroupOf H)
      rw [Y10F.card_subgroupOf hBH]
      exact h4
    · intro h
      apply hx1
      have := congrArg Subtype.val h
      simpa using this
    · intro b' hb''
      show b' ∈ Subgroup.centralizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔ _
      rw [S172.mem_centralizer_subgroupOf_iff hLH, S172.mem_zpowers_subtype_iff]
      exact hcent (b' : G) (Subgroup.mem_subgroupOf.1 hb'')
    · have hDH' : (D.subgroupOf H).map H.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDH
      have key : GLAStdSubPre p ((B.subgroupOf H).map H.subtype) ((⟨x, hxH⟩ : ↥H) : G)
          ((L.subgroupOf H).map H.subtype) ((D.subgroupOf H).map H.subtype)
          ((K.subgroupOf H).map H.subtype) := by
        rw [Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hLH, hDH',
          hK'map]
        exact hstd
      exact S172.glaStdSubPre_map_iff.1 key
  have hconc : T173Concl p (L.subgroupOf H) (B.subgroupOf H)
      (K.subgroupOf H) ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)) ⊓
        Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H)) := by
    by_cases hA' : catalogIs (PSimple p (L.subgroupOf H)) (onLie T173ClassA)
    · exact hA p ↥H _ _ _ _ _ _ hcfg hA'
    · by_cases hD' : catalogIs (PSimple p (L.subgroupOf H)) (onLie T173ClassD)
      · exact hD p ↥H _ _ _ _ _ _ hcfg hD'
      · by_cases hT' : catalogIs (PSimple p (L.subgroupOf H)) (onLie T173ClassTD)
        · exact hTD p ↥H _ _ _ _ _ _ hcfg hT'
        · exact hO p ↥H _ _ _ _ _ _ hcfg hA' hD' hT'
  unfold T173Concl at hconc
  rcases hconc with hT | ⟨B'', U, hB''el, hB''le, hBB'', hne, hU1, hU2, hUK, heq⟩
  · left
    have h := (type126_map_iff (L.subgroupOf H) (K.subgroupOf H) (closureIn (K.subgroupOf H)
      ((Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H)) ⊓
        Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H)))).2 hT
    rw [hS'map, hK'map, hclos] at h
    exact h
  · right
    refine ⟨B''.map H.subtype, U.map H.subtype, (Y10F.isElemAbelian_map_subtype_iff (p := p) B'').2 hB''el,
      ?_, ?_, ?_, ?_, hU2.map H.subtype, ?_, ?_⟩
    · have h1 := Subgroup.map_mono (f := H.subtype) hB''le
      rw [Subgroup.map_sup, hS'map, Subgroup.map_subgroupOf_eq_of_le hBH] at h1
      exact h1
    · have h1 := Subgroup.map_mono (f := H.subtype) hBB''
      rwa [Subgroup.map_subgroupOf_eq_of_le hBH] at h1
    · intro h
      apply hne
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hBH]
      exact h
    · intro h
      apply hU1
      apply Subgroup.map_injective H.subtype_injective
      rw [h, Subgroup.map_bot]
    · have h1 := Subgroup.map_mono (f := H.subtype) hUK
      rwa [hK'map] at h1
    · have h1 := congrArg (fun V : Subgroup ↥H => V.map H.subtype) heq
      rw [Subgroup.map_sup, map_inf_normalizer_subtype, Subgroup.map_inf_eq _ _ H.subtype H.subtype_injective,
        hK'map] at h1
      exact h1

end Final

end CFSG.LocalAnalysis.GLTheoremA.T173

end
