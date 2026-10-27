module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dStmt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5AtlasProved

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
open KFactsSmall

theorem K1525d_of_core_aux_sylow_map {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {T : Subgroup G}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T.map f) ⊤ := by
  refine ⟨le_top, hT.2.1.map f, ?_⟩
  have h1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  have h2 : ((T.map f).subgroupOf ⊤).index = (T.map f).index :=
    Subgroup.relIndex_top_right (T.map f)
  have h3 : (T.map f).index ∣ T.index := Subgroup.index_map_dvd T hf
  have h4 := hT.2.2
  rw [h1] at h4
  rw [h2]
  exact fun h => h4 (h.trans h3)

theorem K1525d_of_core_aux_sylow_inf {G : Type} [Group G] [Finite G] {P L : Subgroup G}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P ⊤) (hN : P ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((P ⊓ L).subgroupOf L) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hP.2.1, hP.2.2⟩
  have h2 : CFSG.ABGLocalTools.IsSylowOf 2 P (P ⊔ L) := h1.of_le le_sup_left le_top
  have h3 : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ L) L :=
    h2.inf_of_le_normalizer le_sup_right (sup_le hN Subgroup.le_normalizer)
  obtain ⟨-, hpg, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h3
  refine ⟨le_top, hpg.comap_subtype, ?_⟩
  have h4 : (((P ⊓ L).subgroupOf L).subgroupOf ⊤).index = ((P ⊓ L).subgroupOf L).index :=
    Subgroup.relIndex_top_right ((P ⊓ L).subgroupOf L)
  rw [h4]
  exact hdvd

theorem K1525d_of_core_aux_map_borel {G : Type} [Group G] {L S : Subgroup G} (hS : S ≤ L) :
    (⊤ ⊓ Subgroup.normalizer ((S.subgroupOf L : Subgroup L) : Set L)).map L.subtype =
      L ⊓ Subgroup.normalizer (S : Set G) := by
  rw [top_inf_eq, ← Subgroup.subgroupOf_normalizer_eq hS, Subgroup.subgroupOf_map_subtype,
    inf_comm]

theorem K1525d_of_core_aux_minOver {G : Type} [Group G] {L S : Subgroup G} (hS : S ≤ L)
    {P' : Subgroup L} (h : IsMinOverBorel ⊤ (S.subgroupOf L) P') :
    IsMinOverBorel L S (P'.map L.subtype) := by
  obtain ⟨-, hlt, hmin⟩ := h
  have hB := K1525d_of_core_aux_map_borel hS
  refine ⟨Subgroup.map_subtype_le P', ?_, ?_⟩
  · rw [← hB]
    exact lt_of_le_of_ne (Subgroup.map_mono hlt.le) fun he =>
      hlt.ne (Subgroup.map_injective L.subtype_injective he)
  · intro Q hBQ hQP
    have hQL : Q ≤ L := hQP.trans (Subgroup.map_subtype_le P')
    have hQ : (Q.subgroupOf L).map L.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQL
    rw [← hB] at hBQ
    have h1 : ⊤ ⊓ Subgroup.normalizer ((S.subgroupOf L : Subgroup L) : Set L) ≤ Q.subgroupOf L :=
      Subgroup.map_le_iff_le_comap.mp hBQ
    have h2 : Q.subgroupOf L ≤ P' :=
      (Subgroup.comap_mono hQP).trans
        (le_of_eq (Subgroup.comap_map_eq_self_of_injective L.subtype_injective P'))
    rcases hmin (Q.subgroupOf L) h1 h2 with h3 | h3
    · left
      rw [← hQ, h3, hB]
    · right
      rw [← hQ, h3]

theorem K1525d_of_core_aux_pElement_map {G : Type} [Group G] {L : Subgroup G} (P' : Subgroup L) :
    (pElementSubgroup 2 P').map L.subtype ≤ pElementSubgroup 2 (P'.map L.subtype) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxP, k, hk⟩
  have hx : L.subtype x ∈ pElementSubgroup 2 (P'.map L.subtype) := by
    refine Subgroup.subset_closure ⟨⟨x, hxP, rfl⟩, k, ?_⟩
    rw [orderOf_injective L.subtype L.subtype_injective x]
    exact hk
  exact hx

theorem K1525d_of_core_aux_isL3TwoModO2 {G : Type} [Group G] {A L : Subgroup G} (hA : A ≤ L)
    (h : IsL3TwoModO2 (A.subgroupOf L)) : IsL3TwoModO2 A := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  let f : ↥(A.subgroupOf L) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hA
  exact ⟨d, hd, ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥(A.subgroupOf L)) (CFSG.pCore 2 ↥A) f
    (CFSG.pCore_map_iso 2 f)).symm.trans e⟩⟩

theorem K1525d_of_core_aux_chevTwo_congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsChevTwo Y') : IsChevTwo Y := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.trans f⟩⟩)

theorem K1525d_of_core_aux_chevTwo_quot {L : Type} [Group L] (hc : Subgroup.center L = ⊥)
    (h : IsChevTwo L) : IsChevTwo (L ⧸ Subgroup.center L) :=
  K1525d_of_core_aux_chevTwo_congr
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot) h

theorem K1525d_of_core_aux_center_eq_bot {L : Type} [Group L] [IsSimpleGroup L]
    (hq : CFSG.Open.IsQuasisimple L) : Subgroup.center L = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L)).resolve_right fun h => ?_
  have hs : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (QuotientGroup.eq.mpr (by rw [h]; exact Subgroup.mem_top _))

theorem K1525d_of_core_aux_chev {G : Type} [Group G] {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (hiso : Nonempty (↥L ≃* alternatingGroup (Fin 8)) ∨ IsL5Two ↥L) :
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) := by
  rcases hiso with ⟨⟨e⟩⟩ | ⟨d, ⟨q, hq2, hd⟩, ⟨e⟩⟩
  · haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup ↥L := e.isSimpleGroup
    exact K1525d_of_core_aux_chevTwo_quot (K1525d_of_core_aux_center_eq_bot hq)
      (Or.inr (Or.inl ⟨8, Or.inr (Or.inr rfl), ⟨e⟩⟩))
  · obtain ⟨e5⟩ := CFSG.AGLEmbeddingD2.McLaughlin.nonempty_equiv_G52_of_isL5Two
      (⟨d, ⟨q, hq2, hd⟩, ⟨e⟩⟩ : IsL5Two ↥L)
    haveI : IsSimpleGroup (GL (Fin 5) (ZMod 2)) := CFSG.GroupTheory.GL52.isSimpleGroup_G52
    haveI : IsSimpleGroup ↥L := e5.isSimpleGroup
    have hdvd : q.p ∣ 2 := by
      rw [← hq2, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
    have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
    have hchev : IsChevIndexTwo d.1 := by
      rw [hd]
      exact hp2
    exact K1525d_of_core_aux_chevTwo_quot (K1525d_of_core_aux_center_eq_bot hq)
      (Or.inl ⟨d, hchev, ⟨e⟩⟩)

theorem K1525d_of_core_aux_cover_le {X : Type} [Group X] [Finite X] {T Ti : Subgroup X}
    {L : Subgroup (X ⧸ gnC T)} {P' : Subgroup ↥L} {B : Subgroup (X ⧸ gnC T)}
    (hB : B ≤ gnImg T (Subgroup.normalizer (Ti : Set X)))
    (h : pElementSubgroup 2 (P'.map L.subtype) ≤ B) :
    pElementSubgroup 2 P' ≤ (gnA T Ti L).subgroupOf L := by
  have hpel := K1525d_of_core_aux_pElement_map P'
  have hPL : pElementSubgroup 2 (P'.map L.subtype) ≤ L :=
    (pElementSubgroup_le _).trans (Subgroup.map_subtype_le P')
  show pElementSubgroup 2 P' ≤ (gnA T Ti L).comap L.subtype
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_inf ((hpel.trans h).trans hB) (hpel.trans hPL)

theorem K1525d_of_core (hC : K1525dCore) : K1525d := by
  intro X _ _ T T₁ T₂ hT hGN L hL hN hiso h1 h2
  have hSylT : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T) ⊤ :=
    K1525d_of_core_aux_sylow_map (QuotientGroup.mk' (gnC T)) (QuotientGroup.mk'_surjective _) hT
  have hSylL := K1525d_of_core_aux_sylow_inf hSylT hN
  have hChev := K1525d_of_core_aux_chev hL.2.2 hiso
  have hcover : ∀ P' : Subgroup ↥L, IsMinOverBorel ⊤ ((gnImg T T ⊓ L).subgroupOf L) P' →
      pElementSubgroup 2 P' ≤ (gnA T T₁ L).subgroupOf L ∨
        pElementSubgroup 2 P' ≤ (gnA T T₂ L).subgroupOf L := by
    intro P' hP'
    rcases hGN L hL hChev _ (K1525d_of_core_aux_minOver inf_le_right hP') with h | h
    · exact Or.inl (K1525d_of_core_aux_cover_le
        (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _)) h)
    · exact Or.inr (K1525d_of_core_aux_cover_le le_rfl h)
  have hrk : ∀ Ti : Subgroup X, CFSG.Open.pRank 3 (gnA T Ti L) ≤ 1 →
      CFSG.Open.pRank 3 ((gnA T Ti L).subgroupOf L) ≤ 1 := by
    intro Ti h
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three
      (gnA T Ti L) L inf_le_right]
    exact h
  rcases hC ↥L hiso _ _ _ hSylL hcover (hrk T₁ h1) (hrk T₂ h2) with h | h
  · exact Or.inl (K1525d_of_core_aux_isL3TwoModO2 inf_le_right h)
  · exact Or.inr (K1525d_of_core_aux_isL3TwoModO2 inf_le_right h)

end CFSG.LocalAnalysis.RankThreeUC.S15
