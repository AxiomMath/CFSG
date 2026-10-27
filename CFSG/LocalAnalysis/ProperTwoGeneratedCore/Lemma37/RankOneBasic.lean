module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SquareCase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearSetup
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

structure RankOneSetting (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G)
    (z : G) (J : Subgroup (EscapingQuotient z)) : Prop where
  square : SquareCaseSetting G S H z
  component : CFSG.IsComponent J
  not_le : ¬ J ≤ escapingImage H z
  unique : ∀ x ∈ J, orderOf x = 2 → x = escapingBar z

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem quotientData : EscapingQuotientData H z :=
  escapingQuotientData h.square.core (h.square.core.sylow_le h.square.central.1)
    h.square.central.2.1 h.square.escape

theorem sylowImage_le : escapingSylowImage S z ≤ escapingImage H z :=
  escapingSylowImage_le_image h.square.core.sylow_le

theorem coe_sylow :
    (sylowBarSylow h.square.central : Subgroup (EscapingQuotient z)) = escapingSylowImage S z := by
  rw [coe_sylowBarSylow, sylowBar_range]

theorem exists_conj_le {P : Subgroup (EscapingQuotient z)} (hP : IsPGroup 2 P) :
    ∃ m : EscapingQuotient z, P.map (MulAut.conj m).toMonoidHom ≤ escapingSylowImage S z := by
  obtain ⟨m, hm⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_conjugate_into_sylow_within_overgroup 2
      Nat.prime_two (sylowBarSylow h.square.central) ⊤ le_top P hP le_top
  exact ⟨m, h.coe_sylow ▸ hm⟩

theorem pRank_le_one : CFSG.Open.pRank 2 J ≤ 1 :=
  pRank_two_le_one_of_forall_involution_eq h.quotientData.bar_order h.unique

theorem component_pRank_le_one {L : Subgroup (EscapingQuotient z)} (hL : CFSG.IsComponent L) :
    CFSG.Open.pRank 2 L ≤ 1 := by
  have hq := h.quotientData
  by_contra hlt
  have h2 : 2 ≤ CFSG.Open.pRank 2 L := by omega
  have := hq.component_normal_of_two_le_pRank hL h2
  obtain ⟨V, hVL, hV, hVcard⟩ := CFSG.SectionRank.exists_pRank (by decide : 1 < 2) L
  obtain ⟨m, hm⟩ := h.exists_conj_le
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 2 V hV)
  set W := V.map (MulAut.conj m).toMonoidHom with hW
  have hWL : W ≤ L := by
    rintro _ ⟨v, hv, rfl⟩
    exact (inferInstance : L.Normal).conj_mem v (hVL hv) m
  have hWrank : 2 ≤ CFSG.Open.pRank 2 W := by
    rw [hW, CFSG.RankThreeCoreUniqueness.Helpers.pRank_map_automorphism 2 (by decide)]
    exact h2.trans (CFSG.SectionRank.le_pRank (by decide) le_rfl hV hVcard)
  have hJL : J ≠ L := by
    rintro rfl
    have := h.pRank_le_one
    omega
  have hcomm : J ≤ Subgroup.centralizer (L : Set (EscapingQuotient z)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute h.component hL).resolve_left hJL)
  apply h.not_le
  refine le_trans ?_ (hq.centralizer_le W (hm.trans h.sylowImage_le) hWrank)
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (hcomm hj) w (hWL hw))

theorem eq_bar_of_mem_component {L : Subgroup (EscapingQuotient z)} (hL : CFSG.IsComponent L)
    {x : EscapingQuotient z} (hx : x ∈ L) (hx2 : orderOf x = 2) : x = escapingBar z := by
  have hq := h.quotientData
  by_contra hne
  have := two_le_pRank_of_commuting_involutions hx (h.square.caseTwo L hL) hx2 hq.bar_order hne
    (hq.commute_bar x)
  have := h.component_pRank_le_one hL
  omega

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
