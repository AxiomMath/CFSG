module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBound
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem exists_pow_sq_eq_of_unique {X : Type*} [Group X] {L : Subgroup X} {u w : X}
    (hu : ∀ x ∈ L, orderOf x = 2 → x = u) (hwL : w ∈ L) {k : ℕ} (hw : orderOf w = 2 ^ k)
    (hw1 : w ≠ 1) (hwu : w ≠ u) : ∃ n : ℕ, (w ^ n) ^ 2 = u := by
  rcases k with _ | _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hw
    exact absurd hw hw1
  · exact absurd (hu w hwL (by rw [hw, pow_one])) hwu
  · refine ⟨2 ^ k, hu _ (L.pow_mem (L.pow_mem hwL _) _) ?_⟩
    have hdvd : 2 ^ k * 2 ∣ orderOf w := by
      rw [hw]
      exact ⟨2, by ring⟩
    rw [← pow_mul, orderOf_pow_of_dvd (by positivity) hdvd, hw]
    rw [show 2 ^ (k + 1 + 1) = 2 ^ k * 2 * 2 by ring]
    exact Nat.mul_div_cancel_left 2 (by positivity)

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem exists_sylow_inf {L : Subgroup (EscapingQuotient z)} (hL : CFSG.IsComponent L) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = escapingSylowImage S z ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ :=
    CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal (sylowBarSylow h.square.central) hL.2
  exact ⟨P, hP.trans (by rw [h.coe_sylow])⟩

theorem sylowImage_isPGroup : IsPGroup 2 (escapingSylowImage S z) := by
  rw [← h.coe_sylow]
  exact (sylowBarSylow h.square.central).isPGroup'

theorem exists_sq_eq_bar {L : Subgroup (EscapingQuotient z)} (hL : CFSG.IsComponent L) :
    ∃ a ∈ escapingSylowImage S z, a ∈ L ∧ a ^ 2 = escapingBar z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.exists_sylow_inf hL
  have hnc := not_isCyclic_sylow_two_of_commutator_eq_top hL.1.1.commutator_eq_top
    (two_dvd_card_of_isComponent hL) P
  have hzL : escapingBar z ∈ L := h.square.caseTwo L hL
  have hnot : ¬ (P : Subgroup L) ≤ Subgroup.zpowers (⟨escapingBar z, hzL⟩ : L) := fun hle =>
    hnc (Subgroup.isCyclic_of_le hle)
  obtain ⟨w, hwP, hwz⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hw1 : (w : EscapingQuotient z) ≠ 1 := fun h1 => hwz (by
    rw [show w = 1 from Subtype.ext h1]
    exact Subgroup.one_mem _)
  have hwu : (w : EscapingQuotient z) ≠ escapingBar z := fun h1 => hwz (by
    rw [show w = ⟨escapingBar z, hzL⟩ from Subtype.ext h1]
    exact Subgroup.mem_zpowers _)
  have hwS : (w : EscapingQuotient z) ∈ escapingSylowImage S z ⊓ L :=
    hP ▸ Subgroup.mem_map_of_mem L.subtype hwP
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.sylowImage_isPGroup) ⟨w, hwS.1⟩
  rw [Subgroup.orderOf_mk] at hk
  obtain ⟨n, hn⟩ := exists_pow_sq_eq_of_unique (L := L)
    (fun x hx hx2 => h.eq_bar_of_mem_component hL hx hx2) w.2 hk hw1 hwu
  exact ⟨_, (escapingSylowImage S z).pow_mem hwS.1 n, L.pow_mem w.2 n, hn⟩

theorem eq_bar_of_mem_centralizer {x : EscapingQuotient z} (hxS : x ∈ escapingSylowImage S z)
    (hxC : x ∈ Subgroup.centralizer (J : Set (EscapingQuotient z))) (hx2 : orderOf x = 2) :
    x = escapingBar z := by
  have hq := h.quotientData
  by_contra hne
  set D := Subgroup.closure ({x, escapingBar z} : Set (EscapingQuotient z)) with hD
  have hxD : x ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbD : escapingBar z ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hDH : D ≤ escapingImage H z := by
    rw [hD, Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact h.sylowImage_le hxS
    · exact hq.bar_mem_image
  have hrank : 2 ≤ CFSG.Open.pRank 2 D :=
    two_le_pRank_of_commuting_involutions hxD hbD hx2 hq.bar_order hne (hq.commute_bar x)
  apply h.not_le
  refine le_trans ?_ (hq.centralizer_le D hDH hrank)
  intro j hj
  rw [hD, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact (Subgroup.mem_centralizer_iff.mp hxC j hj).symm
  · exact (hq.commute_bar j).eq.symm

theorem exists_key
    : ∃ k ∈ escapingSylowImage S z,
    k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧ k ^ 2 = escapingBar z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := h.quotientData
  by_contra hno
  push Not at hno
  have hb2 : escapingBar z ^ 2 = 1 := by
    have := pow_orderOf_eq_one (escapingBar z)
    rwa [hq.bar_order] at this
  have hb1 : escapingBar z ≠ 1 := fun h1 => by
    have := hq.bar_order
    rw [h1, orderOf_one] at this
    exact absurd this (by decide)
  have hsq1 : (1 : EscapingQuotient z) ^ 2 ≠ escapingBar z := by
    rw [one_pow]
    exact fun h1 => hb1 h1.symm
  have hsqz : escapingBar z ^ 2 ≠ escapingBar z := by
    rw [hb2]
    exact fun h1 => hb1 h1.symm
  have hsmall : ∀ w ∈ escapingSylowImage S z,
      w ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) → w = 1 ∨ w = escapingBar z := by
    intro w hwS hwC
    by_contra hne
    push Not at hne
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.sylowImage_isPGroup) ⟨w, hwS⟩
    rw [Subgroup.orderOf_mk] at hk
    obtain ⟨n, hn⟩ := exists_pow_sq_eq_of_unique
      (L := escapingSylowImage S z ⊓ Subgroup.centralizer (J : Set (EscapingQuotient z)))
      (fun x hx hx2 => h.eq_bar_of_mem_centralizer hx.1 hx.2 hx2) ⟨hwS, hwC⟩ hk hne.1 hne.2
    exact hno _ ((escapingSylowImage S z).pow_mem hwS n) (Subgroup.pow_mem _ hwC n) hn
  have hcomp : ∀ L : Subgroup (EscapingQuotient z), CFSG.IsComponent L → L = J := by
    intro L hL
    by_contra hLJ
    obtain ⟨a, haS, haL, ha2⟩ := h.exists_sq_eq_bar hL
    have hcomm : L ≤ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((CFSG.LocalCores.distinct_components_commute hL h.component).resolve_left hLJ)
    rcases hsmall a haS (hcomm haL) with rfl | rfl
    · exact hsq1 ha2
    · exact hsqz ha2
  have hlayer : layer (EscapingQuotient z) = J :=
    le_antisymm (sSup_le fun L hL => (hcomp L hL).le) (component_le_layer h.component)
  have hF2 : IsPGroup 2 (fittingSubgroup (EscapingQuotient z)) :=
    CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hq.oddCore_eq_bot
  have hFS : fittingSubgroup (EscapingQuotient z) ≤ escapingSylowImage S z := by
    rw [← h.coe_sylow]
    exact hF2.le_sylow_of_normal _
  have hFC : fittingSubgroup (EscapingQuotient z) ≤
      Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    have hc := CFSG.LocalCores.fitting_layer_commute (G := EscapingQuotient z)
    rw [hlayer] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hzJ : escapingBar z ∈ J := h.square.caseTwo J h.component
  have hFJ : fittingSubgroup (EscapingQuotient z) ≤ J := by
    intro w hw
    rcases hsmall w (hFS hw) (hFC hw) with rfl | rfl
    · exact J.one_mem
    · exact hzJ
  have hunique : ∀ y ∈ generalizedFitting (EscapingQuotient z), orderOf y = 2 →
      y = escapingBar z := fun y hy hy2 =>
    h.unique y (sup_le hFJ hlayer.le hy) hy2
  have h2 := generalizedFittingUniqueInvolutionRankBound _ _ hq.oddCore_eq_bot
    hq.bar_mem_center hq.bar_order hq.layer_ne_bot hunique
  have h3 := hq.rank
  omega

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
