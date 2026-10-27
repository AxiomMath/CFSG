module

public import CFSG.Assembly.OddCoreEliminationStatements
public import CFSG.LocalAnalysis.LargeEvenClassification.RankThreeSubgroupConnectivity
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.Assembly.Dichotomy

open CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers
open CFSG.ProperTwoGeneratedCore

variable {G : Type*} [Group G]

theorem oddCoreSpan_eq_of_rankThreeSubgroupPath
    (hcomplete : ∀ D : Subgroup G, IsElemAbelian 2 D → Nat.card D = 8 → OddCoreSpanCompleted D)
    {A B : Subgroup G} (hAB : RankThreeSubgroupPath A B) : oddCoreSpan A = oddCoreSpan B := by
  obtain ⟨n, path, rfl, rfl, hsteps⟩ := hAB
  have hspan (X : RankThreeVertex G) {T : Subgroup G} (hTX : T ≤ X.val) (hT : 4 ≤ Nat.card T) :
      oddCoreSpan T = oddCoreSpan X.val :=
    oddCoreSpan_eq_of_completed X.val T X.property.1 X.property.2.ge
      (hcomplete X.val X.property.1 X.property.2) hTX hT
  suffices h : ∀ i : Fin (n + 1), oddCoreSpan (path 0).val = oddCoreSpan (path i).val from
    h (Fin.last n)
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    exact ih.trans ((hspan (path i.castSucc) inf_le_left (hsteps i).ge).symm.trans
      (hspan (path i.succ) inf_le_right (hsteps i).ge))

private theorem isElemAbelian_subgroupOf {E K : Subgroup G} (hEK : E ≤ K)
    (hE : IsElemAbelian 2 E) : CFSG.Open.IsElemAbelian 2 (E.subgroupOf K) :=
  CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 2 E (E.subgroupOf K)
    (Subgroup.subgroupOfEquivOfLe hEK).symm hE

private theorem subgroupOf_mem_E3 {E K : Subgroup G} (hEK : E ≤ K) (hE : E ∈ E3 G) :
    E.subgroupOf K ∈ E3 K :=
  ⟨isElemAbelian_subgroupOf hEK hE.1, (rankThree_card_subgroupOf_eq E K hEK).trans hE.2⟩

variable [Finite G]

private theorem exists_mem_E3_le {H : Subgroup G} (h : 3 ≤ pRank 2 H) :
    ∃ E : Subgroup G, E ≤ H ∧ E ∈ E3 G := by
  obtain ⟨F, hFH, hF, hFcard⟩ := pRank_witness (by decide : 1 < 2) H
  have hF8 : 8 ≤ Nat.card F := by
    rw [hFcard]
    exact (Nat.pow_le_pow_right (by decide : 2 > 0) h : 2 ^ 3 ≤ 2 ^ pRank 2 H)
  obtain ⟨E, hEF, hE⟩ := rankThree_vertex_in_elementary F hF hF8
  exact ⟨E, hEF.trans hFH, hE⟩

theorem completedSpanPreparation : CompletedSpanPreparationStatement := by
  intro G _ _ hrank S U hUS hSU hU hUcard hcomplete
  let P : Subgroup G := S
  have hsub {E T : Subgroup G} (hE : E ∈ E3 G) (hTE : T ≤ E) (hT : 4 ≤ Nat.card T) :
      oddCoreSpan T = oddCoreSpan E :=
    oddCoreSpan_eq_of_completed E T hE.1 hE.2.ge (hcomplete E hE.1 hE.2) hTE hT
  have hSrank : 3 ≤ pRank 2 P := by
    have h : pRank 2 P = twoRank G := (CFSG.SectionRank.pRank_sylow S).1
    rw [h]
    exact hrank
  obtain ⟨E₀, hE₀S, hE₀⟩ := exists_mem_E3_le hSrank
  have : (U.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mpr hSU
  obtain ⟨E', hUE', hE', -, hpaths⟩ := rankThree_normal_four_common_vertex S.isPGroup'
    (U.subgroupOf P) (isElemAbelian_subgroupOf hUS hU)
    ((rankThree_card_subgroupOf_eq U P hUS).trans hUcard) (E₀.subgroupOf P)
    (subgroupOf_mem_E3 hE₀S hE₀)
  have hEU : E'.map P.subtype ∈ E3 G :=
    ⟨elementary_map E' hE'.1 P.subtype,
      (Subgroup.card_map_of_injective P.subtype_injective).trans hE'.2⟩
  have hUEU : U ≤ E'.map P.subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hUS).symm.le.trans (Subgroup.map_mono hUE')
  have hWEU : oddCoreSpan U = oddCoreSpan (E'.map P.subtype) := hsub hEU hUEU hUcard.ge
  have hEUc := hcomplete _ hEU.1 hEU.2
  have hodd : Odd (Nat.card (oddCoreSpan U)) := hWEU ▸ hEUc.2.1
  have hspan (E : Subgroup G) (hES : E ≤ S) (hE : IsElemAbelian 2 E) (hEcard : Nat.card E = 8) :
      oddCoreSpan E = oddCoreSpan U := by
    have hpath := rankThree_path_map P.subtype P.subtype_injective
      (hpaths _ (subgroupOf_mem_E3 hES ⟨hE, hEcard⟩))
    rw [Subgroup.map_subgroupOf_eq_of_le hES] at hpath
    exact (oddCoreSpan_eq_of_rankThreeSubgroupPath hcomplete hpath).trans hWEU.symm
  have hfour (V : Subgroup G) (hVS : V ≤ S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
      (hrankV : 3 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G))) :
      oddCoreSpan V = oddCoreSpan U := by
    obtain ⟨E, hEle, hE⟩ := exists_mem_E3_le hrankV
    have hX := commuting_elementary_sup E V hE.1 hV (hEle.trans inf_le_right)
    have hX8 : 8 ≤ Nat.card (E ⊔ V : Subgroup G) := by
      rw [← hE.2]
      exact Subgroup.card_le_of_le le_sup_left
    obtain ⟨EV, hVEV, hEVX, hEV⟩ :=
      rankThree_extend_four_in_elementary (E ⊔ V) V hX hX8 le_sup_right hVcard
    have hEVS : EV ≤ S := hEVX.trans (sup_le (hEle.trans inf_le_left) hVS)
    exact (hsub hEV hVEV hVcard.ge).trans (hspan EV hEVS hEV.1 hEV.2)
  have hnorm (D : Subgroup G) (hDS : D ≤ S) (hrankD : 3 ≤ pRank 2 D) :
      Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (oddCoreSpan U : Set G) := by
    intro g hg
    obtain ⟨E, hED, hE⟩ := exists_mem_E3_le hrankD
    have hDg := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hEg : E.map (MulAut.conj g).toMonoidHom ≤ S := by
      have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hED
      rw [MulEquiv.toMonoidHom_eq_coe, hDg] at h
      exact h.trans hDS
    have h1 := hspan _ hEg (elementary_map E hE.1 _)
      ((Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hE.2)
    have h2 := hspan E (hED.trans hDS) hE.1 hE.2
    have h3 := oddCoreSpan_map (MulAut.conj g) E
    rw [h1, h2, MulEquiv.toMonoidHom_eq_coe] at h3
    exact h3
  refine ⟨hodd, hSU.trans (normalizer_le_oddCoreSpan_normalizer U), ?_, hspan, ?_, hnorm, ?_⟩
  · intro u hu hne
    rw [hWEU]
    exact hEUc.2.2 u (hUEU hu) hne
  · intro V hVS hV hVcard hrankV
    have h := hfour V hVS hV hVcard hrankV
    refine ⟨h, ?_⟩
    rw [← h]
    exact normalizer_le_oddCoreSpan_normalizer V
  · rintro ⟨E, hES, hE, hEcard, hne⟩
    have hW : oddCoreSpan U ≠ ⊥ := hspan E hES hE hEcard ▸ hne
    refine ⟨hW, fun hcore htop => hW ?_⟩
    have hle : oddCoreSpan U ≤ oddCore G :=
      le_sSup ⟨Subgroup.normalizer_eq_top_iff.mp htop, hodd⟩
    rw [hcore] at hle
    exact le_bot_iff.mp hle

end CFSG.Assembly.Dichotomy
