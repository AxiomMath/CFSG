module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Basics
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct4
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3s_bar_normal_eq_bot_or_eq_top {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsU3Normal M x J) (N : Subgroup ↥(r1sBar x J)) (hN : N.Normal) : N = ⊥ ∨ N = ⊤ := by
  have hJC := hJ.le_centralizer
  have hsurj := r1sHom_surjective x hJC
  have hker := ker_r1sHom_u3 hJ
  set N' : Subgroup ↥J := N.comap (r1sHom x hJC) with hN'
  have hN'n : N'.Normal := hN.comap _
  set NG : Subgroup G := N'.map J.subtype with hNG
  have hsub : NG.subgroupOf J = N' :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective N'
  have hmemNG : ∀ j : ↥J, (j : G) ∈ NG ↔ r1sHom x hJC j ∈ N := by
    intro j
    constructor
    · rintro ⟨j', hj', hjj'⟩
      have : j' = j := Subtype.ext hjj'
      subst this
      exact hj'
    · intro h
      exact ⟨j, h, rfl⟩
  have hcoreJ : rankThreePrimeCore 3 J ≤ J := hJ.lt_core.le
  have hmemker : ∀ j : ↥J, (j : G) ∈ rankThreePrimeCore 3 J → r1sHom x hJC j = 1 := by
    intro j hj
    have hjk : j ∈ (r1sHom x hJC).ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr hj
    exact MonoidHom.mem_ker.mp hjk
  have hcoreN : rankThreePrimeCore 3 J ≤ NG := by
    intro g hg
    refine (hmemNG ⟨g, hcoreJ hg⟩).mpr ?_
    rw [hmemker ⟨g, hcoreJ hg⟩ hg]
    exact N.one_mem
  rcases hJ.minimal NG (Subgroup.map_subtype_le N') (hsub ▸ hN'n) hcoreN with h | h
  · left
    refine eq_bot_iff.mpr fun n hn => ?_
    obtain ⟨j, rfl⟩ := hsurj n
    have hj : (j : G) ∈ NG := (hmemNG j).mpr hn
    rw [h] at hj
    exact (Subgroup.mem_bot).mpr (hmemker j hj)
  · right
    refine eq_top_iff.mpr fun n _ => ?_
    obtain ⟨j, rfl⟩ := hsurj n
    have hj : (j : G) ∈ NG := by
      rw [h]
      exact j.2
    exact (hmemNG j).mp hj

theorem u3s_bar_center_eq_bot {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsU3Normal M x J) : center ↥(r1sBar x J) = ⊥ := by
  rcases u3s_bar_normal_eq_bot_or_eq_top hJ (center _) inferInstance with h | h
  · exact h
  · exfalso
    have hJC := hJ.le_centralizer
    have := r1sBar_perfect_u3 hJ
    have : IsMulCommutative ↥(r1sBar x J) := ⟨⟨fun a b =>
      mem_center_iff.mp (show b ∈ center ↥(r1sBar x J) from h ▸ mem_top b) a⟩⟩
    have hsub : Subsingleton ↥(r1sBar x J) := inferInstance
    refine hJ.lt_core.not_ge fun g hg => ?_
    have hk : (⟨g, hg⟩ : ↥J) ∈ (r1sHom x hJC).ker :=
      MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
    rw [ker_r1sHom_u3 hJ] at hk
    exact Subgroup.mem_subgroupOf.mp hk

theorem u3s_sylow_centralizer_cyclic {Y : Type} [Group Y] [Finite Y] {S : Sylow 3 Y}
    (hrk : CFSG.Open.pRank 3 (S : Subgroup Y) ≤ 3) {Lb D : Subgroup Y} [Lb.Normal]
    (hD : D = centralizer (Lb : Set Y)) (hLD : Lb ⊓ D = ⊥)
    (hL : ∀ T : Sylow 3 Lb, ∃ E : Subgroup Lb, E ≤ T ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2)
    (T : Sylow 3 D) : IsCyclic ↥(T : Subgroup D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDn : D.Normal := by rw [hD]; infer_instance
  have hDc : ∀ c ∈ D, ∀ l ∈ Lb, l * c = c * l := fun c hc l hl =>
    mem_centralizer_iff.mp (by rwa [hD] at hc) l hl
  have hSY : IsSylowOf 3 (S : Subgroup Y) ⊤ := (isSylowOf_iff).mpr
    ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hSL : IsSylowOf 3 ((S : Subgroup Y) ⊓ Lb) Lb :=
    hSY.inf_of_le_normalizer le_top (normalizer_eq_top Lb).ge
  have hSD : IsSylowOf 3 ((S : Subgroup Y) ⊓ D) D :=
    hSY.inf_of_le_normalizer le_top (normalizer_eq_top D).ge
  obtain ⟨Q, hQ⟩ := hSL
  obtain ⟨E₀, hE₀Q, hE₀e, hE₀c⟩ := hL Q
  have hE₁ : IsElemAbelian 3 (E₀.map Lb.subtype) := r1s_isElemAbelian_map Lb.subtype hE₀e
  have hE₁c : Nat.card (E₀.map Lb.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective Lb.subtype_injective, hE₀c]
  have hE₁S : E₀.map Lb.subtype ≤ (S : Subgroup Y) ⊓ Lb := by
    rw [← hQ]
    exact Subgroup.map_mono hE₀Q
  obtain ⟨Q', hQ'⟩ := hSD
  have hSDc : IsCyclic ↥((S : Subgroup Y) ⊓ D) := by
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num)
      S.isPGroup'.to_inf_left hnc
    obtain ⟨E, hEle, hE, hEc⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three ((S : Subgroup Y) ⊓ D)
    have hsum := add_le_pRank_of_commute (P := (S : Subgroup Y)) hE₁ hE hE₁c hEc
      (fun a ha b hb => hDc b (hEle hb).2 a (hE₁S ha).2)
      (by
        rw [disjoint_iff, eq_bot_iff]
        intro c hc
        have : c ∈ Lb ⊓ D := ⟨(hE₁S hc.1).2, (hEle hc.2).2⟩
        rwa [hLD] at this)
      (hE₁S.trans inf_le_left) (hEle.trans inf_le_left)
    omega
  have hcQ' : IsCyclic ↥(Q' : Subgroup D) := by
    let e : ↥(Q' : Subgroup D) ≃* ↥((S : Subgroup Y) ⊓ D) :=
      (Q'.equivMapOfInjective D.subtype D.subtype_injective).trans (MulEquiv.subgroupCongr hQ')
    have := hSDc
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have := hcQ'
  exact isCyclic_of_surjective (Q'.equiv T) (Q'.equiv T).surjective

end CFSG.LocalAnalysis.RankThreeTheoremC
