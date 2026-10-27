module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Basics

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l28s_bar_normal_eq_bot_or_eq_top {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsL28Normal M x J) (N : Subgroup ↥(r1sBar x J)) (hN : N.Normal) : N = ⊥ ∨ N = ⊤ := by
  have hJC := hJ.le_centralizer
  have hsurj := r1sHom_surjective x hJC
  have hker := ker_r1sHom_l28 hJ
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

theorem l28s_bar_center_eq_bot {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsL28Normal M x J) : center ↥(r1sBar x J) = ⊥ := by
  rcases l28s_bar_normal_eq_bot_or_eq_top hJ (center _) inferInstance with h | h
  · exact h
  · exfalso
    have hJC := hJ.le_centralizer
    have := r1sBar_perfect_l28 hJ
    have : IsMulCommutative ↥(r1sBar x J) := ⟨⟨fun a b =>
      mem_center_iff.mp (show b ∈ center ↥(r1sBar x J) from h ▸ mem_top b) a⟩⟩
    have hsub : Subsingleton ↥(r1sBar x J) := inferInstance
    refine hJ.lt_core.not_ge fun g hg => ?_
    have hk : (⟨g, hg⟩ : ↥J) ∈ (r1sHom x hJC).ker :=
      MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
    rw [ker_r1sHom_l28 hJ] at hk
    exact Subgroup.mem_subgroupOf.mp hk

end CFSG.LocalAnalysis.RankThreeTheoremC
