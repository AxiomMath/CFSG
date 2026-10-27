module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.OfModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Main
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Quasithin CFSG.EvenSmallLie CFSG.EvenSmallLie.UnitarySix
  CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem index_inner_eq_two
    (hQ : IsSporadic (L ⧸ center L) .Fi22) :
    ((MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range).index = 2 := by
  obtain ⟨e⟩ := hQ
  have hc : Nat.card (Outer (L ⧸ center L)) = 2 := by
    rw [CFSG.LieType.SteinbergBR.OddSylow.card_outer_congr e]
    exact CFSG.RankThree.PartOne.card_outer_fi22_carrier
  exact hc

theorem relIndex_sup_centralizer_le_two
    (h : StdHyp G L) (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (L ⊔ centralizer (L : Set G)).relIndex (centralizer ({t} : Set G)) ≤ 2 := by
  have hdvd := h.relIndex_sup_centralizer_dvd ht ht2
  rw [index_inner_eq_two hQ] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem spine
    (h : StdHyp G L) (h2 : Nat.card (center L) = 2)
    (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G} (ht : (center L).map L.subtype = zpowers t)
    {E' : Subgroup L} (M : LocalModel L E') :
    centralizer (L : Set G) = zpowers t ∧
      ∃ n ∈ normalizer ((E'.map L.subtype : Subgroup G) : Set G), n⁻¹ * t * n ≠ t := by
  have := h.simple
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center h2 ht
  have htZ : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  obtain ⟨htC, hCc, hC2, -, -, -, -⟩ := std_center_facts h.toStandardSetting ht2 htZ
  have hout := relIndex_sup_centralizer_le_two h hQ htC ht2
  have D := Facts.of_localModel h ht2 htZ M hout
  exact ⟨D.centralizer_eq_zpowers h.nonabelian ht2 hCc hC2 htC
    (centralizer_le_of_localModel h ht2 htZ M), D.exists_normalizer_conj_ne h.nonabelian ht2⟩

theorem exists_surjective_automizer
    (h : StdHyp G L) (h2 : Nat.card (center L) = 2)
    (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G} (ht : (center L).map L.subtype = zpowers t)
    {E' : Subgroup L} (M : LocalModel L E') (hne : centralizer ({t} : Set G) ≠ L) :
    ∃ θ : centralizer ({t} : Set G) →* MulAut (L ⧸ center L), Function.Surjective θ ∧
      θ.ker = (zpowers t).subgroupOf (centralizer ({t} : Set G)) := by
  have := h.simple
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center h2 ht
  have htZ : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  obtain ⟨hCL, -⟩ := spine h h2 hQ ht M
  obtain ⟨-, -, -, -, -, hLt, -⟩ := std_center_facts h.toStandardSetting ht2 htZ
  have htL : t ∈ L := by
    obtain ⟨z, -, rfl⟩ := htZ
    exact z.2
  have hLF : L ⊔ centralizer (L : Set G) = L := by
    rw [hCL]
    exact sup_eq_left.2 (zpowers_le.2 htL)
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := std_automizer_embedding h.toStandardSetting ht2 htZ
  refine ⟨θ, ?_, ?_⟩
  · set I := (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range with hI
    have hIR : I ≤ θ.range := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨⟨(l : G), hLt l.2⟩, ?_⟩
      ext x
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      have := hθ1 ⟨(l : G), hLt l.2⟩ x (l * x * l⁻¹) (by simp)
      rw [this]
      simp [MulAut.conj_apply]
    obtain ⟨g, hgH, hgL⟩ : ∃ g ∈ centralizer ({t} : Set G), g ∉ L := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hcon hLt)
    have hgR : θ ⟨g, hgH⟩ ∈ θ.range := ⟨⟨g, hgH⟩, rfl⟩
    have hgI : θ ⟨g, hgH⟩ ∉ I := by
      rintro ⟨q, hq⟩
      exact hgL (hLF ▸ (hθ3 ⟨g, hgH⟩).1 ⟨q, hq.symm⟩)
    have hrel := Subgroup.relIndex_mul_index hIR
    rw [index_inner_eq_two hQ] at hrel
    have hne1 : I.relIndex θ.range ≠ 1 := fun h1 =>
      hgI (Subgroup.relIndex_eq_one.1 h1 hgR)
    have hne0 : I.relIndex θ.range ≠ 0 := relIndex_ne_zero_of_finite _ _
    have hidx : θ.range.index = 1 := by
      have h0 : θ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : 2 * θ.range.index ≤ 2 :=
        calc 2 * θ.range.index ≤ I.relIndex θ.range * θ.range.index :=
              Nat.mul_le_mul_right _ (by omega)
          _ = 2 := hrel
      omega
    rw [Subgroup.index_eq_one] at hidx
    intro y
    have hy : y ∈ θ.range := by
      rw [hidx]
      exact mem_top y
    exact hy
  · ext g
    rw [MonoidHom.mem_ker, hθ2, mem_subgroupOf, hCL]

theorem centralizer_eq_of_localModel
    (h : StdHyp G L) (h2 : Nat.card (center L) = 2)
    (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G} (ht : (center L).map L.subtype = zpowers t)
    {E' : Subgroup L} (M : LocalModel L E') :
    centralizer ((E'.map L.subtype : Subgroup G) : Set G) = E'.map L.subtype := by
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center h2 ht
  have htZ : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  obtain ⟨hCL, -⟩ := spine h h2 hQ ht M
  have htE : t ∈ E'.map L.subtype := by
    obtain ⟨z, hz, rfl⟩ := htZ
    exact ⟨z, M.center_le hz, rfl⟩
  apply le_antisymm
  · intro c hc
    have := centralizer_le_of_localModel h ht2 htZ M hc
    rwa [hCL, sup_eq_left.2 (zpowers_le.2 htE)] at this
  · intro e he x hx
    have D := Facts.of_localModel h ht2 htZ M
      (relIndex_sup_centralizer_le_two h hQ (std_center_facts h.toStandardSetting ht2 htZ).1 ht2)
    exact D.E_comm x hx e he

theorem exists_outer_normalizer
    (h : StdHyp G L) (h2 : Nat.card (center L) = 2)
    (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G} (ht : (center L).map L.subtype = zpowers t)
    {E' : Subgroup L} (M : LocalModel L E') (hne : centralizer ({t} : Set G) ≠ L) :
    ∃ n ∈ normalizer ((E'.map L.subtype : Subgroup G) : Set G),
      n ∈ centralizer ({t} : Set G) ∧ n ∉ L := by
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center h2 ht
  have htZ : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  have hout := relIndex_sup_centralizer_le_two h hQ
    (std_center_facts h.toStandardSetting ht2 htZ).1 ht2
  have D := Facts.of_localModel h ht2 htZ M hout
  obtain ⟨g, hgH, hgL⟩ : ∃ g ∈ centralizer ({t} : Set G), g ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hcon D.le_centralizer)
  obtain ⟨l, hl, n, hn, rfl⟩ := D.exists_eq_mul hgH
  refine ⟨n, hn, ?_, fun hnL => hgL (mul_mem hl hnL)⟩
  have : n = l⁻¹ * (l * n) := by group
  rw [this]
  exact mul_mem (inv_mem (D.le_centralizer hl)) hgH

end CFSG.EvenSporadicStandard.TwoFi22.DS81
