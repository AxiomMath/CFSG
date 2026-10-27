module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_sylow_growth {G : Type} [Group G] [Finite G] {t : G} {T : Subgroup G}
    (hT : IsPGroup 2 T) (htT : t ∈ T)
    (hR : IsSylow2Of (T ⊓ centralizer ({t} : Set G)) (centralizer ({t} : Set G)))
    (hfus : ∀ u ∈ T, IsConj t u → ∃ a ∈ T, u = a * t * a⁻¹) : IsSylow2Of T ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  have hTQeq : T = Q := by
    by_contra hne
    have hHlt : T.subgroupOf Q < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
      refine le_antisymm hTQ fun x hx => ?_
      have hx' : (⟨x, hx⟩ : Q) ∈ T.subgroupOf Q := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp hx'
    haveI : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
    have hnc : NormalizerCondition Q := Group.normalizerCondition_of_isNilpotent
    obtain ⟨g, hgN, hgH⟩ := IsConcreteLE.exists_of_lt (hnc _ hHlt)
    have hg_norm : (g : G) ∈ Subgroup.normalizer T := by
      have h : g ∈ (Subgroup.normalizer T).subgroupOf Q := by
        rw [Subgroup.subgroupOf_normalizer_eq hTQ]
        exact hgN
      exact Subgroup.mem_subgroupOf.mp h
    have hg_not_T : (g : G) ∉ T := by
      intro hgT
      exact hgH (Subgroup.mem_subgroupOf.mpr hgT)
    have hconjT : (g : G) * t * (g : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hg_norm t).mp htT
    have hconj : IsConj t ((g : G) * t * (g : G)⁻¹) := isConj_iff.mpr ⟨(g : G), rfl⟩
    obtain ⟨u, huT, hu⟩ := hfus ((g : G) * t * (g : G)⁻¹) hconjT hconj
    let b : G := u⁻¹ * (g : G)
    have hb_conj : b * t * b⁻¹ = t := by
      have h1 : b * t * b⁻¹ = u⁻¹ * ((g : G) * t * (g : G)⁻¹) * u := by
        simp only [b]; group
      rw [h1, hu]; group
    have hbC : b ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp hb_conj
    have hbQ : b ∈ Q := by
      simp only [b]
      exact Q.mul_mem (Q.inv_mem (hTQ huT)) g.2
    have hb_not_T : b ∉ T := by
      intro hbT
      apply hg_not_T
      have : (g : G) = u * b := by simp only [b]; group
      rw [this]
      exact T.mul_mem huT hbT
    set C : Subgroup G := Subgroup.centralizer ({t} : Set G)
    set R' : Subgroup G := (T ⊓ C) ⊔ Subgroup.zpowers b
    have hR'C : R' ≤ C := sup_le inf_le_right (Subgroup.zpowers_le.mpr hbC)
    have hR'Q : R' ≤ Q := sup_le (inf_le_left.trans hTQ) (Subgroup.zpowers_le.mpr hbQ)
    have hR'pg : IsPGroup 2 R' := Q.isPGroup'.to_le hR'Q
    obtain ⟨P, hP⟩ := hR.exists_sylow
    have hR'pg_sub : IsPGroup 2 ↥(R'.subgroupOf C) :=
      hR'pg.of_equiv (Subgroup.subgroupOfEquivOfLe hR'C).symm
    have hPle : (P : Subgroup ↥C) ≤ R'.subgroupOf C := by
      intro x hx
      have hx' : C.subtype x ∈ T ⊓ C := by
        rw [← hP]
        exact ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_left hx'
    have hR'eq : R' = T ⊓ C := by
      calc R' = (R'.subgroupOf C).map C.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hR'C).symm
        _ = ((P : Subgroup ↥C)).map C.subtype := by rw [P.is_maximal' hR'pg_sub hPle]
        _ = T ⊓ C := hP
    have hbR' : b ∈ R' := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    exact hb_not_T (by rw [hR'eq] at hbR'; exact hbR'.1)
  refine ⟨le_top, hT, ?_⟩
  rw [Subgroup.relIndex_top_right, hTQeq]
  exact Q.not_dvd_index

end CFSG.OddStandard.SmallF3.Omega
