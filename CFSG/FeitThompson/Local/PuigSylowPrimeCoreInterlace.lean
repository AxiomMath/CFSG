module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Local.AbelianGeneratedPrimeCoreConstraint
import CFSG.FeitThompson.Local.PuigLimitsStationaryExchange
import CFSG.FeitThompson.Local.PuigSubgroupSameOnContainingSubgroup
import CFSG.FeitThompson.Local.PuigSeriesContainsCentralizer

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem map_puigLambda_le_map_puigLambda_of_map_le {T Sg : Subgroup G} (hTS : T ≤ Sg)
    {W : Subgroup T} {V : Subgroup Sg} (h : V.map Sg.subtype ≤ W.map T.subtype) :
    (puigLambda W).map T.subtype ≤ (puigLambda V).map Sg.subtype := by
  rw [map_le_iff_le_comap]
  refine puigLambda_le fun B hB hW => ?_
  rw [← map_le_iff_le_comap]
  have := hB
  exact le_map_puigLambda_of_le_normalizer ((map_subtype_le B).trans hTS)
    (map_isMulCommutative _ _) (h.trans ((map_mono hW).trans (le_normalizer_map T.subtype)))

theorem map_puigSeries_succ_le_map_puigSeries_succ_of_pCore [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥)
    {T Sg : Subgroup G} (hT : T = pCore p G) (hSp : IsPGroup p Sg) {n : ℕ}
    (hind : (puigSeries T (n + 1)).map T.subtype ≤ (puigSeries Sg (n + 1)).map Sg.subtype) :
    (puigSeries Sg (n + 1 + 1)).map Sg.subtype ≤ (puigSeries T (n + 1 + 1)).map T.subtype := by
  have := Fact.mk hp
  have hTn : T.Normal := by rw [hT]; exact pCore_normal p G
  have hTp : IsPGroup p T := by rw [hT]; exact isPGroup_pCore hp G
  have hPn : ((puigSeries T (n + 1)).map T.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hPp : IsPGroup p ((puigSeries T (n + 1)).map T.subtype) := hTp.to_le (map_subtype_le _)
  have hPC : pCore p G ⊓ centralizer (((puigSeries T (n + 1)).map T.subtype : Subgroup G) : Set G)
      ≤ (puigSeries T (n + 1)).map T.subtype := by
    rw [← hT]
    intro x hx
    obtain ⟨hxT, hxC⟩ := mem_inf.1 hx
    have hmem : (⟨x, hxT⟩ : T) ∈ centralizer ((puigSeries T (n + 1) : Subgroup T) : Set T) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact Subtype.ext (mem_centralizer_iff.1 hxC (a : G) (mem_map_of_mem T.subtype ha))
    exact mem_map_of_mem T.subtype (centralizer_puigSeries_le hp hTp (Nat.le_add_left 1 n) hmem)
  have hnormP : ∀ B : Subgroup Sg, puigSeries Sg (n + 1) ≤ normalizer (B : Set Sg) →
      (puigSeries T (n + 1)).map T.subtype
        ≤ normalizer ((B.map Sg.subtype : Subgroup G) : Set G) := fun B hB =>
    hind.trans ((map_mono hB).trans (le_normalizer_map Sg.subtype))
  have hX : (puigLambda (puigSeries Sg (n + 1))).map Sg.subtype ≤
      sSup ((fun B : Subgroup Sg => B.map Sg.subtype) ''
        {B : Subgroup Sg | IsMulCommutative B ∧
          puigSeries Sg (n + 1) ≤ normalizer (B : Set Sg)}) := by
    rw [map_le_iff_le_comap]
    refine puigLambda_le fun B hB hW => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup ⟨B, ⟨hB, hW⟩, rfl⟩
  have hXT : (puigLambda (puigSeries Sg (n + 1))).map Sg.subtype ≤ T := by
    rw [hT]
    refine le_pCore_of_le_sSup_of_inf_pCore_le hp hGodd hp' hPp hPC ?_ ?_ ?_ hX
    · rintro A ⟨B, ⟨hB, -⟩, rfl⟩
      have := hB
      exact map_isMulCommutative _ _
    · rintro A ⟨B, -, rfl⟩
      exact hSp.to_le (map_subtype_le _)
    · rintro A ⟨B, ⟨-, hW⟩, rfl⟩
      exact hnormP B hW
  rw [puigSeries_succ (X := Sg), puigSeries_succ (X := T), map_le_iff_le_comap]
  refine puigLambda_le fun B hB hW => ?_
  rw [← map_le_iff_le_comap]
  have := hB
  exact le_map_puigLambda_of_le_normalizer ((map_mono (le_puigLambda hB hW)).trans hXT)
    (map_isMulCommutative _ _) (hnormP B hW)

theorem map_puigSeries_pCore_interlace [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥)
    {T Sg : Subgroup G} (hT : T = pCore p G) (hSp : IsPGroup p Sg) (hTS : T ≤ Sg) (n : ℕ) :
    (puigSeries Sg (2 * n)).map Sg.subtype ≤ (puigSeries T (2 * n)).map T.subtype ∧
      (puigSeries T (2 * n + 1)).map T.subtype
        ≤ (puigSeries Sg (2 * n + 1)).map Sg.subtype := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [Nat.mul_zero, Nat.zero_add, puigSeries_one (X := T), puigSeries_one (X := Sg),
      ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, T.range_subtype, Sg.range_subtype]
    exact hTS
  | succ n ih =>
    have heven : (puigSeries Sg (2 * n + 1 + 1)).map Sg.subtype
        ≤ (puigSeries T (2 * n + 1 + 1)).map T.subtype :=
      map_puigSeries_succ_le_map_puigSeries_succ_of_pCore hp hGodd hp' hT hSp ih.2
    have hodd : (puigSeries T (2 * n + 1 + 1 + 1)).map T.subtype
        ≤ (puigSeries Sg (2 * n + 1 + 1 + 1)).map Sg.subtype := by
      rw [puigSeries_succ (X := T), puigSeries_succ (X := Sg)]
      exact map_puigLambda_le_map_puigLambda_of_map_le hTS heven
    exact ⟨by rwa [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring],
      by rwa [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 from by ring]⟩

theorem map_puigLower_le_map_puigLower_pCore [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥)
    {T Sg : Subgroup G} (hT : T = pCore p G) (hSp : IsPGroup p Sg) (hTS : T ≤ Sg) :
    (puigLower Sg).map Sg.subtype ≤ (puigLower T).map T.subtype := by
  obtain ⟨rS, -, hrS⟩ := exists_puigSeries_stationary (Sg : Type _)
  obtain ⟨rT, -, hrT⟩ := exists_puigSeries_stationary (T : Type _)
  have h := (map_puigSeries_pCore_interlace hp hGodd hp' hT hSp hTS (max rS rT)).1
  rwa [(hrS _ (le_max_left rS rT)).1, (hrT _ (le_max_right rS rT)).1] at h

theorem map_puigSubgroup_pCore_le_map_puigSubgroup [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥)
    {T Sg : Subgroup G} (hT : T = pCore p G) (hSp : IsPGroup p Sg) (hTS : T ≤ Sg) :
    (puigSubgroup T).map T.subtype ≤ (puigSubgroup Sg).map Sg.subtype := by
  obtain ⟨rS, -, hrS⟩ := exists_puigSeries_stationary (Sg : Type _)
  obtain ⟨rT, -, hrT⟩ := exists_puigSeries_stationary (T : Type _)
  have h := (map_puigSeries_pCore_interlace hp hGodd hp' hT hSp hTS (max rS rT)).2
  rw [(hrS _ (le_max_left rS rT)).2, (hrT _ (le_max_right rS rT)).2] at h
  rwa [puigSubgroup_eq_puigUpper, puigSubgroup_eq_puigUpper]

theorem puig_pCore_sylow_interlace [Finite G] [Group.IsSolvable G] (hp : p.Prime) (_hpodd : Odd p)
    (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥) (S : Sylow p G) :
    (puigLower (S : Subgroup G)).map (S : Subgroup G).subtype
        ≤ (puigLower (pCore p G)).map (pCore p G).subtype ∧
      (puigLower (pCore p G)).map (pCore p G).subtype
        ≤ (puigSubgroup (pCore p G)).map (pCore p G).subtype ∧
      (puigSubgroup (pCore p G)).map (pCore p G).subtype
        ≤ (puigSubgroup (S : Subgroup G)).map (S : Subgroup G).subtype := by
  refine ⟨map_puigLower_le_map_puigLower_pCore hp hGodd hp' rfl S.isPGroup'
      (pCore_le_sylow hp S), ?_, map_puigSubgroup_pCore_le_map_puigSubgroup hp hGodd hp' rfl
      S.isPGroup' (pCore_le_sylow hp S)⟩
  rw [puigSubgroup_eq_puigUpper]
  exact map_mono puigLower_le_puigUpper

end CFSG.FeitThompson

end
