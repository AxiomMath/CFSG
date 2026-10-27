module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.LinearAlgebra.Dimension.Finrank

import CFSG.GroupTheory.GLnTwoSplitting.Main
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Lift
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

theorem not_three_pow_five_dvd_card_linearEquiv_of_finrank_le_seven
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hdim : Module.finrank (ZMod 2) V ≤ 7) : ¬ 3 ^ 5 ∣ Nat.card (V ≃ₗ[ZMod 2] V) := by
  intro hdvd
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  set d : ℕ := Module.finrank (ZMod 2) V with hd
  have hdle : d ≤ 7 := by rw [hd]; exact hdim
  have hcard : Nat.card (V ≃ₗ[ZMod 2] V) = ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
    rw [CFSG.GroupTheory.GLnTwoSplitting.card_linearEquiv_eq (n := d) (by rw [hd]),
      Matrix.card_GL_field, ZMod.card]
  rw [hcard] at hdvd
  have hnot : ¬ 3 ^ 5 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
    interval_cases d <;> decide
  exact hnot hdvd

theorem injective_of_ker_inf_center_eq_bot {X T : Type*} [Group X] [Group T] (π : X →* T)
    (hperf : commutator X = ⊤) (hs : IsSimpleGroup (X ⧸ Subgroup.center X))
    (hπ : π.ker ≠ ⊤) (hZ : π.ker ⊓ Subgroup.center X = ⊥) : Function.Injective π := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have : ((π.ker).map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal ((π.ker).map (QuotientGroup.mk' (Subgroup.center X))) with
    h | h
  · have hle : π.ker ≤ Subgroup.center X := by
      intro k hk
      have hmem : (QuotientGroup.mk' (Subgroup.center X)) k ∈
          (π.ker).map (QuotientGroup.mk' (Subgroup.center X)) :=
        Subgroup.mem_map_of_mem _ hk
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    exact (inf_eq_left.mpr hle).symm.trans hZ
  · refine absurd ?_ hπ
    refine CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_top_of_sup_center_eq_top
      hperf ?_
    rw [← QuotientGroup.ker_mk' (Subgroup.center X), ← Subgroup.comap_map_eq, h,
      Subgroup.comap_top]

end CFSG.GroupTheory
