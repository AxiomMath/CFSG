module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.LinearAlgebra.Dimension.Finrank

import CFSG.GroupTheory.GLnTwoSplitting.Main
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GroupTheory

theorem not_prime_dvd_card_linearEquiv_of_finrank_lt
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {p : ℕ} (hp : p.Prime) (hdim : Module.finrank (ZMod 2) V < orderOf (2 : ZMod p)) :
    ¬ p ∣ Nat.card (V ≃ₗ[ZMod 2] V) := by
  intro hpd
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [h0, orderOf_zero (ZMod 2)] at hdim
    exact Nat.not_lt_zero _ hdim
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpd
  exact CFSG.RankThree.GF2n.Stroth80.orderOf_ne_prime_of_finrank_lt hp hp2 hdim g hg

theorem not_three_pow_four_dvd_card_linearEquiv_of_finrank_le_five
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hdim : Module.finrank (ZMod 2) V ≤ 5) : ¬ 3 ^ 4 ∣ Nat.card (V ≃ₗ[ZMod 2] V) := by
  intro hdvd
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  set d : ℕ := Module.finrank (ZMod 2) V with hd
  have hdle : d ≤ 5 := by rw [hd]; exact hdim
  have hcard : Nat.card (V ≃ₗ[ZMod 2] V) = ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
    rw [CFSG.GroupTheory.GLnTwoSplitting.card_linearEquiv_eq (n := d) (by rw [hd]),
      Matrix.card_GL_field, ZMod.card]
  rw [hcard] at hdvd
  have hnot : ¬ 3 ^ 4 ∣ ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
    interval_cases d <;> decide
  exact hnot hdvd

theorem ker_sup_ker_eq_top_of_dvd_card_of_not_dvd
    {Y T : Type*} [Group Y] [Finite Y] [Group T] [IsSimpleGroup T]
    (π : Y →* T) (hπ : Function.Surjective π)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Y →* (V ≃ₗ[ZMod 2] V)) {n : ℕ} (hT : n ∣ Nat.card T)
    (hV : ¬ n ∣ Nat.card (V ≃ₗ[ZMod 2] V)) : ρ.ker ⊔ π.ker = ⊤ := by
  have hN : (ρ.ker.map π).Normal := (MonoidHom.normal_ker ρ).map π hπ
  rcases Subgroup.Normal.eq_bot_or_eq_top (ρ.ker.map π) with hbot | htop
  ·
    exfalso
    have hle : ρ.ker ≤ π.ker := (Subgroup.map_eq_bot_iff (f := π) ρ.ker).mp hbot
    have hidxT : Nat.card T = π.ker.index := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top]
    have hdvd1 : Nat.card T ∣ ρ.ker.index := by
      rw [hidxT]
      exact Subgroup.index_dvd_of_le hle
    have hidxρ : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
    have hdvd2 : Nat.card ρ.range ∣ Nat.card (V ≃ₗ[ZMod 2] V) :=
      Subgroup.card_subgroup_dvd_card ρ.range
    rw [hidxρ] at hdvd1
    exact hV (hT.trans (hdvd1.trans hdvd2))
  ·
    have hsup : ρ.ker ⊔ π.ker = (⊤ : Subgroup Y) ⊔ π.ker :=
      Subgroup.map_eq_map_iff.mp (show ρ.ker.map π = (⊤ : Subgroup Y).map π by
        rw [htop, Subgroup.map_top_of_surjective π hπ])
    simpa using hsup

end CFSG.GroupTheory
