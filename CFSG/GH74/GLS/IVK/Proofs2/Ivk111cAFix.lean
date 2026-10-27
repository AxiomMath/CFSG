module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem exists_fixed_ne_zero_span {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] {p n : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p ^ n) {W : Type} [AddCommGroup W] [Module L W]
    (T : Multiplicative F →* Module.End L W) {v : W} (hv : v ≠ 0) :
    ∃ w ∈ Submodule.span L (Set.range fun b => T b v), w ≠ 0 ∧ ∀ b, T b w = w := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : Module F W := Module.compHom W (algebraMap F L)
  have : IsScalarTower F L W := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  set S : Submodule F W := Submodule.span F (Set.range fun b => T b v) with hS
  have hvS : v ∈ S := Submodule.subset_span ⟨1, by simp⟩
  have hstab : ∀ (b : Multiplicative F), ∀ s ∈ S, T b s ∈ S := by
    intro b s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b', rfl⟩ := hx
      exact Submodule.subset_span ⟨b * b', by simp [map_mul]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul a x _ hx =>
      have h : T b (a • x) = a • T b x := by
        show T b ((algebraMap F L a) • x) = (algebraMap F L a) • T b x
        exact map_smul (T b) _ _
      rw [h]
      exact S.smul_mem a hx
  have : Module.Finite F S := Module.Finite.span_of_finite F (Set.finite_range _)
  have : Finite S := Module.finite_of_finite F
  let : SMul (Multiplicative F) S := ⟨fun b s => ⟨T b s.1, hstab b s.1 s.2⟩⟩
  have hsmul : ∀ (b : Multiplicative F) (s : S), ((b • s : S) : W) = T b s := fun _ _ => rfl
  let : MulAction (Multiplicative F) S :=
    { one_smul := fun s => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun a b s => Subtype.ext (by rw [hsmul, hsmul, hsmul]; simp [map_mul]) }
  have hU : IsPGroup p (Multiplicative F) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)]; exact hF)
  have hmod := hU.card_modEq_card_fixedPoints S
  have hn : n ≠ 0 := by
    rintro rfl
    have : 1 < Nat.card F := Finite.one_lt_card
    rw [pow_zero] at hF
    omega
  have : Nontrivial S := ⟨⟨⟨v, hvS⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hdvd : p ∣ Nat.card S := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF, ← pow_mul]
    exact dvd_pow_self p (Nat.mul_ne_zero hn (Module.finrank_pos (R := F) (M := S)).ne')
  have hdvd' : p ∣ Nat.card (MulAction.fixedPoints (Multiplicative F) S) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  have hzero : (0 : S) ∈ MulAction.fixedPoints (Multiplicative F) S := by
    intro b
    exact Subtype.ext (by rw [hsmul]; simp)
  have hpos : 0 < Nat.card (MulAction.fixedPoints (Multiplicative F) S) := by
    have : Nonempty (MulAction.fixedPoints (Multiplicative F) S) := ⟨⟨0, hzero⟩⟩
    exact Nat.card_pos
  have hone : 1 < Nat.card (MulAction.fixedPoints (Multiplicative F) S) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdvd')
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := (Finite.one_lt_card_iff_nontrivial.mp hone).exists_pair_ne
  have hab' : a ≠ b := fun h => hab (Subtype.ext h)
  have hmem : ∀ s : S, (s : W) ∈ Submodule.span L (Set.range fun b => T b v) := fun s =>
    Submodule.span_le_restrictScalars F L _ s.2
  by_cases ha0 : a = 0
  · refine ⟨b, hmem b, fun hb0 => hab' (ha0.trans (Subtype.ext hb0).symm), fun g => ?_⟩
    have := congrArg Subtype.val (hb g)
    rwa [hsmul] at this
  · refine ⟨a, hmem a, fun h => ha0 (Subtype.ext h), fun g => ?_⟩
    have := congrArg Subtype.val (ha g)
    rwa [hsmul] at this

end CFSG.GH74.GLS.Stage4.Rest
