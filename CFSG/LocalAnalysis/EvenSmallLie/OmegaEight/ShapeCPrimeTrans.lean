module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeCone

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem transN_facts (ε : Eps) {v : ℕ} (hv : v < 64)
    (hq : qfB ε v = true) :
    (transN ε v).1 < 64 ∧ (transN ε v).2 < 64 ∧ qfB ε (transN ε v).1 = true ∧
      qfB ε (transN ε v).2 = true ∧ ((transN ε v).1 ^^^ (transN ε v).2) ≠ 0 ∧
      ((transN ε v).1 ^^^ (transN ε v).2) ≠ v ∧
      bfB ε ((transN ε v).1 ^^^ (transN ε v).2) v = false := by
  have h := (cprimeChecks ε).2.2.2.1
  simp only [transNCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  rcases h v hv with h | ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  · rw [hq] at h; exact absurd h (by decide)
  · exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem toVec_ne_zero {z : ℕ} (hz : z < 64) (hz0 : z ≠ 0) : toVec 6 z ≠ 0 := fun h =>
  hz0 (toVec_injective hz (by norm_num) (h.trans (by ext i; simp [toVec])))

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

@[expose] def isomSubgroup (hS : Setting ε t L U Q P a ψ p c v₀) : Subgroup G where
  carrier := {x | x ∈ normalizer (Q : Set G) ∧ ∀ v, qfV ε (lin ψ x v) = qfV ε v}
  one_mem' := ⟨one_mem _, fun v => by rw [hS.rad.lin_one]⟩
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, fun v => by
    rw [hS.rad.lin_mul hx.1 hy.1, hx.2, hy.2]⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, fun v => by
    conv_rhs => rw [← hS.rad.lin_inv hx.1 v]
    rw [hx.2]⟩

theorem qfV_refl (v : V6) :
    qfV ε (toMat 6 6 (reflRows ε v₀) *ᵥ v) = qfV ε v := by
  have h := (cprimeChecks ε).2.1
  simp only [reflQfCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  rcases h v₀ hS.data.v₀_lt with h | h
  · rw [hS.data.v₀_nonsingular] at h; exact absurd h (by decide)
  · rw [mulVec_reflRows ε hS.data.v₀_lt, qfV_toVec ε (reflB_lt ε hS.data.v₀_lt (vecBits_lt v)),
      h _ (vecBits_lt v), qfV]

theorem qfV_lin_of_mem {x : G}
    (hx : x ∈ P ⊔ zpowers c) (v : V6) : qfV ε (lin ψ x v) = qfV ε v := by
  have hle : P ⊔ zpowers c ≤ hS.isomSubgroup := by
    refine sup_le (fun y hy => ⟨hS.rad.P_le_normalizer hy, hS.rad.qfV_lin hy⟩) ?_
    refine zpowers_le.2 ⟨hS.c_mem_normalizer_Q, fun v => ?_⟩
    rw [hS.lin_c, hS.qfV_refl]
  exact (hle hx).2 v

theorem affHom_mem_orthGroup
    {g : Kgrp t Q} (h0 : aff t ψ g 0 = 0) : hS.affHom g ∈ orthGroup ε := by
  have hgt : (g : G) * t = t * g := (hS.aff_zero_eq_zero_iff g.2).1 h0
  have hgP : (g : G) ∈ P ⊔ zpowers c :=
    hS.data.normalizer_E ⟨mem_centralizer_singleton_iff.2 hgt, g.2.1⟩
  refine ⟨fun x y => ?_, fun v => ?_⟩
  · change aff t ψ g (x + y) = aff t ψ g x + aff t ψ g y
    rw [hS.aff_eq_lin g.2 hgt, hS.aff_eq_lin g.2 hgt, hS.aff_eq_lin g.2 hgt,
      hS.rad.lin_add g.2.2]
  · change qfV ε (aff t ψ g v) = qfV ε v
    rw [hS.aff_eq_lin g.2 hgt]
    exact hS.qfV_lin_of_mem hgP v

theorem refl_fix {z : ℕ} (hz : z < 64) (hb : bfB ε z v₀ = false) :
    toMat 6 6 (reflRows ε v₀) *ᵥ toVec 6 z = toVec 6 z := by
  rw [mulVec_reflRows_toVec ε hS.data.v₀_lt hz, reflB, hb]
  simp

theorem false_of_good_translation {z : ℕ} (hz : z < 64)
    (hz0 : z ≠ 0) (hzv : z ≠ v₀) (hb : bfB ε z v₀ = false)
    (hzM : Equiv.addRight (toVec 6 z) ∈ hS.affHom.range) : False := by
  obtain ⟨g, hg⟩ := hzM
  have hgv : ∀ x, aff t ψ g x = x + toVec 6 z := fun x =>
    congrArg (fun σ : Equiv.Perm V6 => σ x) hg
  have hcomm : ∀ x, aff t ψ g (aff t ψ c x) = aff t ψ c (aff t ψ g x) := fun x => by
    rw [hgv, hS.aff_c, hS.aff_c, hgv, mulVec_add, hS.refl_fix hz hb]
  rcases hS.square_root g.2 hcomm with h | h <;> rw [hgv, zero_add] at h
  · exact toVec_ne_zero hz hz0 h
  · exact hzv (toVec_injective hz hS.data.v₀_lt h)

theorem conj_translation {y z : V6} (hy : y ≠ 0) (hz : z ≠ 0)
    (hq : qfV ε y = qfV ε z) (hyM : Equiv.addRight y ∈ hS.affHom.range) :
    Equiv.addRight z ∈ hS.affHom.range := by
  obtain ⟨x, hxP, hxz⟩ := hS.rad.exists_lin_eq hy hz hq
  obtain ⟨g, hg⟩ := hyM
  set xx : Kgrp t Q := ⟨x, hS.P_le_Kgrp hxP⟩
  refine ⟨xx * g * xx⁻¹, Equiv.ext fun v => ?_⟩
  rw [map_mul, map_mul, map_inv, hg]
  change aff t ψ x (aff t ψ x⁻¹ v + y) = v + z
  rw [hS.aff_P hxP, hS.aff_P (inv_mem hxP), hS.rad.lin_add (hS.rad.P_le_normalizer hxP),
    hS.rad.lin_inv (hS.rad.P_le_normalizer hxP), hxz]

theorem false_of_translation
    {y : V6} (hy : y ≠ 0) (hyM : Equiv.addRight y ∈ hS.affHom.range) : False := by
  have hv₀ := hS.data.v₀_lt
  have hq₀ := hS.data.v₀_nonsingular
  rcases qfV_cases ε y with hq | hq
  · obtain ⟨hw, hw0, hwq, hwb, -⟩ := sigma_facts ε hv₀ hq₀
    have hzq : qfV ε (toVec 6 (coneW ε v₀)) = 0 := by rw [qfV_toVec ε hw, hwq, bz_false]
    refine hS.false_of_good_translation hw hw0 (fun h => ?_) hwb
      (hS.conj_translation hy (toVec_ne_zero hw hw0) (hq.trans hzq.symm) hyM)
    rw [h, hq₀] at hwq
    exact absurd hwq (by decide)
  · obtain ⟨h1, h2, hq1, hq2, h0, hv, hb⟩ := transN_facts ε hv₀ hq₀
    have hn : ∀ n, n < 64 → qfB ε n = true → Equiv.addRight (toVec 6 n) ∈ hS.affHom.range := by
      intro n hn hqn
      have hqv : qfV ε (toVec 6 n) = 1 := by rw [qfV_toVec ε hn, hqn, bz_true]
      have hn0 : toVec 6 n ≠ 0 := fun h => by rw [h, qfV_zero] at hqv; exact zero_ne_one hqv
      exact hS.conj_translation hy hn0 (hq.trans hqv.symm) hyM
    have hsum : Equiv.addRight (toVec 6 ((transN ε v₀).1 ^^^ (transN ε v₀).2)) ∈
        hS.affHom.range := by
      have h := mul_mem (hn _ h1 hq1) (hn _ h2 hq2)
      convert h using 1
      refine Equiv.ext fun v => ?_
      simp only [Equiv.coe_addRight, Equiv.Perm.coe_mul, Function.comp_apply, toVec_xor]
      abel
    exact hS.false_of_good_translation (Nat.xor_lt_two_pow (n := 6) h1 h2) h0 hv hb hsum

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime
