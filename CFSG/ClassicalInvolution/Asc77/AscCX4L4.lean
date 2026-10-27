module

public import CFSG.ClassicalInvolution.Asc77.AscCX4A
public import CFSG.ClassicalInvolution.Asc77.AscCX4L3

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem eq_one_or_neg_one_of_pow_four (hsq : ¬ IsSquare (-1 : F)) {c : F} (hc : c ^ 4 = 1) :
    c = 1 ∨ c = -1 := by
  have h1 : (c ^ 2 - 1) * (c ^ 2 + 1) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp h1 with h | h
  · have h' : (c - 1) * (c + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl (by linear_combination h'')
    · exact Or.inr (by linear_combination h'')
  · exact absurd ⟨c, by linear_combination -h⟩ hsq

theorem twin_data {Y : Type} [Group Y] (h2 : (2 : F) ≠ 0) (ψ : SL(4, F) →* Y)
    (hker : ψ.ker ≤ Subgroup.center SL(4, F)) {R : Subgroup SL(4, F)} {i : SL(4, F)}
    (hi : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R i) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') : i ∈ R ∧ i * i = 1 ∧ i ≠ 1 ∧ ψ i = z' := by
  have hcl := hi.isClassicalSL2 h2
  have hio := hcl.orderOf_eq_two
  have hi2 : i * i = 1 := by
    have := pow_orderOf_eq_one i
    rwa [hio, sq] at this
  have hi1 : i ≠ 1 := fun h => by rw [h, orderOf_one] at hio; omega
  refine ⟨hcl.mem, hi2, hi1, ?_⟩
  rcases hz.unique (ψ i) ⟨i, hcl.mem, rfl⟩ (by rw [← map_mul, hi2, map_one]) with h | h
  · exact absurd (eq_one_of_mem_longRoot_of_mem_center hi hcl.mem (hker h)) hi1
  · exact h

theorem ker_eq_scalars {Y : Type} [Group Y] (h2 : (2 : F) ≠ 0) (hsq : ¬ IsSquare (-1 : F))
    (ψ : SL(4, F) →* Y) (hker : ψ.ker ≤ Subgroup.center SL(4, F)) {R R' : Subgroup SL(4, F)}
    {i i' : SL(4, F)} (hi : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R i)
    (hi' : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R' i') (hne : R ≠ R') {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    ψ.ker = scalars 4 F := by
  obtain ⟨-, -, -, hψi⟩ := twin_data h2 ψ hker hi hz
  obtain ⟨-, -, -, hψi'⟩ := twin_data h2 ψ hker hi' hz'
  have hck : i' * i⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel]
  have hc1 : i' * i⁻¹ ≠ 1 := by
    intro h
    apply hne
    rw [hi.eq_longRootGroup h2, hi'.eq_longRootGroup h2, mul_inv_eq_one.mp h]
  obtain ⟨d, hd4, hd⟩ := mem_scalars.mp ((scalars_eq_center 4 F).ge (hker hck))
  have hd1 : (d : F) = -1 := by
    rcases eq_one_or_neg_one_of_pow_four hsq (show (d : F) ^ 4 = 1 by
      rw [← Units.val_pow_eq_pow_val, hd4, Units.val_one]) with h | h
    · exfalso
      apply hc1
      apply Subtype.ext
      rw [hd, h, Matrix.SpecialLinearGroup.coe_one]
      simp
    · exact h
  refine le_antisymm (hker.trans (scalars_eq_center 4 F).ge) fun x hx => ?_
  obtain ⟨c, hc4, hc⟩ := mem_scalars.mp hx
  rcases eq_one_or_neg_one_of_pow_four hsq (show (c : F) ^ 4 = 1 by
      rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]) with h | h
  · have hx1 : x = 1 := by
      apply Subtype.ext
      rw [hc, h, Matrix.SpecialLinearGroup.coe_one]
      simp
    rw [hx1]
    exact Subgroup.one_mem _
  · have hxe : x = i' * i⁻¹ := by
      apply Subtype.ext
      rw [hc, hd, h, hd1]
    rw [hxe]
    exact hck

theorem layerTwinFacts_psl4 [Finite F] (h2 : (2 : F) ≠ 0) (hsq : ¬ IsSquare (-1 : F))
    {Y : Type} [Group Y] (ψ : SL(4, F) →* Y) (hker : ψ.ker ≤ Subgroup.center SL(4, F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') :
    LayerTwinFacts (R.map ψ) (R'.map ψ) z' := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hRR : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨hiR, hi2, hi1, hψi⟩ := twin_data h2 ψ hker hi hz
  obtain ⟨hi'R, hi'2, hi'1, hψi'⟩ := twin_data h2 ψ hker hi' hz'
  have hc : i' * i⁻¹ ∈ Subgroup.center SL(4, F) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hig⟩ := twin_std h2 ⟨i, hi⟩ ⟨i', hi'⟩ hRR hiR hi2 hi1 hi'R hi'2 hi'1 hc
  have hk := ker_eq_scalars h2 hsq ψ hker hi hi' hRR hz hz'
  set e : projectiveSL 4 F ≃* Y := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with he
  have hep : ∀ s, e (proj 4 F s) = ψ s := fun s => rfl
  set e' : projectiveSL 4 F ≃* Y := (MulAut.conj (proj 4 F g)).trans e with he'
  have he'p : ∀ s, e' (proj 4 F s) = ψ (g * s * g⁻¹) := fun s => by
    show e (proj 4 F g * proj 4 F s * (proj 4 F g)⁻¹) = _
    rw [← map_inv, ← map_mul, ← map_mul, hep]
  have hcomp : ψ.comp (MulAut.conj g).toMonoidHom = e'.toMonoidHom.comp (proj 4 F) := by
    ext s
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [he'p]
  have hA : R.map ψ = A0.map e'.toMonoidHom := by
    rw [hRg, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  have hA' : R'.map ψ = A2.map e'.toMonoidHom := by
    rw [hR'g, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  have hzz : z' = e' zbar := by
    rw [← hψi, hig, zbar, he'p]
  have hcen : Subgroup.center Y = ⊥ := CX4.center_eq_bot_of_mulEquiv e
    (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 4) (k := F) (by norm_num))
  have hO := oddCoreOf_map_longRoot_eq_bot h2 ψ hker hi
  have hO' := oddCoreOf_map_longRoot_eq_bot h2 ψ hker hi'
  rw [hA, hA', hzz] at *
  exact CX4.layerTwinFacts_map_of e' hcen hO hO' (fix_pgroup_std h2 hsq) (fix_invol_std h2 hsq)

end CFSG.ClassicalInvolution.Asc77.CX.CX4.L4
