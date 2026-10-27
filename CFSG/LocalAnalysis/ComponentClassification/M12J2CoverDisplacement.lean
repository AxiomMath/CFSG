module

public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusion
public import Certificates.Certificate10026
import CFSG.LocalAnalysis.ComponentClassification.M12CoverRigid
import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsCocycle

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

variable {Q : Type*} [Group Q] {f : NormCocycle Q}

theorem CocycleExtension.commutator_mk_of_commute {x y : Q} (hxy : x * y = y * x)
    (a b : ZMod 2) :
    (⟨a, x⟩ : CocycleExtension f)⁻¹ * (⟨b, y⟩ : CocycleExtension f)⁻¹ * ⟨a, x⟩ * ⟨b, y⟩ =
      ⟨f x y + f y x, 1⟩ := by
  set A : CocycleExtension f := ⟨a, x⟩
  set B : CocycleExtension f := ⟨b, y⟩
  set C : CocycleExtension f := ⟨f x y + f y x, 1⟩
  have hC : C ∈ center (CocycleExtension f) := CocycleExtension.mem_center_of_snd_eq_one rfl
  have hAB : A * B = C * (B * A) := by
    rw [CocycleExtension.mk_mul_mk, CocycleExtension.mk_mul_mk, CocycleExtension.mk_mul_mk]
    have h1 : f 1 (y * x) = 0 := f.map_one_left (y * x)
    rw [h1, hxy, one_mul]
    congr 1
    show a + b + f x y = f x y + f y x + (b + a + f y x) + 0
    generalize f x y = u
    generalize f y x = v
    revert a b u v
    decide
  calc A⁻¹ * B⁻¹ * A * B = (B * A)⁻¹ * (A * B) := by group
    _ = (B * A)⁻¹ * (C * (B * A)) := by rw [hAB]
    _ = C := by
      rw [← mul_assoc, mem_center_iff.mp hC, mul_assoc, inv_mul_cancel, mul_one]

end CFSG.ComponentClassification.CentralCover

namespace CFSG.ComponentClassification.M12Cover

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CentralCover InternalSylow

theorem m12_pair_displacement :
    ∃ x y : Blueprint.NativeSporadic.M12, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y ∧
      x * y = y * x ∧
      ∀ (E : Type) [Group E] [Finite E], Assembly.IsQuasisimple E → ∀ t : E, orderOf t = 2 →
        center E = zpowers t → ∀ ρ : E →* Blueprint.NativeSporadic.M12,
          Function.Surjective ρ → ρ.ker = zpowers t →
          ∀ X Y : E, ρ X = x → ρ Y = y → X⁻¹ * Y⁻¹ * X * Y = t := by
  have hm88 : mTab 8 8 = 0 := by decide +kernel
  have hm2020 : mTab 20 20 = 0 := by decide +kernel
  have hm820 : mTab 8 20 = mTab 20 8 := by decide +kernel
  have hsq : ∀ j : Fin 64, mTab j j = 0 → j ≠ 0 → orderOf (d j : NativeSporadic.M12) = 2 := by
    intro j hj hj0
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← Subgroup.coe_mul, ← d_mul, hj, d_zero, Subgroup.coe_one]
    · intro h1
      apply hj0
      apply d_injective
      rw [d_zero]
      exact Subtype.ext h1
  refine ⟨d 8, d 20, hsq 8 hm88 (by decide), hsq 20 hm2020 (by decide), ?_, ?_, ?_⟩
  · intro h
    exact absurd (d_injective (Subtype.ext h)) (by decide)
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← d_mul, ← d_mul, hm820]
  intro E _ _ hEq t ht hZ ρ hρ hker X Y hX hY
  have : Group.IsPerfect E := (Group.isPerfect_def).2 hEq.1
  have hπ : IsCentralDoubleExt ρ t := ⟨hρ, hZ ▸ mem_zpowers t, ht, hker⟩
  obtain ⟨-, h4, h0⟩ := m12_double_cover_involution_lift_orders hEq ht hZ ρ hρ hker
  obtain ⟨ι, hιsnd, hιz, -⟩ :=
    exists_local_coordinates hπ h4 (fun v hv hv0 => (h0 v hv hv0).1)
  have hXS : X ∈ InternalSylow.S.comap ρ := by rw [mem_comap, hX]; exact (d 8).2
  have hYS : Y ∈ InternalSylow.S.comap ρ := by rw [mem_comap, hY]; exact (d 20).2
  set X' : InternalSylow.S.comap ρ := ⟨X, hXS⟩
  set Y' : InternalSylow.S.comap ρ := ⟨Y, hYS⟩
  have hιX : ι X' = ⟨(ι X').fst, d 8⟩ := by
    refine CocycleExtension.ext rfl (Subtype.ext ?_)
    rw [hιsnd]
    exact hX
  have hιY : ι Y' = ⟨(ι Y').fst, d 20⟩ := by
    refine CocycleExtension.ext rfl (Subtype.ext ?_)
    rw [hιsnd]
    exact hY
  have hcomm : d 8 * d 20 = d 20 * d 8 := by rw [← d_mul, ← d_mul, hm820]
  have hval : fN (d 8) (d 20) + fN (d 20) (d 8) = 1 := by
    have h1 : fIdx ((8 : Fin 64) : ℕ) ((20 : Fin 64) : ℕ) = 0 := by decide +kernel
    have h2 : fIdx ((20 : Fin 64) : ℕ) ((8 : Fin 64) : ℕ) = 1 := by decide +kernel
    rw [fN_apply, fN_apply, f_d, f_d, h1, h2]
    decide
  have hcomm' : ι (X'⁻¹ * Y'⁻¹ * X' * Y') = ⟨1, 1⟩ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hιX, hιY,
      CocycleExtension.commutator_mk_of_commute hcomm, hval]
  have := congrArg (fun w => ((ι.symm w : InternalSylow.S.comap ρ) : E)) hcomm'
  simp only [MulEquiv.symm_apply_apply] at this
  rw [hιz] at this
  exact this

end CFSG.ComponentClassification.M12Cover

namespace CFSG.ComponentClassification.J2Cover

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CentralCover
open CFSG.ComponentClassification.J2Cover.Models

set_option compiler.extract_closed false in
private theorem fRows_bits_two_sixteen :
    (bitAt fRows 2 16 && !bitAt fRows 16 2) = false ∧
    (!bitAt fRows 2 16 && bitAt fRows 16 2) = true :=
  Certificates.certificate10026

theorem j2_pair_displacement :
    ∃ x y : NativeSporadic.J2, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y ∧ x * y = y * x ∧
      ∀ (E : Type) [Group E] [Finite E], Assembly.IsQuasisimple E → ∀ t : E, orderOf t = 2 →
        center E = zpowers t → ∀ ρ : E →* NativeSporadic.J2,
          Function.Surjective ρ → ρ.ker = zpowers t →
          ∀ X Y : E, ρ X = x → ρ Y = y → X⁻¹ * Y⁻¹ * X * Y = t := by
  let e : NativeSporadic.J2 ≃* Models.P := nativeEquivP.trans Lift.toModels
  have h2 : (2 : ℕ) < 128 := by norm_num
  have h16 : (16 : ℕ) < 128 := by norm_num
  have hm22 : mulIdx 2 2 = 0 := by decide +kernel
  have hm1616 : mulIdx 16 16 = 0 := by decide +kernel
  have hm216 : mulIdx 2 16 = mulIdx 16 2 := by decide +kernel
  have hsq : ∀ j : ℕ, j < 128 → mulIdx j j = 0 → j ≠ 0 → orderOf (elt j) = 2 := by
    intro j hj hjj hj0
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← (mulIdx_spec hj).2, hjj, elt_zero]
    · intro h1
      exact hj0 (elt_injective hj (by norm_num) (h1.trans elt_zero.symm))
  let a₀ : Sp := eS.symm (elt 2)
  let b₀ : Sp := eS.symm (elt 16)
  have hord : ∀ s : Sp, orderOf (e.symm (s : Models.P)) = orderOf (eS s) := fun s => by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hcomm : elt 2 * elt 16 = elt 16 * elt 2 := by
    rw [← (mulIdx_spec h16).2, ← (mulIdx_spec h2).2, hm216]
  refine ⟨e.symm (a₀ : Models.P), e.symm (b₀ : Models.P), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hord, MulEquiv.apply_symm_apply]
    exact hsq 2 h2 hm22 (by norm_num)
  · rw [hord, MulEquiv.apply_symm_apply]
    exact hsq 16 h16 hm1616 (by norm_num)
  · intro h
    have h' := congrArg eS (Subtype.ext (e.symm.injective h) : a₀ = b₀)
    simp only [a₀, b₀, MulEquiv.apply_symm_apply] at h'
    exact absurd (elt_injective h2 h16 h') (by norm_num)
  · rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      hcomm]
  intro E _ _ hEq t ht hZ ρ hρ hker X Y hX hY
  have : Group.IsPerfect E := (Group.isPerfect_def).2 hEq.1
  let ρ' : E →* Models.P := e.toMonoidHom.comp ρ
  have hπ : IsCentralDoubleExt ρ' t := by
    refine ⟨e.surjective.comp hρ, hZ ▸ mem_zpowers t, ht, ?_⟩
    rw [← hker]
    ext v
    simp only [ρ', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨ι, hιsnd, hιz, -⟩ := exists_local_coordinates_of_finite hπ
  have hXS : X ∈ Sp.comap ρ' := by
    rw [mem_comap]
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hX, MulEquiv.apply_symm_apply]
    exact a₀.2
  have hYS : Y ∈ Sp.comap ρ' := by
    rw [mem_comap]
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hY, MulEquiv.apply_symm_apply]
    exact b₀.2
  set X' : Sp.comap ρ' := ⟨X, hXS⟩
  set Y' : Sp.comap ρ' := ⟨Y, hYS⟩
  have hιX : ι X' = ⟨(ι X').fst, a₀⟩ := by
    refine CocycleExtension.ext rfl (Subtype.ext ?_)
    rw [hιsnd]
    simp only [X', ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hX,
      MulEquiv.apply_symm_apply]
  have hιY : ι Y' = ⟨(ι Y').fst, b₀⟩ := by
    refine CocycleExtension.ext rfl (Subtype.ext ?_)
    rw [hιsnd]
    simp only [Y', ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hY,
      MulEquiv.apply_symm_apply]
  have hcomm₀ : a₀ * b₀ = b₀ * a₀ := by
    simp only [a₀, b₀, ← map_mul, hcomm]
  have hval : fN a₀ b₀ + fN b₀ a₀ = 1 := by
    have hb1 : bitAt fRows 2 16 = false := by
      have := fRows_bits_two_sixteen.2
      revert this
      cases bitAt fRows 2 16 <;> simp
    have hb2 : bitAt fRows 16 2 = true := by
      have := fRows_bits_two_sixteen.2
      revert this
      cases bitAt fRows 16 2 <;> simp
    rw [fN_apply, fN_apply]
    simp only [a₀, b₀, MulEquiv.apply_symm_apply, fCoc, tbl_elt fRows h2 h16,
      tbl_elt fRows h16 h2, hb1, hb2]
    decide
  have hcomm' : ι (X'⁻¹ * Y'⁻¹ * X' * Y') = ⟨1, 1⟩ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hιX, hιY,
      CocycleExtension.commutator_mk_of_commute hcomm₀, hval]
  have := congrArg (fun w => ((ι.symm w : Sp.comap ρ') : E)) hcomm'
  simp only [MulEquiv.symm_apply_apply] at this
  rw [hιz] at this
  exact this

end CFSG.ComponentClassification.J2Cover

namespace CFSG.ComponentClassification.StandardRecognition

theorem m12J2PairDisplacement :
    M12J2PairDisplacement := by
  rintro s (rfl | rfl)
  · exact M12Cover.m12_pair_displacement
  · exact J2Cover.j2_pair_displacement

theorem m12J2CentralTwoGroupOrderBound :
    M12J2CentralTwoGroupOrderBound :=
  m12J2CentralTwoGroupOrderBound_of_displacement m12J2PairDisplacement

end CFSG.ComponentClassification.StandardRecognition
