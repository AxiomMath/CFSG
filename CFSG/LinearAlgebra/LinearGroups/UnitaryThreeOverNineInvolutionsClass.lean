module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsTau

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] {h : UnitaryFieldData 3 1 F}

theorem exists_generator_of_finrank_eq_one {W : Submodule F (Fin 3 → F)}
    (hW : Module.finrank F W = 1) : ∃ v ∈ W, v ≠ 0 ∧ ∀ u ∈ W, ∃ c : F, u = c • v := by
  obtain ⟨⟨v, hvW⟩, hv0, hgen⟩ := finrank_eq_one_iff'.mp hW
  refine ⟨v, hvW, fun h0 => hv0 (Subtype.ext h0), fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := hgen ⟨u, hu⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem exists_tauGL_eq_of_orderOf (hF : Nat.card F = 9) {g : GL (Fin 3) F}
    (hgK : g ∈ StatedSU 3 3 F) (hg2 : orderOf g = 2) :
    ∃ v, ∃ hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0, g = tauGL v hv := by
  have h2 := two_ne_zero' h
  rw [statedSU_eq_gramSU hF h, mem_gramSU_iff_isometry] at hgK
  obtain ⟨hiso, hdet⟩ := hgK
  set a := Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F) with ha
  have hg2' : g * g = 1 := by rw [← sq, ← hg2, pow_orderOf_eq_one]
  have haa : ∀ y, a (a y) = y := fun y => by
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hg2',
      Units.val_one, Matrix.one_mulVec]
  have hiso' : ∀ x y, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (a x) (a y) =
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y := fun x y => by
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hiso x y
  have hdet' : LinearMap.det a = 1 := by rw [ha, LinearMap.det_toLin']; exact hdet
  have hne : a ≠ LinearMap.id := by
    intro h1
    have hg1 : g = 1 := by
      apply Units.ext
      apply Matrix.toLin'.injective
      rw [← ha, h1, Units.val_one, Matrix.toLin'_one]
    rw [hg1, orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  have hneg1 : (-1 : F) ≠ 1 := fun h1 => h2 (by linear_combination -h1)
  have hdetneg : ∀ b : (Fin 3 → F) →ₗ[F] (Fin 3 → F), LinearMap.det b = 1 →
      LinearMap.det (-b) = -1 := fun b hb => by
    rw [← neg_one_smul F b, LinearMap.det_smul, hb, Module.finrank_fin_fun]
    norm_num
  set Vp : Submodule F (Fin 3 → F) := LinearMap.ker (a - LinearMap.id) with hVp
  set Vm : Submodule F (Fin 3 → F) := LinearMap.ker (a + LinearMap.id) with hVm
  have hmemVp : ∀ y, y ∈ Vp ↔ a y = y := fun y => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hmemVm : ∀ y, y ∈ Vm ↔ a y = -y := fun y => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hyp : ∀ y, (2 : F)⁻¹ • (y + a y) ∈ Vp := fun y => by
    rw [hmemVp, map_smul, map_add, haa, add_comm]
  have hym : ∀ y, (2 : F)⁻¹ • (y - a y) ∈ Vm := fun y => by
    rw [hmemVm, map_smul, map_sub, haa, ← smul_neg, neg_sub]
  have hsum : ∀ y, y = (2 : F)⁻¹ • (y + a y) + (2 : F)⁻¹ • (y - a y) := fun y => by
    rw [← smul_add, show y + a y + (y - a y) = (2 : F) • y by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hay : ∀ y, a y = (2 : F)⁻¹ • (y + a y) - (2 : F)⁻¹ • (y - a y) := fun y => by
    rw [← smul_sub, show y + a y - (y - a y) = (2 : F) • a y by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have horth : ∀ u ∈ Vp, ∀ w ∈ Vm, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u w = 0 := by
    intro u hu w hw
    have h1 := hiso' u w
    rw [(hmemVp u).mp hu, (hmemVm w).mp hw, map_neg] at h1
    have h3 : (2 : F) * gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u w = 0 := by
      linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have horth' : ∀ u ∈ Vp, ∀ w ∈ Vm, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w u = 0 := by
    intro u hu w hw
    rw [← bar_gramForm, horth u hu w hw, map_zero]
  have hinf : Vp ⊓ Vm = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 := (hmemVp y).mp hy.1
    have h3 := (hmemVm y).mp hy.2
    rw [Submodule.mem_bot]
    have h4 : (2 : F) • y = 0 := by rw [two_smul]; nth_rewrite 1 [← h1]; rw [h3, neg_add_cancel]
    exact (smul_eq_zero.mp h4).resolve_left h2
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [hsum y]
    exact Submodule.add_mem_sup (hyp y) (hym y)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq Vp Vm
  rw [hsup, hinf, finrank_top, finrank_bot, Module.finrank_fin_fun] at hdim
  rcases (show Module.finrank F Vp = 0 ∨ Module.finrank F Vp = 1 ∨ Module.finrank F Vp = 2 ∨
      Module.finrank F Vp = 3 by omega) with h0 | h1 | h2' | h3
  ·
    exfalso
    have hVp0 : Vp = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hneg : a = -LinearMap.id := LinearMap.ext fun y => by
      have hy0 : (2 : F)⁻¹ • (y + a y) = 0 := by
        have := hyp y
        rw [hVp0, Submodule.mem_bot] at this
        exact this
      have hy1 : y + a y = 0 := (smul_eq_zero.mp hy0).resolve_left (inv_ne_zero h2)
      rw [LinearMap.neg_apply, LinearMap.id_apply]
      exact eq_neg_of_add_eq_zero_right hy1
    rw [hneg, hdetneg _ LinearMap.det_id] at hdet'
    exact hneg1 hdet'
  ·
    obtain ⟨v, hvVp, hv0, hgen⟩ := exists_generator_of_finrank_eq_one h1
    have hBy : ∀ y, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v y =
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v ((2 : F)⁻¹ • (y + a y)) := fun y => by
      conv_lhs => rw [hsum y]
      rw [map_add, horth v hvVp _ (hym y), add_zero]
    have hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0 := by
      intro hvv
      apply hv0
      refine eq_zero_of_gramForm_eq_zero h fun y => ?_
      obtain ⟨c, hc⟩ := hgen _ (hyp y)
      rw [hBy y, hc, map_smul, hvv, smul_zero]
    refine ⟨v, hv, Units.ext ?_⟩
    rw [coe_tauGL]
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix', ← ha]
    refine LinearMap.ext fun y => ?_
    obtain ⟨c, hc⟩ := hgen _ (hyp y)
    have hcB : c = gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v y /
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v := by
      rw [hBy y, hc, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hv]
    rw [tauLin_apply, ← hcB, hay y, hc]
    nth_rewrite 3 [hsum y]
    rw [hc, two_mul, add_smul]
    abel
  ·
    exfalso
    obtain ⟨w, hwVm, hw0, hgen⟩ := exists_generator_of_finrank_eq_one
      (show Module.finrank F Vm = 1 by omega)
    have hBy : ∀ y, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w y =
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w ((2 : F)⁻¹ • (y - a y)) := fun y => by
      conv_lhs => rw [hsum y]
      rw [map_add, horth' _ (hyp y) w hwVm, zero_add]
    have hw : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w w ≠ 0 := by
      intro hww
      apply hw0
      refine eq_zero_of_gramForm_eq_zero h fun y => ?_
      obtain ⟨c, hc⟩ := hgen _ (hym y)
      rw [hBy y, hc, map_smul, hww, smul_zero]
    have hneg : a = -tauLin h w := LinearMap.ext fun y => by
      obtain ⟨c, hc⟩ := hgen _ (hym y)
      have hcB : c = gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w y /
          gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w w := by
        rw [hBy y, hc, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hw]
      have hyp' : (2 : F)⁻¹ • (y + a y) = y - c • w := by
        rw [← hc]
        exact eq_sub_of_add_eq (hsum y).symm
      rw [LinearMap.neg_apply, tauLin_apply, ← hcB, hay y, hc, hyp', two_mul, add_smul]
      abel
    rw [hneg, hdetneg _ (det_tauLin hw)] at hdet'
    exact hneg1 hdet'
  ·
    exfalso
    have hVpt : Vp = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
    apply hne
    refine LinearMap.ext fun y => ?_
    have := (hmemVp y).mp (by rw [hVpt]; exact Submodule.mem_top)
    rw [this, LinearMap.id_apply]

end CFSG.LinearGroups.UnitaryThreeOverNine
