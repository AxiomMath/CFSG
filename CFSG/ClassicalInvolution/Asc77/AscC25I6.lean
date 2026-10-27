module

public import CFSG.ClassicalInvolution.Asc77.AscC25I5
public import CFSG.ClassicalInvolution.SmallCases.NDB1Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I.Sp5

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix commutatorElement

variable {F : Type} [Field F]

theorem psp4_std_twinQ (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (k : Fin 2)
    (hψ : ψ (longInv F 2 (Fin.rev k)) = ψ (longInv F 2 k)) :
    ∃ s : Y, s * s = 1 ∧ s * ψ (longInv F 2 k) = ψ (longInv F 2 k) * s ∧
      conjSub s ((longRootSp2 F 2 k).map ψ) = (longRootSp2 F 2 (Fin.rev k)).map ψ ∧
      conjSub s ((longRootSp2 F 2 (Fin.rev k)).map ψ) = (longRootSp2 F 2 k).map ψ ∧
      (∃ x : Y, s = x * ψ (longInv F 2 k) * x⁻¹) ∧
      ∃ x y : Y, y ∈ conjSub x ((longRootSp2 F 2 k).map ψ) ∧ orderOf y = 4 ∧
        y * (ψ (longInv F 2 k) * s) = (ψ (longInv F 2 k) * s) * y := by
  have hσi : (Sp.swapSp : StatedSp 2 F) * longInv F 2 k =
      longInv F 2 (Fin.rev k) * Sp.swapSp := by
    have := Sp.swapSp_conj_longInv (F := F) k
    calc (Sp.swapSp : StatedSp 2 F) * longInv F 2 k =
        (Sp.swapSp * longInv F 2 k * Sp.swapSp⁻¹) * Sp.swapSp := by group
      _ = _ := by rw [this]
  have hσL : conjSub (Sp.swapSp : StatedSp 2 F) (longRootSp2 F 2 k) = longRootSp2 F 2 (Fin.rev k) :=
    Sp.map_conj_swapSp k
  have hσL' : conjSub (Sp.swapSp : StatedSp 2 F) (longRootSp2 F 2 (Fin.rev k)) =
      longRootSp2 F 2 k := by
    have := Sp.map_conj_swapSp (F := F) (Fin.rev k)
    rwa [Fin.rev_rev] at this
  obtain ⟨h, hh⟩ := exists_swapSp_mul_eq h2 k
  have hsw : (Sp.swapSp : StatedSp 2 F) = h * longInv F 2 k * h⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hh
  refine ⟨ψ Sp.swapSp, ?_, ?_, ?_, ?_, ⟨ψ h, ?_⟩, ?_⟩
  · rw [← map_mul, swapSp_mul_self, map_one]
  · rw [← map_mul, ← map_mul, hσi, map_mul, map_mul, hψ]
  · rw [← Sp.map_conjSub_of_hom, hσL]
  · rw [← Sp.map_conjSub_of_hom, hσL']
  · rw [hsw, map_mul, map_mul, map_inv]
  · have hP : IsHyperbolicPlane (Submodule.span F {(uV : Fin 2 ⊕ Fin 2 → F), wV}) :=
      ⟨uV, wV, form_uV_wV h2, rfl⟩
    obtain ⟨i₁, hi₁, -⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hP
    obtain ⟨k₁, g₁, hL, -⟩ := hi₁
    have hyL : yEl h2 ∈ conjSub g₁ (longRootSp2 F 2 k₁) := by
      have : yEl h2 ∈ (longRootSp2 F 2 k₁).map (MulAut.conj g₁).toMonoidHom := by
        rw [← hL]
        exact yEl_mem_planeGroup h2
      exact this
    have hmem : ψ (yEl h2) ∈ conjSub (ψ g₁) ((longRootSp2 F 2 k₁).map ψ) := by
      rw [← Sp.map_conjSub_of_hom]
      exact Subgroup.mem_map_of_mem ψ hyL
    have hcomm : ψ (yEl h2) * (ψ (longInv F 2 k) * ψ Sp.swapSp) =
        (ψ (longInv F 2 k) * ψ Sp.swapSp) * ψ (yEl h2) := by
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      apply mat_injective
      rw [map_mul, map_mul, mat_yEl]
      exact yMat_comm_g k
    have hk₁ : k₁ = k ∨ k₁ = Fin.rev k := by
      fin_cases k <;> fin_cases k₁ <;> simp
    rcases hk₁ with rfl | rfl
    · exact ⟨ψ g₁, ψ (yEl h2), hmem, orderOf_map_yEl h2 ψ hker, hcomm⟩
    · refine ⟨ψ g₁ * ψ Sp.swapSp, ψ (yEl h2), ?_, orderOf_map_yEl h2 ψ hker, hcomm⟩
      have e1 : conjSub (ψ Sp.swapSp) ((longRootSp2 F 2 k).map ψ) =
          (longRootSp2 F 2 (Fin.rev k)).map ψ := by
        rw [← Sp.map_conjSub_of_hom, hσL]
      rw [conjSub_mul, e1]
      exact hmem

theorem psp4_std_center (hperf : Group.IsPerfect (StatedSp 2 F)) {Y : Type} [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) (k : Fin 2)
    (hψ : ψ (longInv F 2 (Fin.rev k)) = ψ (longInv F 2 k)) :
    ∀ w : Y, (∀ v : Y, v * w = w * v) → w = 1 := by
  have hψ' : ψ (longInv F 2 1) = ψ (longInv F 2 0) := by
    fin_cases k
    · exact hψ
    · exact hψ.symm
  have hcen : ∀ c ∈ Subgroup.center (StatedSp 2 F), ψ c = 1 := by
    intro c hc
    rcases CFSG.ClassicalInvolution.NDB.Model.center_eq hc with rfl | rfl
    · exact map_one ψ
    · rw [map_mul, hψ', ← map_mul, CFSG.ClassicalInvolution.NDB.Model.longInv_sq, map_one]
  intro w hw
  obtain ⟨g₀, rfl⟩ := hsurj w
  have hcomm : ∀ g : StatedSp 2 F, ⁅g₀, g⁆ ∈ Subgroup.center (StatedSp 2 F) := by
    intro g
    refine hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hw (ψ g)).symm
  exact hcen _
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.mem_center_of_forall_commutator_mem_center
      hperf hcomm)

theorem psp4_model_twinQ (h2 : (2 : F) ≠ 0) (hperf : Group.IsPerfect (StatedSp 2 F)) {Y : Type}
    [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ)
    {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F} (hR : IsLongRootSp2 R i)
    (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    (∃ s : Y, s * s = 1 ∧ s * z' = z' * s ∧ conjSub s (R.map ψ) = R'.map ψ ∧
      conjSub s (R'.map ψ) = R.map ψ ∧ (∃ x : Y, s = x * z' * x⁻¹) ∧
      ∃ x y : Y, y ∈ conjSub x (R.map ψ) ∧ orderOf y = 4 ∧ y * (z' * s) = (z' * s) * y) ∧
      ∀ w : Y, (∀ v : Y, v * w = w * v) → w = 1 := by
  have hψi := CFSG.ClassicalInvolution.Asc77.C25W.Sp.psp4_map_inv_eq h2 ψ hker hR hz
  have hψi' := CFSG.ClassicalInvolution.Asc77.C25W.Sp.psp4_map_inv_eq h2 ψ hker hR' hz'
  have hiR : i ∈ R := (hR.isClassicalSL2 h2).mem
  have hi'R' : i' ∈ R' := (hR'.isClassicalSL2 h2).mem
  have hi2 : i * i = 1 := by
    have := pow_orderOf_eq_one i
    rwa [(hR.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi'2 : i' * i' = 1 := by
    have := pow_orderOf_eq_one i'
    rwa [(hR'.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi1 : i ≠ 1 := by
    intro h
    have := (hR.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hi'1 : i' ≠ 1 := by
    intro h
    have := (hR'.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hc : i' * i⁻¹ ∈ Subgroup.center (StatedSp 2 F) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel])
  have hRne : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨g, k, hRg, hR'g⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.twin_std_sp h2 ⟨i, hR⟩ ⟨i', hR'⟩ hRne
      hiR hi2 hi1 hi'R' hi'2 hi'1 hc
  set ψ₁ : StatedSp 2 F →* Y := ψ.comp (MulAut.conj g).toMonoidHom with hψ₁
  have hker₁ : ψ₁.ker ≤ Subgroup.center (StatedSp 2 F) := by
    intro x hx
    have hc' : g * x * g⁻¹ ∈ Subgroup.center (StatedSp 2 F) := hker hx
    have h3 : g * (g * x * g⁻¹) = (g * x * g⁻¹) * g := Subgroup.mem_center_iff.mp hc' g
    have e : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * ((g * x * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [← h3]
        _ = g * x * g⁻¹ := by group
    rw [e]
    exact hc'
  have hRψ : R.map ψ = (longRootSp2 F 2 k).map ψ₁ := by
    rw [hRg, hψ₁, ← Subgroup.map_map]
    rfl
  have hR'ψ : R'.map ψ = (longRootSp2 F 2 (Fin.rev k)).map ψ₁ := by
    rw [hR'g, hψ₁, ← Subgroup.map_map]
    rfl
  have hRi : IsLongRootSp2 R (g * longInv F 2 k * g⁻¹) := by
    rw [hRg]
    exact (isLongRootSp2_standard k).conj g
  have hR'i : IsLongRootSp2 R' (g * longInv F 2 (Fin.rev k) * g⁻¹) := by
    rw [hR'g]
    exact (isLongRootSp2_standard (Fin.rev k)).conj g
  have hz₁ : ψ₁ (longInv F 2 k) = z' := by
    rw [← CFSG.ClassicalInvolution.Asc77.C25W.Sp.psp4_map_inv_eq h2 ψ hker hRi hz]
    rfl
  have hz₂ : ψ₁ (longInv F 2 (Fin.rev k)) = z' := by
    rw [← CFSG.ClassicalInvolution.Asc77.C25W.Sp.psp4_map_inv_eq h2 ψ hker hR'i hz']
    rfl
  obtain ⟨s, hs0, hs1, hs2, hs3, hs4, hs5⟩ := psp4_std_twinQ h2 ψ₁ hker₁ k (by rw [hz₁, hz₂])
  have hcen := psp4_std_center hperf ψ₁ hker₁ (hsurj.comp (MulAut.conj g).surjective) k
    (by rw [hz₁, hz₂])
  rw [hz₁] at hs1 hs4 hs5
  rw [← hRψ, ← hR'ψ] at hs2 hs3
  rw [← hRψ] at hs5
  exact ⟨⟨s, hs0, hs1, hs2, hs3, hs4, hs5⟩, hcen⟩

end CFSG.ClassicalInvolution.Asc77.C25I.Sp5
