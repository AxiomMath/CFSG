module

public import CFSG.ClassicalInvolution.Asc77.AscC25W10
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect

public section

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.Generic

namespace CFSG.ClassicalInvolution.Asc77.C25W.Sp

variable {F : Type} [Field F]

theorem scalar_of_mem_spScalars {x : StatedSp 2 F} (hx : x ∈ spScalars 2 F) :
    ∃ c : F, mat 2 F x = c • 1 := by
  have hx' : (x : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedScalars (Fin 2 ⊕ Fin 2) F := hx
  rw [StatedScalars, MonoidHom.mem_range] at hx'
  obtain ⟨c, hc⟩ := hx'
  refine ⟨c, ?_⟩
  rw [mat_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem longInv_conj_not_scalar (h2 : (2 : F) ≠ 0) (k : Fin 2) (g : StatedSp 2 F) :
    ¬ ∃ c : F, mat 2 F (g * longInv F 2 k * g⁻¹) = c • 1 := by
  rintro ⟨c, hc⟩
  have hi : mat 2 F (longInv F 2 k) = c • 1 := by
    have : longInv F 2 k = g⁻¹ * (g * longInv F 2 k * g⁻¹) * g := by group
    rw [this, map_mul, map_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← map_mul, inv_mul_cancel, map_one]
  rw [mat_longInv] at hi
  fin_cases k
  · have a0 := congrFun (congrFun hi (Sum.inl 0)) (Sum.inl 0)
    have a1 := congrFun (congrFun hi (Sum.inl 1)) (Sum.inl 1)
    have h10 : (Sum.inl 1 : Fin 2 ⊕ Fin 2) ∉ coords (0 : Fin 2) := by
      intro h
      rcases mem_coords.1 h with h | h
      · exact absurd (Sum.inl.inj h) (by decide)
      · exact Sum.inl_ne_inr h
    simp [inl_mem_coords, h10] at a0 a1
    apply h2
    linear_combination a1 - a0
  · have a0 := congrFun (congrFun hi (Sum.inl 1)) (Sum.inl 1)
    have a1 := congrFun (congrFun hi (Sum.inl 0)) (Sum.inl 0)
    have h10 : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ∉ coords (1 : Fin 2) := by
      intro h
      rcases mem_coords.1 h with h | h
      · exact absurd (Sum.inl.inj h) (by decide)
      · exact Sum.inl_ne_inr h
    simp [inl_mem_coords, h10] at a0 a1
    apply h2
    linear_combination a1 - a0


theorem ker_eq_spScalars [Finite F] (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F} (hR : IsLongRootSp2 R i)
    (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    ψ.ker = spScalars 2 F := by
  have hcen : Subgroup.center (StatedSp 2 F) = spScalars 2 F :=
    CFSG.LieType.Universal.Symplectic.center_eq 2 F
  have key : ∀ {L : Subgroup (StatedSp 2 F)} {j : StatedSp 2 F} {z : Y}, IsLongRootSp2 L j →
      IsUniqueInvolution (L.map ψ) z → ψ j = z := by
    intro L j z hL hzL
    have hjL : j ∈ L := (hL.isClassicalSL2 h2).mem
    have hj2 : j * j = 1 := by
      have := pow_orderOf_eq_one j
      rwa [(hL.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
    have hmem : ψ j ∈ L.map ψ := Subgroup.mem_map_of_mem ψ hjL
    have hψj2 : ψ j * ψ j = 1 := by rw [← map_mul, hj2, map_one]
    rcases hzL.unique (ψ j) hmem hψj2 with h | h
    · exfalso
      have hjk : j ∈ ψ.ker := h
      have hjc := hker hjk
      rw [hcen] at hjc
      obtain ⟨c, hc⟩ := scalar_of_mem_spScalars hjc
      obtain ⟨k, g, -, hjg⟩ := hL
      rw [hjg] at hc
      exact longInv_conj_not_scalar h2 k g ⟨c, hc⟩
    · exact h
  have hψi := key hR hz
  have hψi' := key hR' hz'
  have hc1 : i * i'⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel]
  have hcne : i * i'⁻¹ ≠ 1 := by
    intro h
    have : i = i' := mul_inv_eq_one.mp h
    apply hne
    rw [hR.eq_longRootGroup h2, hR'.eq_longRootGroup h2, this]
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have := hker hx
    rwa [hcen] at this
  · have hcsc : i * i'⁻¹ ∈ spScalars 2 F := by rw [← hcen]; exact hker hc1
    have hcard := CFSG.LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two 2 F
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · by_cases hxc : x = i * i'⁻¹
      · rw [hxc]; exact hc1
      · exfalso
        let a : ↥(spScalars 2 F) := 1
        let b : ↥(spScalars 2 F) := ⟨i * i'⁻¹, hcsc⟩
        let d : ↥(spScalars 2 F) := ⟨x, hx⟩
        have hab : a ≠ b := fun h => hcne (congrArg Subtype.val h).symm
        have had : a ≠ d := fun h => hx1 (congrArg Subtype.val h).symm
        have hbd : b ≠ d := fun h => hxc (congrArg Subtype.val h).symm
        have hinj : Function.Injective (![a, b, d] : Fin 3 → ↥(spScalars 2 F)) := by
          intro i j h
          fin_cases i <;> fin_cases j <;> simp_all
        have h3 := Nat.card_le_card_of_injective _ hinj
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
        have : Nat.card ↥(spScalars 2 F) ≤ 2 := hcard
        omega


@[expose] noncomputable def projEquiv {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker = spScalars 2 F) :
    StatedProj (StatedSp 2 F) ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq (show spScalars 2 F = ψ.ker from hker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)

theorem projEquiv_proj {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker = spScalars 2 F) (x : StatedSp 2 F) :
    projEquiv ψ hsurj hker (proj 2 F x) = ψ x := rfl

theorem psp4_model_sq [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {Y : Type} [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z')
    (β : MulAut Y) (hβ : ∀ x : Y, β (β (β (β x))) = x) :
    ∃ (u w : Fin 2 ⊕ Fin 2 → F) (s : StatedSp 2 F), form u w = 1 ∧
      s ∈ planeGroup (Submodule.span F {u, w}) ∧ orderOf (ψ s) = 4 ∧ β (β (ψ s)) = ψ s := by
  have hk := ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  set e := projEquiv ψ hsurj hk with he
  let β' : MulAut (StatedProj (StatedSp 2 F)) := e.trans (β.trans e.symm)
  have hβ'1 : ∀ x, e (β' x) = β (e x) := fun x => by simp [β']
  have hβ'4 : β' * β' * (β' * β') = 1 := by
    ext x
    apply e.injective
    show e (β' (β' (β' (β' x)))) = e x
    rw [hβ'1, hβ'1, hβ'1, hβ'1, hβ]
  obtain ⟨u, w, s, huw, hs, hord, hfix⟩ := psp4_sq_fixed h2 h4 β' hβ'4
  refine ⟨u, w, s, huw, hs, ?_, ?_⟩
  · rw [← projEquiv_proj ψ hsurj hk s, ← he, MulEquiv.orderOf_eq]
    exact hord
  · have h1 := congrArg e hfix
    have e1 : e (β' (β' (proj 2 F s))) = β (β (e (proj 2 F s))) := by rw [hβ'1, hβ'1]
    rw [e1] at h1
    exact h1

end CFSG.ClassicalInvolution.Asc77.C25W.Sp
