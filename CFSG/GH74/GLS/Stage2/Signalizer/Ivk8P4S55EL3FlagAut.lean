module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharVec
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Fl3

open Subgroup Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def gAut (A : GL (Fin 3) F) (σ : F ≃+* F) : MulAut SL(3, F) :=
  CatalogueBHigherLinearAction.slConjugation 3 F A *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ * CatalogueBGraphForm.slGraphAut 3 F

theorem proj_gAut (A : GL (Fin 3) F) (σ : F ≃+* F) (x : SL(3, F)) :
    (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F x) = proj 3 F (gAut A σ x) := by
  have h : descendAut 3 F (gAut A σ) = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F := by
    unfold gAut
    rw [map_mul, map_mul]
    try rfl
  rw [← h, descendAut_proj]

theorem gAut_coe (A : GL (Fin 3) F) (σ : F ≃+* F) (x : SL(3, F)) :
    ((gAut A σ x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        σ.toRingHom.mapMatrix ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [gAut, MulAut.mul_apply, MulAut.mul_apply,
    CatalogueBHigherLinearAction.slConjugation_matrix]
  have h1 : ((CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ
      (CatalogueBGraphForm.slGraphAut 3 F x) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      σ.toRingHom.mapMatrix ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ) := by
    ext i j
    rfl
  rw [h1]

theorem gAut_mem {p : ℕ} [Fact p.Prime] [CharP F p] [Finite F] {Û : Subgroup SL(3, F)}
    (hÛ : IsPGroup p ↥Û) (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hα : ∀ x ∈ Û, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F x) ∈
      Û.map (proj 3 F)) : ∀ x ∈ Û, gAut A σ x ∈ Û := by
  intro x hx
  obtain ⟨m, hm⟩ := hÛ ⟨x, hx⟩
  have hxm : x ^ p ^ m = 1 := congrArg Subtype.val hm
  have h1 : (gAut A σ x) ^ p ^ m = 1 := by rw [← map_pow, hxm, map_one]
  refine CFSG.LieType.BorelTits.mem_of_mk_mem_map (scalars 3 F) (scalars_le_center 3 F)
    (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.coprime_card_scalars p) hÛ ?_ h1
  have h2 := hα x hx
  rw [proj_gAut] at h2
  exact h2

theorem card_fix_eq_aux [Finite F] (M M' : Matrix (Fin 3) (Fin 3) F) (hMM' : M' * M = 1)
    (hM'M : M * M' = 1) (σ : F ≃+* F) (γ : MulAut SL(3, F))
    (hγ : ∀ x : SL(3, F), ((γ x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      M * σ.toRingHom.mapMatrix ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ) * M')
    (R : Subgroup SL(3, F)) (hR : ∀ x ∈ R, γ x ∈ R) :
    Nat.card {v : Fin 3 → F // ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v} =
      Nat.card {w : Fin 3 → F // ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w} := by
  classical
  have hsurj : ∀ y ∈ R, ∃ x ∈ R, γ x = y := by
    let φ : ↥R → ↥R := fun x => ⟨γ x, hR x x.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (γ.injective (congrArg Subtype.val h))
    have hs := Finite.injective_iff_surjective.mp hinj
    intro y hy
    obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  have hinv : ∀ u : Fin 3 → F, M' *ᵥ (M *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
  have hinv' : ∀ u : Fin 3 → F, M *ᵥ (M' *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  let Ψ : (Fin 3 → F) ≃ (Fin 3 → F) :=
    { toFun := fun w => M *ᵥ (fun i => σ (w i))
      invFun := fun v => fun i => σ.symm ((M' *ᵥ v) i)
      left_inv := fun w => by
        funext i
        simp only [hinv, RingEquiv.symm_apply_apply]
      right_inv := fun v => by
        have : (fun i => σ (σ.symm ((M' *ᵥ v) i))) = M' *ᵥ v := by
          funext i
          exact σ.apply_symm_apply _
        show M *ᵥ (fun i => σ (σ.symm ((M' *ᵥ v) i))) = v
        rw [this, hinv'] }
  have key : ∀ (x : SL(3, F)) (w : Fin 3 → F),
      ((γ x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Ψ w) = Ψ w ↔
        (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ w = w := by
    intro x w
    rw [hγ]
    have e1 : (M * σ.toRingHom.mapMatrix ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ) *
        M') *ᵥ (Ψ w) = M *ᵥ (fun i => σ (((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ
          w) i)) := by
      change (M * σ.toRingHom.mapMatrix ((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ) *
        M') *ᵥ (M *ᵥ (fun i => σ (w i))) = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv]
      congr 1
      funext i
      exact (RingHom.map_mulVec σ.toRingHom _ w i).symm
    rw [e1]
    change M *ᵥ (fun i => σ (((((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ w) i)) =
      M *ᵥ (fun i => σ (w i)) ↔ _
    constructor
    · intro h
      have h2 := congrArg (fun u => M' *ᵥ u) h
      simp only [hinv] at h2
      funext i
      exact σ.injective (congrFun h2 i)
    · intro h
      rw [h]
  have hΨ : ∀ w : Fin 3 → F, (∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w) ↔
      (∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (Ψ w) = Ψ w) := by
    intro w
    constructor
    · intro h g hg
      obtain ⟨x, hx, rfl⟩ := hsurj g hg
      exact (key x w).mpr (h _ (R.inv_mem hx))
    · intro h g hg
      have := (key g⁻¹ w).mp (h _ (hR _ (R.inv_mem hg)))
      simpa using this
  exact (Nat.card_congr (Equiv.subtypeEquiv Ψ hΨ)).symm

theorem card_fix_eq [Finite F] (A : GL (Fin 3) F) (σ : F ≃+* F) (R : Subgroup SL(3, F))
    (hR : ∀ x ∈ R, gAut A σ x ∈ R) :
    Nat.card {v : Fin 3 → F // ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v} =
      Nat.card {w : Fin 3 → F // ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w} :=
  card_fix_eq_aux (A : Matrix (Fin 3) (Fin 3) F) ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) σ (gAut A σ) (gAut_coe A σ) R hR

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Fl3
