module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GU6

open Matrix CFSG.Open CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

theorem scalars_subgroupOf_bot (hF : Nat.card F = (2 ^ 2) ^ 2) :
    (StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 hx
  have hcSU : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ StatedSU 6 (2 ^ 2) F := by
    rw [hc]
    exact x.2
  have hkey := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 6)
    (by norm_num)).2.1 c).1 hcSU
  have h6 : c ^ 6 = 1 := hkey.1
  have h5 : c ^ 5 = 1 := by simpa using hkey.2
  have hc1 : c = 1 := by
    have key : c = c ^ 6 * (c ^ 5)⁻¹ := by group
    rw [h6, h5] at key
    simpa using key
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

@[expose] noncomputable def projIso (hF : Nat.card F = (2 ^ 2) ^ 2) :
    StatedProj (StatedSU 6 (2 ^ 2) F) ≃* StatedSU 6 (2 ^ 2) F :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_subgroupOf_bot hF)).trans QuotientGroup.quotientBot

theorem projIso_projH (hF : Nat.card F = (2 ^ 2) ^ 2) (x : StatedSU 6 (2 ^ 2) F) :
    projIso hF (projH _ x) = x :=
  rfl

theorem projH_injective (hF : Nat.card F = (2 ^ 2) ^ 2) {x y : StatedSU 6 (2 ^ 2) F}
    (h : projH _ x = projH _ y) : x = y := by
  rw [← projIso_projH hF x, ← projIso_projH hF y, h]

theorem projH_eq_symm (hF : Nat.card F = (2 ^ 2) ^ 2) (y : StatedSU 6 (2 ^ 2) F) :
    (projIso hF).symm y = projH _ y := by
  rw [MulEquiv.symm_apply_eq, projIso_projH]

theorem transport_fix (hF : Nat.card F = (2 ^ 2) ^ 2) (α : MulAut (StatedSU 6 (2 ^ 2) F)) :
    ∃ A : GL (Fin 6) F, ((A : Matrix (Fin 6) (Fin 6) F).map (fun x : F => x ^ 4))ᵀ *
        (A : Matrix (Fin 6) (Fin 6) F) = 1 ∧
      ∃ φ : F ≃+* F, ∀ x : ↥(StatedSU 6 (2 ^ 2) F),
        (((α x : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
          (A : Matrix (Fin 6) (Fin 6) F) * ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).map φ *
            ((A⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  have hh : UnitaryFieldData 2 2 F :=
    ⟨Nat.prime_two, by norm_num, by rw [hF]; norm_num⟩
  let α'' : MulAut (StatedProj (StatedSU 6 (2 ^ 2) F)) :=
    (projIso hF).trans (α.trans (projIso hF).symm)
  obtain ⟨A, φ, hαeq⟩ := exists_uConjAut_mul_uFieldAut hh (n := 6) (by norm_num)
    (by norm_num) α''
  have hA : (A : GL (Fin 6) F) ∈ uU hh 6 := A.2
  refine ⟨(A : GL (Fin 6) F), ?_, φ, ?_⟩
  · have h := (mem_uU hh).1 hA
    have hbar : (fun x : F => x ^ 4) = ⇑hh.bar := by
      funext c
      rw [UnitaryFieldData.bar_apply]
      norm_num
    rw [hbar]
    exact h
  · intro x
    have hx : projH _ (α x) = projH _ (uLift hh A φ x) := by
      have h1 : α'' (projH _ x) = projH _ (α x) := by
        change (projIso hF).symm (α (projIso hF (projH _ x))) = projH _ (α x)
        rw [projIso_projH, projH_eq_symm]
      rw [← h1, hαeq]
      exact uLift_proj hh (by norm_num) A φ x
    have hxe : α x = uLift hh A φ x := projH_injective hF hx
    rw [hxe, coe_uLift]

end CFSG.LocalAnalysis.GLTheoremA.Y10GU6
