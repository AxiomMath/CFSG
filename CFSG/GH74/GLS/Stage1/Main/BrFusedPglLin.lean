module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedH4
public import CFSG.GH74.GLS.Stage2.Final.ModelLUData

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GorensteinWalter

variable {F : Type} [Field F]

theorem unit_det_sc2 (c : Fˣ) : Matrix.GeneralLinearGroup.det (sc2 c : GL (Fin 2) F) = c * c := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_sc2, Units.val_mul, sq]

theorem exists_sq_mul_pow_four_lin [Finite F] (hq8 : Nat.card F % 8 = 5) (δ : Fˣ) :
    ∃ u : Fˣ, (u * u * δ) ^ 4 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 8 * k + 5 := ⟨Nat.card F / 8, by omega⟩
  refine ⟨δ⁻¹ ^ (k + 1), ?_⟩
  have h1 : δ⁻¹ ^ (k + 1) * δ⁻¹ ^ (k + 1) * δ = δ⁻¹ ^ (2 * k + 1) := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, mul_assoc,
      inv_mul_cancel, mul_one]
  rw [h1, ← pow_mul, show (2 * k + 1) * 4 = Nat.card F - 1 by omega]
  exact pow_card_sub_one_lin _

theorem lin_psi4 [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (hq8 : Nat.card F % 8 = 5) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (Ψ : ↥(H4 (ModelData.lin F)) →* PGL2 F₀),
      Nat.card F₀ = Nat.card F ∧ Function.Surjective Ψ ∧
        ∀ g : ↥(H4 (ModelData.lin F)), Ψ g = 1 ↔ ∃ c : Fˣ, (g : GL (Fin 2) F) = sc2 c := by
  have _ := h2
  have _ := h5
  refine ⟨F, inferInstance, inferInstance,
    (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F).comp (H4 (ModelData.lin F)).subtype, rfl,
    ?_, ?_⟩
  · intro x
    obtain ⟨g₀, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    obtain ⟨u, hu⟩ := exists_sq_mul_pow_four_lin hq8 (Matrix.GeneralLinearGroup.det g₀)
    refine ⟨⟨sc2 u * g₀, Subgroup.mem_top _, ?_⟩, ?_⟩
    · rw [map_mul, unit_det_sc2]
      exact hu
    · show Matrix.ProjGenLinGroup.mk (sc2 u * g₀) = Matrix.ProjGenLinGroup.mk g₀
      rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  · intro g
    show (Matrix.ProjGenLinGroup.mk (g : GL (Fin 2) F) : PGL2 F) = 1 ↔ _
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
