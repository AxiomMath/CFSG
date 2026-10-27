module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Facts
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

namespace Fz319Data

theorem cL_x {x₁ x₂ : G} (hx₁ : x₁ ∈ E) (hx₂ : x₂ ∈ E) (hl : lam * x₁ * lam⁻¹ = x₂) :
    (D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩) = D.φ ⟨x₂, D.pf.EP hx₂⟩ := by
  apply D.φ.symm.injective
  apply Subtype.ext
  rw [D.cL_coe]
  simp only [MulEquiv.symm_apply_apply, Subtype.coe_mk]
  exact hl

theorem validX {x₁ x₂ : G} (hx₁ : x₁ ∈ E) (hx₂ : x₂ ∈ E) (hE : E = closure {x₁, x₂})
    (hl : lam * x₁ * lam⁻¹ = x₂) :
    FzValidX D.cT D.cL (D.φ ⟨x₁, D.pf.EP hx₁⟩) := by
  have h2 : (D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩) = D.φ ⟨x₂, D.pf.EP hx₂⟩ :=
    D.cL_x hx₁ hx₂ hl
  have hx1E : x₁ ^ 4 = 1 := D.str.E_exp x₁ hx₁
  have hx2E : x₂ ^ 4 = 1 := D.str.E_exp x₂ hx₂
  have hcomm : x₁ * x₂ = x₂ * x₁ := D.str.W_comm x₁ (D.str.EW hx₁) x₂ (D.str.EW hx₂)
  have hx1c : (D.cT) (D.φ ⟨x₁, D.pf.EP hx₁⟩) = D.φ ⟨x₁, D.pf.EP hx₁⟩ :=
    (D.E_iff ⟨x₁, D.pf.EP hx₁⟩).mp hx₁
  have hx2c : (D.cT) (D.φ ⟨x₂, D.pf.EP hx₂⟩) = D.φ ⟨x₂, D.pf.EP hx₂⟩ :=
    (D.E_iff ⟨x₂, D.pf.EP hx₂⟩).mp hx₂
  have hx1pow : (⟨x₁, D.pf.EP hx₁⟩ : ↥P) ^ 4 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subtype.coe_mk, Subgroup.coe_one]
    exact hx1E
  have hx2pow : (⟨x₂, D.pf.EP hx₂⟩ : ↥P) ^ 4 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subtype.coe_mk, Subgroup.coe_one]
    exact hx2E
  have x1_four : (D.φ ⟨x₁, D.pf.EP hx₁⟩) ^ 4 = 1 := by
    rw [← map_pow, hx1pow, map_one]
  have x2_four : (D.φ ⟨x₂, D.pf.EP hx₂⟩) ^ 4 = 1 := by
    rw [← map_pow, hx2pow, map_one]
  have hcommP : (⟨x₁, D.pf.EP hx₁⟩ : ↥P) * ⟨x₂, D.pf.EP hx₂⟩
      = ⟨x₂, D.pf.EP hx₂⟩ * ⟨x₁, D.pf.EP hx₁⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    exact hcomm
  have comm : (D.φ ⟨x₁, D.pf.EP hx₁⟩) * ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩))
      = ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩)) * (D.φ ⟨x₁, D.pf.EP hx₁⟩) := by
    calc (D.φ ⟨x₁, D.pf.EP hx₁⟩) * ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩))
        = (D.φ ⟨x₁, D.pf.EP hx₁⟩) * (D.φ ⟨x₂, D.pf.EP hx₂⟩) := by rw [h2]
      _ = D.φ ((⟨x₁, D.pf.EP hx₁⟩ : ↥P) * ⟨x₂, D.pf.EP hx₂⟩) := by rw [map_mul]
      _ = D.φ ((⟨x₂, D.pf.EP hx₂⟩ : ↥P) * ⟨x₁, D.pf.EP hx₁⟩) := by rw [hcommP]
      _ = (D.φ ⟨x₂, D.pf.EP hx₂⟩) * (D.φ ⟨x₁, D.pf.EP hx₁⟩) := by rw [map_mul]
      _ = ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩)) * (D.φ ⟨x₁, D.pf.EP hx₁⟩) := by rw [h2]
  refine ⟨hx1c, x1_four, ?_, comm, ?_⟩
  · rw [h2]
    exact x2_four
  · intro y
    constructor
    · intro hy
      have hpE : ((D.φ.symm y : ↥P) : G) ∈ E :=
        (D.E_iff (D.φ.symm y)).mpr (by rw [MulEquiv.apply_symm_apply]; exact hy)
      have hmem : ((D.φ.symm y : ↥P) : G) ∈ Subgroup.closure ({x₁, x₂} : Set G) := by
        rw [← hE]
        exact hpE
      obtain ⟨i, j, hij⟩ :=
        CFSG.GH74.GLS.Stage1.Thm6.Sec13.mem_closure_pair hx1E hx2E hcomm hmem
      refine ⟨⟨i % 4, Nat.mod_lt _ (by norm_num)⟩,
        ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      have hmemP : x₁ ^ i * x₂ ^ j ∈ P := by
        rw [← hij]
        exact (D.φ.symm y).2
      have hpcoe : (D.φ.symm y : ↥P) = ⟨x₁ ^ i * x₂ ^ j, hmemP⟩ := Subtype.ext hij
      have hsub : (⟨x₁ ^ i * x₂ ^ j, hmemP⟩ : ↥P)
          = (⟨x₁, D.pf.EP hx₁⟩ : ↥P) ^ i * (⟨x₂, D.pf.EP hx₂⟩ : ↥P) ^ j := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subtype.coe_mk]
      rw [← MulEquiv.apply_symm_apply D.φ y, hpcoe, hsub,
        map_mul, map_pow, map_pow, h2, pow_eq_pow_mod i x1_four, pow_eq_pow_mod j x2_four]
    · rintro ⟨i, j, rfl⟩
      calc (D.cT) ((D.φ ⟨x₁, D.pf.EP hx₁⟩) ^ (i : ℕ)
              * ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩)) ^ (j : ℕ))
          = ((D.cT) (D.φ ⟨x₁, D.pf.EP hx₁⟩)) ^ (i : ℕ)
              * ((D.cT) ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩))) ^ (j : ℕ) := by
            rw [map_mul, map_pow, map_pow]
        _ = (D.φ ⟨x₁, D.pf.EP hx₁⟩) ^ (i : ℕ)
              * ((D.cT) ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩))) ^ (j : ℕ) := by rw [hx1c]
        _ = (D.φ ⟨x₁, D.pf.EP hx₁⟩) ^ (i : ℕ)
              * (D.φ ⟨x₂, D.pf.EP hx₂⟩) ^ (j : ℕ) := by rw [h2, hx2c]
        _ = (D.φ ⟨x₁, D.pf.EP hx₁⟩) ^ (i : ℕ)
              * ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩)) ^ (j : ℕ) := by rw [← h2]

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
