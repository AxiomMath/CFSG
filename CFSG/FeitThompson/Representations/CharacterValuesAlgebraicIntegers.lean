module

public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import CFSG.FeitThompson.Representations.StableModuleAlgebraicIntegrality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Polynomial

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V] {g : G}

theorem isIntegral_int_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsIntegral ℤ z :=
  IsIntegral.of_pow hn (hz ▸ isIntegral_one)

theorem Representation.isIntegral_character_of_isOfFinOrder [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hg : IsOfFinOrder g) : IsIntegral ℤ (ρ.character g) := by
  obtain ⟨b, d, hd, hpow⟩ := Representation.exists_basis_eigenvector ρ hg
  rw [Representation.character_eq_sum_of_eigenbasis ρ b d hd]
  exact IsIntegral.sum _ fun i _ => isIntegral_int_of_pow_eq_one hg.orderOf_pos (hpow i)

theorem Representation.isIntegral_character [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) : IsIntegral ℤ (ρ.character g) :=
  Representation.isIntegral_character_of_isOfFinOrder ρ (isOfFinOrder_of_finite g)

theorem FDRep.isIntegral_character [Finite G] (W : FDRep ℂ G) (g : G) :
    IsIntegral ℤ (W.character g) :=
  Representation.isIntegral_character W.ρ g

theorem irreducibleCharacters.isIntegral [Finite G] {χ : G → ℂ}
    (hχ : χ ∈ irreducibleCharacters G) (g : G) : IsIntegral ℤ (χ g) := by
  obtain ⟨W, -, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  exact FDRep.isIntegral_character W g

theorem exists_monic_natDegree_pos_character [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ∃ p : ℤ[X], p.Monic ∧ 0 < p.natDegree ∧ aeval (ρ.character g) p = 0 :=
  (isIntegral_int_iff_exists_monic_natDegree_pos _).1 (Representation.isIntegral_character ρ g)

theorem Representation.character_mem_integralClosure [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) : ρ.character g ∈ integralClosure ℤ ℂ :=
  Representation.isIntegral_character ρ g

end CFSG.FeitThompson
