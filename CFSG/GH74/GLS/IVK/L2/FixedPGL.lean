module

public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.CharacterTheory.Semidihedral.FixedFieldCentralizer

public section

namespace CFSG.GH74.GLS.IVK

open CFSG.GorensteinWalter

section PGLIncl

variable {F : Type*} [Field F]

@[expose] noncomputable def pgl2Incl (σ : F ≃+* F) : PGL2 (fixedField σ) →* PGL2 F :=
  Matrix.ProjGenLinGroup.map (fixedField σ).subtype

theorem pgl2Incl_mk (σ : F ≃+* F) (M : GL (Fin 2) (fixedField σ)) :
    pgl2Incl σ (Matrix.ProjGenLinGroup.mk M) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (fixedField σ).subtype M) := rfl

theorem pgl2Incl_injective (σ : F ≃+* F) : Function.Injective (pgl2Incl σ) :=
  CFSG.Semidihedral.FixedFieldCentralizer.pgl_map_injective _

theorem mem_range_pgl2Incl_iff (σ : F ≃+* F) (A : PGL2 F) :
    A ∈ (pgl2Incl σ).range ↔ pgl2RingEquiv σ A = A := by
  have h := CFSG.Semidihedral.FixedFieldCentralizer.pgl_fixed_iff F (Subgroup.zpowers σ) A
  change (∀ τ : Subgroup.zpowers σ, pgl2FieldAut F (τ : F ≃+* F) A = A) ↔
    A ∈ (pgl2Incl σ).range at h
  rw [← h]
  constructor
  · intro hall
    exact hall ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro hσ τ
    have hmem : σ ∈ (MulAction.stabilizer (MulAut (PGL2 F)) A).comap (pgl2FieldAut F) := by
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      exact hσ
    have := (Subgroup.zpowers_le.mpr hmem) τ.2
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at this
    exact this

theorem card_range_pgl2Incl [Finite F] (σ : F ≃+* F) :
    Nat.card ↥(pgl2Incl σ).range =
      Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := by
  rw [← pgl2_card_formula (fixedField σ)]
  exact (Nat.card_congr (MonoidHom.ofInjective (pgl2Incl_injective σ)).toEquiv).symm

theorem isOddPrimePower_of_odd_card [Finite F] (h : Odd (Nat.card F)) :
    IsOddPrimePower (Nat.card F) := by
  have := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' F
  have hq : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  refine ⟨p, n, hp, ?_, n.pos, hq⟩
  by_contra hpo
  have h2 : p = 2 := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · exact h2
    · exact absurd h2 hpo
  have hq2 : Even (Nat.card F) := by
    rw [hq, h2]
    exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  exact (Nat.not_even_iff_odd.mpr h) hq2

end PGLIncl

end CFSG.GH74.GLS.IVK
