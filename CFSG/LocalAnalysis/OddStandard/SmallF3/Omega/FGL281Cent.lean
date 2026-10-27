module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Fix

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.GorensteinWalter

universe u

variable {K : Type u} [Field K] [Finite K]

theorem fg_fixes_decomp {P : Subgroup (PSL2 K)} {A : Subgroup (MulAut (PSL2 K))}
    (hA : ∀ α ∈ A, ∀ x ∈ P, α x = x) (a : ↥A) :
    ∃ (M : Matrix.GeneralLinearGroup (Fin 2) K) (σ : K ≃+* K),
      fgFieldPart K (a : MulAut (PSL2 K)) = σ ∧
      (a : MulAut (PSL2 K)) = semilinearAction K (SemidirectProduct.inl
        (Matrix.ProjGenLinGroup.mk M) * SemidirectProduct.inr σ) ∧
      ∀ x ∈ P, semilinearAction K (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
        SemidirectProduct.inr σ) x = x := by
  obtain ⟨M, σ, hα, hσ⟩ := fg_exists_decomp (a : MulAut (PSL2 K))
  exact ⟨M, σ, hσ, hα, fun x hx => by rw [← hα]; exact hA a a.2 x hx⟩

theorem fg_fieldPart_injective {P : Subgroup (PSL2 K)} (hP : ⁅P, P⁆ = P) (hne : P ≠ ⊥)
    {A : Subgroup (MulAut (PSL2 K))} (hA : ∀ α ∈ A, ∀ x ∈ P, α x = x) :
    Function.Injective ((fgFieldPart K).comp A.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  obtain ⟨M, σ, hσ, hα, hfix⟩ := fg_fixes_decomp hA a
  have hσ1 : σ = 1 := by
    rw [← hσ]
    exact ha
  subst hσ1
  have hM := fg_central_of_sigma_one hP hne hfix
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hα, hM]
  simp

theorem fg_card_le_two_of_fixes (hK : Nat.card K = 81)
    {P : Subgroup (PSL2 K)} (hP : ⁅P, P⁆ = P) (hne : P ≠ ⊥)
    {A : Subgroup (MulAut (PSL2 K))} (hA : ∀ α ∈ A, ∀ x ∈ P, α x = x) : Nat.card A ≤ 2 := by
  let f := (fgFieldPart K).comp A.subtype
  have hinj : Function.Injective f := fg_fieldPart_injective hP hne hA
  have hsq : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨M, σ, hσ, -, hfix⟩ := fg_fixes_decomp hA a
    have hfa : f a = σ := hσ
    rw [hfa]
    exact fg_sq_of_fixes hK hP hne hfix
  calc Nat.card A ≤ Nat.card f.range :=
        Nat.card_le_card_of_injective f.rangeRestrict
          (fun a b h => hinj (congrArg Subtype.val h))
    _ ≤ 2 := card_le_two_of_sq_ringAut f.range hsq

end CFSG.OddStandard.SmallF3.Omega
