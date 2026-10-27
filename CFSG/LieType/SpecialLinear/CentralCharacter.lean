module

public import CFSG.LieType.SpecialLinear.CurtisDatum
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Central
public import CFSG.HardMathSupport.U4FF.ClassChar

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

noncomputable section

attribute [local instance] Fintype.ofFinite

section Exponent

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
variable {k V : Type*} [Field k] [Algebra F k] [CharP k p]
  [AddCommGroup V] [Module k V]

omit [CharP k p] in
theorem IsCoverType.exists_exponent
    {ρ : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V}
    {y : V} {χ : Matrix.SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F p) ρ y χ J) (i : Fin m) :
    ∃ e : ℕ, e < Nat.card F - 1 ∧
      ∀ u : Fˣ, χ (hdiag m F i u) = (algebraMap F k (u : F)) ^ e := by
  have hmem : ∀ u : Fˣ, hdiag m F i u ∈ (curtisDatum m F p).H.comap (MonoidHom.id _) :=
    fun u => (rankOne m F p).hh_mem i u
  obtain ⟨e, he, h⟩ := CFSG.HardMathSupport.U4FF.exists_char_exponent
    (fun u : Fˣ => χ (hdiag m F i u))
    (fun u v => by rw [hdiag_mul, ht.chi_mul_of_mem (hmem u) (hmem v)])
    (by rw [hdiag_one, ht.chi_one])
  exact ⟨e, by rwa [Nat.card_units] at he, h⟩

@[expose] noncomputable def IsCoverType.exponent
    {ρ : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V}
    {y : V} {χ : Matrix.SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F p) ρ y χ J) (i : Fin m) : ℕ :=
  Classical.choose (CFSG.LieType.SpecialLinear.IsCoverType.exists_exponent m F p ht i)

omit [CharP k p] in
theorem IsCoverType.exponent_lt
    {ρ : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V}
    {y : V} {χ : Matrix.SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F p) ρ y χ J) (i : Fin m) :
    CFSG.LieType.SpecialLinear.IsCoverType.exponent m F p ht i < Nat.card F - 1 :=
  (Classical.choose_spec (CFSG.LieType.SpecialLinear.IsCoverType.exists_exponent m F p ht i)).1

omit [CharP k p] in
theorem IsCoverType.chi_hdiag_eq_pow
    {ρ : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V}
    {y : V} {χ : Matrix.SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F p) ρ y χ J) (i : Fin m) (u : Fˣ) :
    χ (hdiag m F i u) = (algebraMap F k (u : F)) ^ CFSG.LieType.SpecialLinear.IsCoverType.exponent m F p ht i :=
  (Classical.choose_spec (CFSG.LieType.SpecialLinear.IsCoverType.exists_exponent m F p ht i)).2 u

end Exponent

end

end CFSG.LieType.SpecialLinear
