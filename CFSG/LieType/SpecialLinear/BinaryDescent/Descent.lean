module

public import CFSG.LieType.SpecialLinear.BinaryDescent.Irreducibility

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open ExteriorModel

variable {n i j : ℕ} {F : Type*} [Field F] [CharP F 2]

theorem exists_addEquiv_extTwist_of_extend {V k : Type*} [AddCommGroup V]
    [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) V] [Field k] [Algebra F k] [Fintype F]
    (hi : 1 ≤ i) (hin : i < n)
    (hV : IsIrreducibleAdd (fun (g : Matrix.SpecialLinearGroup (Fin n) F) (v : V) => g • v))
    (Φ : V →+ (Set.powersetCard (Fin n) i → k)) (hΦ : Φ ≠ 0)
    (hΦeq : ∀ g v, Φ (g • v) =
      (extTwist n i j F g).map (algebraMap F k) *ᵥ Φ v) :
    ∃ β : V ≃+ (Set.powersetCard (Fin n) i → F),
      ∀ g v, β (g • v) = extTwist n i j F g *ᵥ β v := by
  classical
  obtain ⟨Ψ, hΨ0, hΨ⟩ := exists_addHom_of_extend (extTwist n i j F) Φ hΦ hΦeq
  have hbij := bijective_of_ne_zero_of_irreducible (extTwist n i j F) hV
    (isIrreducibleAdd_extTwist hi hin) Ψ hΨ0 hΨ
  exact ⟨AddEquiv.ofBijective Ψ hbij, hΨ⟩

end CFSG.LieType.SpecialLinear
