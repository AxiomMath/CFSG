module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOrders

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open scoped Matrix LinearAlgebra.Projectivization

variable (a : ℕ) (K : Type) [Field K]

@[expose] def suppliedSuzukiOvoidInfinity : ℙ K (Fin 4 → K) :=
  Projectivization.mk K ![0, 0, 0, 1] (by simp)

@[expose] def suppliedSuzukiOvoidFinitePoint (x y : K) : ℙ K (Fin 4 → K) :=
  Projectivization.mk K ![1, x, y, x ^ (2 ^ (a + 1) + 2) + x * y + y ^ 2 ^ (a + 1)]
    (by simp)

@[expose] def suppliedSuzukiOvoidSet : Set (ℙ K (Fin 4 → K)) :=
  {suppliedSuzukiOvoidInfinity K} ∪
    Set.range fun z : K × K => suppliedSuzukiOvoidFinitePoint a K z.1 z.2

theorem suppliedSuzukiOvoidFinitePoint_injective :
    Function.Injective (fun z : K × K => suppliedSuzukiOvoidFinitePoint a K z.1 z.2) := by
  intro z w hzw
  dsimp only [suppliedSuzukiOvoidFinitePoint] at hzw
  rw [Projectivization.mk_eq_mk_iff] at hzw
  obtain ⟨c, hc⟩ := hzw
  have hcOne : (c : K) = 1 := by
    have h := congrFun hc (0 : Fin 4)
    simpa [Units.smul_def] using h
  apply Prod.ext
  · have h := congrFun hc (1 : Fin 4)
    simpa [Units.smul_def, hcOne] using h.symm
  · have h := congrFun hc (2 : Fin 4)
    simpa [Units.smul_def, hcOne] using h.symm

theorem suppliedSuzukiOvoidInfinity_not_mem_range :
    suppliedSuzukiOvoidInfinity K ∉
      Set.range fun z : K × K => suppliedSuzukiOvoidFinitePoint a K z.1 z.2 := by
  rintro ⟨z, hz⟩
  dsimp only [suppliedSuzukiOvoidInfinity, suppliedSuzukiOvoidFinitePoint] at hz
  rw [Projectivization.mk_eq_mk_iff] at hz
  obtain ⟨c, hc⟩ := hz
  have h := congrFun hc (0 : Fin 4)
  simp at h

@[expose] def suppliedSuzukiOvoidParametrization :
    Option (K × K) ≃ {p : ℙ K (Fin 4 → K) // p ∈ suppliedSuzukiOvoidSet a K} := by
  let f : Option (K × K) →
      {p : ℙ K (Fin 4 → K) // p ∈ suppliedSuzukiOvoidSet a K}
    | none => ⟨suppliedSuzukiOvoidInfinity K, Or.inl rfl⟩
    | some z => ⟨suppliedSuzukiOvoidFinitePoint a K z.1 z.2, Or.inr ⟨z, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        exact False.elim (suppliedSuzukiOvoidInfinity_not_mem_range a K
          ⟨v, (congrArg Subtype.val huv).symm⟩)
    | some u =>
      cases v with
      | none =>
        exact False.elim (suppliedSuzukiOvoidInfinity_not_mem_range a K
          ⟨u, congrArg Subtype.val huv⟩)
      | some v =>
        exact congrArg some (suppliedSuzukiOvoidFinitePoint_injective a K
          (congrArg Subtype.val huv))
  · intro p
    rcases p.property with hp | ⟨z, hz⟩
    · exact ⟨none, Subtype.ext (Set.mem_singleton_iff.mp hp).symm⟩
    · exact ⟨some z, Subtype.ext hz⟩

theorem suppliedSuzukiOvoid_card [Finite K] :
    Nat.card {p : ℙ K (Fin 4 → K) // p ∈ suppliedSuzukiOvoidSet a K} =
      (Nat.card K) ^ 2 + 1 := by
  let := Fintype.ofFinite K
  rw [← Nat.card_congr (suppliedSuzukiOvoidParametrization a K)]
  simp [Nat.card_eq_fintype_card, pow_two]

instance suppliedSuzukiOvoid_finite [Finite K] :
    Finite {p : ℙ K (Fin 4 → K) // p ∈ suppliedSuzukiOvoidSet a K} :=
  Finite.of_equiv (Option (K × K)) (suppliedSuzukiOvoidParametrization a K)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
