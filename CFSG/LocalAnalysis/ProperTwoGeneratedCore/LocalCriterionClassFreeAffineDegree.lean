module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {F Ω : Type*} [Group F] [Finite F] [MulAction F Ω] [Finite Ω]

omit [Finite F] [Finite Ω] in
theorem degree_dvd_group_order_of_pretransitive
    (htrans : MulAction.IsPretransitive F Ω) (a : Ω) :
    Nat.card Ω ∣ Nat.card F := by
  let : MulAction.IsPretransitive F Ω := htrans
  have horbit : Nat.card (MulAction.orbit F a) = Nat.card Ω := by
    rw [MulAction.orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ Ω)
  have hcard : Nat.card (MulAction.orbit F a) *
      Nat.card (MulAction.stabilizer F a) = Nat.card F := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup F a)
  rw [horbit] at hcard
  exact ⟨Nat.card (MulAction.stabilizer F a), hcard.symm⟩

omit [Finite F] in
theorem two_pretransitive_group_even
    (htwo : MulAction.IsMultiplyPretransitive F Ω 2)
    (hdegree : 2 ≤ Nat.card Ω) : Even (Nat.card F) := by
  classical
  let : Fintype Ω := Fintype.ofFinite Ω
  have hemb : Nonempty (Fin 2 ↪ Ω) := Function.Embedding.nonempty_of_card_le
    (by simpa [Nat.card_eq_fintype_card] using hdegree)
  obtain ⟨a⟩ := hemb
  have hpairdvd := degree_dvd_group_order_of_pretransitive htwo a
  have hpaircard : Nat.card (Fin 2 ↪ Ω) = Nat.card Ω * (Nat.card Ω - 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      mul_one, ← Nat.card_eq_fintype_card]
    exact Nat.mul_comm _ _
  rw [hpaircard] at hpairdvd
  obtain ⟨r, hr⟩ := hpairdvd
  rw [hr]
  exact (Nat.even_mul_pred_self (Nat.card Ω)).mul_right r

omit [Finite F] in
theorem two_pretransitive_point_stabilizer_isCoatom
    (htwo : MulAction.IsMultiplyPretransitive F Ω 2)
    (hdegree : 2 ≤ Nat.card Ω) (a : Ω) :
    IsCoatom (MulAction.stabilizer F a) := by
  let : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : MulAction.IsPreprimitive F Ω := MulAction.isPreprimitive_of_is_two_pretransitive htwo
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive F a

variable {G : Type*} [Group G] [Finite G]

theorem maximal_prime_common_induced_image_even
    (H : Subgroup G)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (W : Subgroup G) (hW : IsPGroup p W)
    (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    Even (Nat.card (pointwiseKernelNormalizerImage H W)) :=
  two_pretransitive_group_even
    (maximal_prime_common_induced_image_two_pretransitive H hdoubly p hp W hW hthree hmax)
    (by omega)

theorem maximal_prime_common_induced_image_stabilizer_isCoatom
    (H : Subgroup G)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (W : Subgroup G) (hW : IsPGroup p W)
    (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (a : pointFixedSet H W) :
    IsCoatom (MulAction.stabilizer (pointwiseKernelNormalizerImage H W) a) :=
  two_pretransitive_point_stabilizer_isCoatom
    (maximal_prime_common_induced_image_two_pretransitive H hdoubly p hp W hW hthree hmax)
    (by omega) a

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
