module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem exists_global_maximal_three_point_prime_overgroup
    (H : Subgroup G) (p : ℕ) (P : Subgroup G) (hP : IsPGroup p P)
    (hthree : 3 ≤ Nat.card (pointFixedSet H P)) :
    ∃ W : Subgroup G, P ≤ W ∧ IsPGroup p W ∧
      3 ≤ Nat.card (pointFixedSet H W) ∧
      ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
        3 ≤ Nat.card (pointFixedSet H V) → V ≤ W := by
  let family : Set (Subgroup G) := {W | P ≤ W ∧ IsPGroup p W ∧
    3 ≤ Nat.card (pointFixedSet H W)}
  have hfinite : family.Finite := Set.toFinite family
  have hnonempty : family.Nonempty := ⟨P, le_rfl, hP, hthree⟩
  obtain ⟨W, hW⟩ := hfinite.exists_maximal hnonempty
  refine ⟨W, hW.1.1, hW.1.2.1, hW.1.2.2, ?_⟩
  intro V hV hWV hVthree
  exact hW.2 ⟨hW.1.1.trans hWV, hV, hVthree⟩ hWV

omit [Finite G] in
theorem global_three_point_prime_maximality_iff
    (H : Subgroup G) (p : ℕ) (W : Subgroup G) :
    (IsPGroup p W ∧ 3 ≤ Nat.card (pointFixedSet H W) ∧
      ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
        3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) ↔
      Maximal (fun V : Subgroup G => IsPGroup p V ∧
        2 < Nat.card (pointFixedSet H V)) W := by
  constructor
  · rintro ⟨hW, hthree, hmax⟩
    refine ⟨⟨hW, by omega⟩, ?_⟩
    intro V hV hWV
    exact hmax V hV.1 hWV (by omega)
  · rintro ⟨⟨hW, hthree⟩, hmax⟩
    exact ⟨hW, by omega, fun V hV hWV hVthree => hmax ⟨hV, by omega⟩ hWV⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
