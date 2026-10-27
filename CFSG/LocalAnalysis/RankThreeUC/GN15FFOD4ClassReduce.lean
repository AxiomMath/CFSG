module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Center

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.Open CFSG.Quasithin

theorem natural_classification_of_leaves
    (hTwo : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
      ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ (L E : Subgroup (MulAut V)), (L ≃* orthElementaryGroup (quadPlus 4 K)) →
        CFSG.QuasithinUnique.Setup.X1.IsIrrOn L →
        E ≤ Subgroup.normalizer (L : Set (MulAut V)) → E ≠ ⊥ → IsElemAbelian2 E →
        IsQuadratic E → Nat.card V ≤ Nat.card E * Nat.card (fixV E) →
        ∃ (ψ : L ≃* orthElementaryGroup (quadPlus 4 K)) (φ : Additive V ≃+ (Fin 4 ⊕ Fin 4 → K)),
          ∀ (l : L) (v : V), φ (Additive.ofMul ((l : MulAut V) v)) =
            (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (Additive.ofMul v)))
    (hLarge : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ (L E : Subgroup (MulAut V)), (L ≃* orthElementaryGroup (quadPlus 4 K)) →
        CFSG.QuasithinUnique.Setup.X1.IsIrrOn L →
        E ≤ Subgroup.normalizer (L : Set (MulAut V)) → E ≠ ⊥ → IsElemAbelian2 E →
        IsQuadratic E → Nat.card V ≤ Nat.card E * Nat.card (fixV E) →
        ∃ (ψ : L ≃* orthElementaryGroup (quadPlus 4 K)) (φ : Additive V ≃+ (Fin 4 ⊕ Fin 4 → K)),
          ∀ (l : L) (v : V), φ (Additive.ofMul ((l : MulAut V) v)) =
            (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (Additive.ofMul v))) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ L E : Subgroup (MulAut V), CFSG.QuasithinUnique.Setup.X1.IsIrrOn L → Group.IsPerfect L →
        (∃ f : ℕ, StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 f) →
        E ≤ Subgroup.normalizer (L : Set (MulAut V)) → E ≠ ⊥ → IsElemAbelian2 E →
        IsQuadratic E → Nat.card V ≤ Nat.card E * Nat.card (fixV E) →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
          (χ : L ≃* orthElementaryGroup (quadPlus 4 K)) (φ : Additive V ≃+ (Fin 4 ⊕ Fin 4 → K)),
          ∀ (l : L) (v : V), φ (Additive.ofMul ((l : MulAut V) v)) =
            (χ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (Additive.ofMul v)) := by
  intro V _ _ hV L E hirr hperf ⟨f, hmodel⟩ hEN hE hEel hEq hoff
  obtain ⟨K, hF, hFin, hChar, hK, ⟨χ⟩⟩ :=
    exists_mulEquiv_of_model hV L hirr hperf hmodel
  let : Field K := hF
  let : Finite K := hFin
  let : CharP K 2 := hChar
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · have hf1 : f = 1 := by
      have hfpos : 1 ≤ f := hmodel.1.2.1
      omega
    obtain rfl : f = 1 := hf1
    have hK2 : Nat.card K = 2 := by
      rw [hK]
      norm_num
    obtain ⟨ψ, φ, hφ⟩ := hTwo K hK2 V hV L E χ hirr hEN hE hEel hEq hoff
    exact ⟨K, hF, hFin, hChar, ψ, φ, hφ⟩
  · have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
    obtain ⟨ψ, φ, hφ⟩ := hLarge K hK4 V hV L E χ hirr hEN hE hEel hEq hoff
    exact ⟨K, hF, hFin, hChar, ψ, φ, hφ⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

end
