module

public import CFSG.GH74.E2.LocalLeaves
public import CFSG.GH74.E2.K0Rest
public import CFSG.GH74.AS16.E2.Pump2
public import CFSG.GH74.KGroups.A5
public import CFSG.GH74.KGroups.A6
public import CFSG.GH74.KGroups.L27
public import CFSG.GH74.KGroups.L217
public import CFSG.GH74.KGroups.L28
public import CFSG.GH74.KGroups.L33Tables
public import CFSG.GH74.KGroups.M11Tables
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.KGroups

theorem m11Tables : M11Tables where
  tables := by
    intro K _ _ h
    obtain ⟨e⟩ := M11.equiv_of_sporadic h
    exact ⟨M11.one_class e, M11.sylow_sd16 e⟩
  aut_inner := by
    intro K _ _ h φ
    exact M11.out_trivial h φ

theorem l33Tables : L33Tables where
  tables := by
    intro K _ _ h
    obtain ⟨e⟩ := L33.equiv_of_lieModel h
    exact ⟨L33.one_class e, L33.sylow_sd16 e⟩

theorem shapeA5_equiv
    {K : Type} [Group K] (h : ShapeA5 K) :
    Nonempty (K ≃* A5.QP.originalSubgroup) := by
  rcases h with h | h | h
  · exact A5.equiv_of_alt h.some
  · exact A5.equiv_of_lieModel22 h
  · exact A5.equiv_of_lieModel25 h

theorem shapeL27_equiv {K : Type} [Group K] (h : ShapeL27 K) :
    Nonempty (K ≃* L27.QP.originalSubgroup) := by
  rcases h with h | h
  · exact L27.equiv_of_lieModel h
  · exact L27.equiv_of_lieModel3 h

theorem shapeA6_equiv {K : Type} [Group K] (h : ShapeA6 K) :
    Nonempty (K ≃* A6.QP.originalSubgroup) := by
  rcases h with h | h
  · exact A6.equiv_of_alt6 h
  · exact A6.equiv_of_lieModel h

@[expose] def Covered8 (K : Type) [Group K] : Prop :=
  ShapeA5 K ∨ ShapeL27 K ∨ ShapeA6 K ∨ ShapeL217 K ∨ ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨
    ShapeM11 K

@[expose] def Uncovered3 (K : Type) [Group K] : Prop :=
  ShapeSz8 K ∨ Shape2M12 K ∨ Shape2Sz8 K

theorem k0Shape_split {K : Type} [Group K] (h : K0Shape K) : Covered8 K ∨ Uncovered3 K := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

section Covered

variable {K : Type} [Group K]

theorem covered_autRank_ge5
    (h : Covered8 K) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (B : Subgroup (MulAut K)) (hB : ElemAb p B) : Nat.card B ≤ p := by
  rcases h with h | h | h | h | h | h | h | h
  · obtain ⟨e⟩ := shapeA5_equiv h
    exact A5.autRank_ge5 e p hp h5 B hB
  · obtain ⟨e⟩ := shapeL27_equiv h
    exact L27.autRank_ge5 e p hp h5 B hB
  · obtain ⟨e⟩ := shapeA6_equiv h
    exact A6.autRank_ge5 e p hp h5 B hB
  · obtain ⟨e⟩ := L217.equiv_of_lieModel h
    exact L217.autRank_ge5 e p hp h5 B hB
  · exact L28.autRank_ge5 h p hp h5 B hB
  · obtain ⟨e⟩ := L33.equiv_of_lieModel h
    exact L33.autRank_ge5 e p hp h5 B hB
  · obtain ⟨e⟩ := U33.equiv_of_lieModel h
    exact U33.autRank_ge5 e p hp h5 B hB
  · exact M11.autRank_ge5 h p hp h5 B hB

theorem covered_autRank3_le_two
    (h : Covered8 K) (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) :
    Nat.card R ≤ 9 := by
  rcases h with h | h | h | h | h | h | h | h
  · obtain ⟨e⟩ := shapeA5_equiv h
    exact A5.autRank3_le_two e R hR
  · obtain ⟨e⟩ := shapeL27_equiv h
    exact L27.autRank3_le_two e R hR
  · obtain ⟨e⟩ := shapeA6_equiv h
    exact A6.autRank3_le_two e R hR
  · obtain ⟨e⟩ := L217.equiv_of_lieModel h
    exact L217.autRank3_le_two e R hR
  · exact L28.autRank3_le_two h R hR
  · obtain ⟨e⟩ := L33.equiv_of_lieModel h
    exact L33.autRank3_le_two e R hR
  · obtain ⟨e⟩ := U33.equiv_of_lieModel h
    exact U33.autRank3_le_two e R hR
  · exact M11.autRank3_le_two h R hR

theorem covered_autRank3_le_one
    (h : ShapeA5 K ∨ ShapeL27 K ∨ ShapeL217 K)
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 3 := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := shapeA5_equiv h
    exact A5.autRank3_le_one e R hR
  · obtain ⟨e⟩ := shapeL27_equiv h
    exact L27.autRank3_le_one e R hR
  · obtain ⟨e⟩ := L217.equiv_of_lieModel h
    exact L217.autRank3_le_one e R hR

theorem covered_inner3
    (h : ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K) (φ : MulAut K) (hφ : φ ^ 3 = 1) :
    ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := shapeA6_equiv h
    exact A6.inner3 e φ hφ
  · obtain ⟨e⟩ := L33.equiv_of_lieModel h
    exact L33.inner3 e φ hφ
  · exact M11.inner3 h φ hφ

theorem covered_inner3_small
    (h : ShapeA5 K ∨ ShapeL27 K ∨ ShapeL217 K) (φ : MulAut K)
    (hφ : φ ^ 3 = 1) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := shapeA5_equiv h
    exact A5.inner3 e φ hφ
  · obtain ⟨e⟩ := shapeL27_equiv h
    exact L27.inner3 e φ hφ
  · obtain ⟨e⟩ := L217.equiv_of_lieModel h
    exact L217.inner3 e φ hφ

theorem covered_centralizer3
    (h : ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K) (B : Subgroup K)
    (hB : ElemAb 3 B) (hcard : Nat.card B = 9) (k : K) (hk : ∀ b ∈ B, k * b = b * k) : k ∈ B := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := shapeA6_equiv h
    exact A6.centralizer3 e B hB hcard k hk
  · obtain ⟨e⟩ := L33.equiv_of_lieModel h
    exact L33.centralizer3 e B hB hcard k hk
  · exact M11.centralizer3 h B hB hcard k hk

theorem covered_autCentralizer
    (h : ShapeA6 K ∨ ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨ ShapeM11 K)
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) (hcard : Nat.card R = 9) (ψ : MulAut K)
    (hψ : ψ ^ 2 = 1) (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  rcases h with h | h | h | h | h
  · obtain ⟨e⟩ := shapeA6_equiv h
    exact A6.autCentralizer e R hR hcard ψ hψ hc
  · exact L28.autCentralizer h R hR hcard ψ hψ hc
  · obtain ⟨e⟩ := L33.equiv_of_lieModel h
    exact L33.autCentralizer e R hR hcard ψ hψ hc
  · obtain ⟨e⟩ := U33.equiv_of_lieModel h
    exact U33.autCentralizer e R hR hcard ψ hψ hc
  · exact M11.autCentralizer h R hR hcard ψ hψ hc

theorem covered_fixed_not_quasisimple
    (h : Covered8 K) (α : MulAut K) (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1) (L : Subgroup K) (hL : ∀ x ∈ L, α x = x) : ¬ IsQuasisimple ↥L := by
  intro hq
  have hsol : Group.IsSolvable ↥L := by
    rcases h with h | h | h | h | h | h | h | h
    · obtain ⟨e⟩ := shapeA5_equiv h
      exact A5.fixed_solvable e α hα2 hα1 L hL
    · obtain ⟨e⟩ := shapeL27_equiv h
      exact L27.fixed_solvable e α hα2 hα1 L hL
    · obtain ⟨e⟩ := shapeA6_equiv h
      exact A6.fixed_solvable e α hα2 hα1 L hL
    · obtain ⟨e⟩ := L217.equiv_of_lieModel h
      exact L217.fixed_solvable e α hα2 hα1 L hL
    · exact L28.fixed_solvable h α hα2 hα1 L hL
    · obtain ⟨e⟩ := L33.equiv_of_lieModel h
      exact L33.fixed_solvable e α hα2 hα1 L hL
    · obtain ⟨e⟩ := U33.equiv_of_lieModel h
      exact U33.fixed_solvable e α hα2 hα1 L hL
    · exact M11.fixed_solvable h α hα2 hα1 L hL
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq hsol

end Covered

structure K0Rest2 : Prop where
  autRank_ge5 : ∀ (K : Type) [Group K] [Finite K], Uncovered3 K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ B : Subgroup (MulAut K), ElemAb p B → Nat.card B ≤ p
  autRank3_le_two : ∀ (K : Type) [Group K] [Finite K], Uncovered3 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 9
  autRank3_le_one : ∀ (K : Type) [Group K] [Finite K], (ShapeSz8 K ∨ Shape2Sz8 K) →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 3
  rank_ge4_sz : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K →
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 4 ≤ Group.rank U
  autCentralizer : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R = 9 → ∀ ψ : MulAut K, ψ ^ 2 = 1 →
      (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1
  pumpUp : ∀ (K : Type) [Group K] [Finite K], Uncovered3 K → ∀ α : MulAut K, α ^ 2 = 1 →
    α ≠ 1 → ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → IsQuasisimple ↥L →
      (Nat.card ↥L = 60 ∨ Nat.card ↥L = 120) ∧ Shape2M12 K

theorem k0DataRest_of_rest2
    (h : K0Rest2) : K0DataRest where
  autRank_ge5 := by
    intro K _ _ hK p hp h5 B hB
    rcases k0Shape_split hK with hc | hu
    · exact covered_autRank_ge5 hc p hp h5 B hB
    · exact h.autRank_ge5 K hu p hp h5 B hB

theorem k0Data3Rest_of_rest2
    (h : K0Rest2) : K0Data3Rest where
  autRank3_le_two := by
    intro K _ _ hK R hR
    rcases k0Shape_split hK with hc | hu
    · exact covered_autRank3_le_two hc R hR
    · exact h.autRank3_le_two K hu R hR
  autRank3_le_one := by
    intro K _ _ hK R hR
    rcases hK with hK | hK | hK | hK | hK
    · exact covered_autRank3_le_one (Or.inl hK) R hR
    · exact covered_autRank3_le_one (Or.inr (Or.inl hK)) R hR
    · exact covered_autRank3_le_one (Or.inr (Or.inr hK)) R hR
    · exact h.autRank3_le_one K (Or.inl hK) R hR
    · exact h.autRank3_le_one K (Or.inr hK) R hR
  rank_ge4_sz := h.rank_ge4_sz
  inner3 := by
    intro K _ _ hK φ hφ
    exact covered_inner3 hK φ hφ
  centralizer3 := by
    intro K _ _ hK B hB hcard k hk
    exact covered_centralizer3 hK B hB hcard k hk
  inner3_small := by
    intro K _ _ hK φ hφ
    exact covered_inner3_small hK φ hφ
  autCentralizer := by
    intro K _ _ hK R hR hcard ψ hψ hc
    rcases hK with hK | hK | hK | hK | hK | hK
    · exact covered_autCentralizer (Or.inl hK) R hR hcard ψ hψ hc
    · exact covered_autCentralizer (Or.inr (Or.inl hK)) R hR hcard ψ hψ hc
    · exact covered_autCentralizer (Or.inr (Or.inr (Or.inl hK))) R hR hcard ψ hψ hc
    · exact covered_autCentralizer (Or.inr (Or.inr (Or.inr (Or.inl hK)))) R hR hcard ψ hψ hc
    · exact covered_autCentralizer (Or.inr (Or.inr (Or.inr (Or.inr hK)))) R hR hcard ψ hψ hc
    · exact h.autCentralizer K hK R hR hcard ψ hψ hc

theorem pumpUpData_of_rest2
    (h : K0Rest2) : PumpUpData where
  card_quasisimple_fixed := by
    intro K _ _ hK α hα2 hα1 L hL hq
    rcases k0Shape_split hK with hc | hu
    · exact absurd hq (covered_fixed_not_quasisimple hc α hα2 hα1 L hL)
    · exact (h.pumpUp K hu α hα2 hα1 L hL hq).1

theorem pumpUpData2_of_rest2
    (h : K0Rest2) : CFSG.GH74.AS16.E2.PumpUpData2 where
  shape_of_fixed := by
    intro K _ _ hK α hα2 hα1 L hL hq
    rcases k0Shape_split hK with hc | hu
    · exact absurd hq (covered_fixed_not_quasisimple hc α hα2 hα1 L hL)
    · exact (h.pumpUp K hu α hα2 hα1 L hL hq).2

end CFSG.GH74.E2
