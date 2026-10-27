module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.PropVDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.PropVVert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.A2Cases

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem residual_or_kDatum_of_violation (hI : Phase1Inputs) (hL : Leaves1) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Catalog G)
    (hbal : ∀ z : G, orderOf z = 2 → oddCore ↥(centralizer ({z} : Set G)) = ⊥) {x y : G}
    {X K : Subgroup G} (h : A2Config G x y X K) (hX : IsFStar ↥X) (hK : ¬ IsFStar ↥K) :
    IsResidualA2 ↥K ∨ KDatum ↥K := by
  have hbalY : oddCore (centralizer ({y} : Set G)) = ⊥ := hbal y h.oy
  obtain ⟨hKc, hcases⟩ := a2Config_cases hbalY h
  have hKq : IsQuasisimple ↥K := hKc.isQuasisimple
  have hZ : IsPGroup 2 ↥(center ↥K) := isPGroup_two_center_of_isComponentIn hbalY hKc
  have hH : centralizer ({y} : Set G) ≠ ⊤ :=
    Helpers.centralizer_ne_top_of_involution G hnonab y h.oy
  have hcat : Catalog (↥K ⧸ center ↥K) :=
    catalog_quotient_center_of_isComponentIn hKP hH hKc
  rcases hcases with ⟨hKx, hXK, hXT⟩ | ⟨hne, hcomm, φ, hφ, hXφ, hker⟩
  ·
    have hx2 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [h.ox] at this
    have hxx : x * x = 1 := by rwa [pow_two] at hx2
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hσ : ∀ k : ↥K, conjAut K x hKx (conjAut K x hKx k) = k := by
      intro k
      apply Subtype.ext
      rw [coe_conjAut_apply, coe_conjAut_apply]
      calc x * (x * (k : G) * x⁻¹) * x⁻¹
          = x * x * (k : G) * (x⁻¹ * x⁻¹) := by group
        _ = (k : G) := by rw [hxx, hxinv, hxx]; group
    have hfix : FixedCommutingProduct.fixedSubgroup (conjAut K x hKx) =
        (K ⊓ centralizer ({x} : Set G)).subgroupOf K := by
      ext k
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      change conjAut K x hKx k = k ↔ (k : G) ∈ K ∧ (k : G) ∈ centralizer ({x} : Set G)
      constructor
      · intro hk
        refine ⟨k.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        have hk' : x * (k : G) * x⁻¹ = (k : G) := by
          have := congrArg (fun z : ↥K => (z : G)) hk
          rwa [coe_conjAut_apply] at this
        have h2 := congrArg (fun t : G => t * x) hk'
        simpa [mul_assoc] using h2
      · rintro ⟨-, hc⟩
        apply Subtype.ext
        rw [coe_conjAut_apply]
        have hcomm := Subgroup.mem_centralizer_iff.mp hc x (by simp)
        rw [hcomm]; group
    have hXF : X.subgroupOf K ≤ FixedCommutingProduct.fixedSubgroup (conjAut K x hKx) := by
      rw [hfix]
      exact Subgroup.subgroupOf_mono K hXT.1
    have hXpc : IsPComponent 2
        ((X.subgroupOf K).subgroupOf (FixedCommutingProduct.fixedSubgroup (conjAut K x hKx))) := by
      rw [hfix]
      have hpcA : IsPComponent 2 (X.subgroupOf (K ⊓ centralizer ({x} : Set G))) :=
        (ComponentClassification.HarrisLit.isTwoComponentIn_iff hXT.1).1 hXT
      exact (ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
        (X := K) (Y := K ⊓ centralizer ({x} : Set G)) (L := X) inf_le_left 2
        Nat.prime_two).mpr hpcA
    have hX'FS : IsFStar ↥(X.subgroupOf K) :=
      (isFStar_congr (Subgroup.subgroupOfEquivOfLe hXK)).2 hX
    exact residual_or_kDatum_of_vertical (K := ↥K) (σ := conjAut K x hKx)
      (X := X.subgroupOf K) hI hL hKq hZ hcat hσ hXF hXpc hX'FS hK
  ·
    exact Or.inr (Or.inl
      (centralDatum_of_diagonal hL.coverDatum hKq hZ φ hker (hXφ ▸ hX) hK))

end CFSG.OddStandard.SmallF3.HypA2
