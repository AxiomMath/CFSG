module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRoot

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)

section Bar

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def rootRadicalBar (Q : QuadraticForm K (Fin d → K))
    (P₁ P₂ : HypPair Q) : Subgroup (matrixProjectiveDerived Q) :=
  ((rootRadical Q P₁ P₂).subgroupOf (orthDerived Q)).map (projHom Q)

@[expose] noncomputable def rootLeviBar (Q : QuadraticForm K (Fin d → K)) (P₁ P₂ : HypPair Q) :
    Subgroup (matrixProjectiveDerived Q) :=
  ((rootLevi Q P₁ P₂).subgroupOf (orthDerived Q)).map (projHom Q)

theorem isPGroup_rootRadicalBar [CharP K 2] (P₁ P₂ : HypPair Q) :
    IsPGroup 2 (rootRadicalBar Q P₁ P₂) :=
  ((isPGroup_rootRadical (P₁ := P₁) (P₂ := P₂)).comap_subtype).map _

theorem rootLeviBar_le_normalizer {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) :
    rootLeviBar Q P₁ P₂ ≤ normalizer (rootRadicalBar Q P₁ P₂ : Set (matrixProjectiveDerived Q)) := by
  have key : ∀ y ∈ rootLeviBar Q P₁ P₂, ∀ x ∈ rootRadicalBar Q P₁ P₂,
      y * x * y⁻¹ ∈ rootRadicalBar Q P₁ P₂ := by
    rintro _ ⟨Y, hY, rfl⟩ _ ⟨X, hX, rfl⟩
    refine ⟨Y * X * Y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hY' : (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi Q P₁ P₂ := mem_subgroupOf.mp hY
    have hX' : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootRadical Q P₁ P₂ := mem_subgroupOf.mp hX
    exact mem_subgroupOf.mpr
      (conj_mem_rootRadical h₁₂ hY'.1.1 (mem_centralizer_singleton_iff.mp hY'.1.2) hX')
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key y hy x hx, fun hx => ?_⟩
  have h := key y⁻¹ (inv_mem hy) _ hx
  rwa [inv_inv, show y⁻¹ * (y * x * y⁻¹) * y = x by group] at h

theorem disjoint_rootRadicalBar_rootLeviBar [CharP K 2] {P₁ P₂ : HypPair Q}
    (h₁₂ : P₁.Orth P₂) : Disjoint (rootRadicalBar Q P₁ P₂) (rootLeviBar Q P₁ P₂) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨X, hX, rfl⟩ ⟨Y, hY, hYX⟩
  have hXY : Y = X := projHom_injective (exists_map_ne_zero_of_hypPair P₁) hYX
  subst hXY
  have h1 : (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootRadical Q P₁ P₂ ⊓ rootLevi Q P₁ P₂ :=
    ⟨mem_subgroupOf.mp hX, mem_subgroupOf.mp hY⟩
  rw [rootRadical_inf_rootLevi h₁₂, mem_bot] at h1
  rw [show Y = 1 from Subtype.ext h1, map_one]

theorem centralizer_rootPairElt [Finite K] [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    centralizer {rootPairElt hQ h₁₂ h₁₃ h₂₃} = rootRadicalBar Q P₁ P₂ ⊔ rootLeviBar Q P₁ P₂ := by
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  have hQ' := exists_map_ne_zero_of_hypPair P₁
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  have hEΩ := eichler_mem_orthDerived hQ hT
  apply le_antisymm
  · intro x hx
    obtain ⟨X, rfl⟩ := projHom_surjective Q x
    have hc := mem_centralizer_singleton_iff.mp hx
    rw [rootPairElt, ← map_mul, ← map_mul] at hc
    have hc' := congrArg Subtype.val (projHom_injective hQ' hc)
    simp only [Subgroup.coe_mul] at hc'
    have hmem := mem_sup_of_commute h₁₂ (orthDerived Q) hΩO hEΩ X.2 hc'
    have hmem' : X ∈ ((rootRadical Q P₁ P₂ ⊓ orthDerived Q) ⊔
        (rootLevi Q P₁ P₂ ⊓ orthDerived Q)).subgroupOf (orthDerived Q) := mem_subgroupOf.mpr hmem
    rw [subgroupOf_sup inf_le_right inf_le_right, inf_subgroupOf_right, inf_subgroupOf_right]
      at hmem'
    rw [rootRadicalBar, rootLeviBar, ← Subgroup.map_sup]
    exact mem_map_of_mem _ hmem'
  · refine sup_le ?_ ?_
    · rintro _ ⟨Y, hY, rfl⟩
      have h := mem_centralizer_singleton_iff.mp (rootRadical_le_centralizer (mem_subgroupOf.mp hY))
      rw [mem_centralizer_singleton_iff, rootPairElt, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h
    · rintro _ ⟨Y, hY, rfl⟩
      have h := mem_centralizer_singleton_iff.mp (rootLevi_le_centralizer (mem_subgroupOf.mp hY))
      rw [mem_centralizer_singleton_iff, rootPairElt, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h

theorem pairTorusOf_le_rootLeviBar [Finite K] [CharP K 2] {P₁ P₂ : HypPair Q} {a b : Fin d}
    (h : IsHypCoord Q a b) (he₁ : P₁.e a = 0 ∧ P₁.e b = 0) (hf₁ : P₁.f a = 0 ∧ P₁.f b = 0)
    (he₂ : P₂.e a = 0 ∧ P₂.e b = 0) (hf₂ : P₂.f a = 0 ∧ P₂.f b = 0) :
    pairTorusOf Q a b ≤ rootLeviBar Q P₁ P₂ := by
  rintro _ ⟨T, hT, rfl⟩
  refine ⟨T, mem_subgroupOf.mpr ?_, rfl⟩
  obtain ⟨c, hc⟩ := mem_subgroupOf.mp hT
  rw [← hc]
  exact mem_rootLevi_of_fix (h.torusLin_mem_orthogonalGroup c)
    (torusLin_eq_self_of he₁.1 he₁.2 c) (torusLin_eq_self_of hf₁.1 hf₁.2 c)
    (torusLin_eq_self_of he₂.1 he₂.2 c) (torusLin_eq_self_of hf₂.1 hf₂.2 c)

theorem rootPairElt_mem_pairPerpOf [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {a b : Fin d}
    (h : IsHypCoord Q a b) (he₁ : P₁.e a = 0 ∧ P₁.e b = 0) (he₂ : P₂.e a = 0 ∧ P₂.e b = 0) :
    rootPairElt hQ h₁₂ h₁₃ h₂₃ ∈ pairPerpOf Q a b :=
  ⟨_, mem_subgroupOf.mpr ⟨eichler_apply_of_polar_eq_zero (by rw [h.polar_left]; exact he₁.2)
      (by rw [h.polar_left]; exact he₂.2),
    eichler_apply_of_polar_eq_zero (by rw [h.polar_right]; exact he₁.1)
      (by rw [h.polar_right]; exact he₂.1)⟩, rfl⟩

end Bar

section Coordinates

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem single_plus_apply_eq_zero {i k : Fin n} (hik : i ≠ k) (s t : Fin n ⊕ Fin n)
    (hs : s = .inl i ∨ s = .inr i) (ht : t = .inl k ∨ t = .inr k) :
    (Pi.single (plusIndexEquiv n s) (1 : K) : Fin (2 * n) → K) (plusIndexEquiv n t) = 0 := by
  refine Pi.single_eq_of_ne (fun h => ?_) _
  have h' := (plusIndexEquiv n).injective h
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all

theorem centralizer_longRoot_decomp_core (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ (z : matrixProjectiveDerived (coordinateQuadPlus n K))
      (Qz Mz : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))),
      z ∈ pairPerp k ∧ IsLongRoot _ z ∧ centralizer {z} = Qz ⊔ Mz ∧ IsPGroup 2 Qz ∧
        Mz ≤ normalizer (Qz : Set (matrixProjectiveDerived (coordinateQuadPlus n K))) ∧
        Disjoint Qz Mz ∧ pairTorus k ≤ Mz := by
  have hQ := (regular_coordinateQuadPlus n K hn).1
  have hi := isHypCoord_coordinateQuadPlus (K := K) i
  have hj := isHypCoord_coordinateQuadPlus (K := K) j
  have hk := isHypCoord_coordinateQuadPlus (K := K) k
  have h₁₂ := hi.orth hj (pairDisjoint_plus hij)
  have h₁₃ := hi.orth hk (pairDisjoint_plus hik)
  have h₂₃ := hj.orth hk (pairDisjoint_plus hjk)
  have hz := isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, rootRadicalBar _ hi.hypPair hj.hypPair,
    rootLeviBar _ hi.hypPair hj.hypPair, ?_, hz, centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃,
    isPGroup_rootRadicalBar _ _, rootLeviBar_le_normalizer h₁₂,
    disjoint_rootRadicalBar_rootLeviBar h₁₂, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inr rfl)⟩

end Coordinates

end CFSG.SeitzReduction.OmegaPilot
