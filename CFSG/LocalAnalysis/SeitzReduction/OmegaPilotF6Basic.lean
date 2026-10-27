module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerOTwo

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)

@[expose] def RefinedF6 {C : Type*} [Group C] (Qz Mz J : Subgroup C) (D : Type*) [Group D] :
    Prop :=
  ∀ ι : Mz ≃* Mz,
    Nat.card (Qz ⊓ centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map Mz.subtype :
        Subgroup C) : Set C) : Subgroup C) =
      Nat.card (Qz ⊓ centralizer (J : Set C) : Subgroup C) →
    Nonempty (perfectCore (centralizer ((((J.subgroupOf Mz).map ι.toMonoidHom).map
      Mz.subtype : Subgroup C) : Set C)) ≃* D)

theorem rootPairElt_ne_one {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    rootPairElt hQ h₁₂ h₁₃ h₂₃ ≠ 1 := by
  intro h1
  rw [rootPairElt, ← map_one (projHom Q)] at h1
  have h := congrArg (fun g : orthDerived Q => (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) P₁.f)
    (projHom_injective (exists_map_ne_zero_of_hypPair P₁) h1)
  simp only [Subgroup.coe_one, LinearEquiv.coe_one, id] at h
  rw [eichler_apply P₁.Q_e h₁₂.ee, P₁.polar_fe, h₁₂.fe, P₂.Q_e] at h
  simp only [one_smul, mul_one, add_zero, zero_smul, sub_zero, add_eq_left] at h
  exact P₂.e_ne_zero h

variable (K : Type) [Field K] {n : ℕ}

noncomputable abbrev plusRadical (i j : Fin n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  rootRadicalBar (coordinateQuadPlus n K) (isHypCoord_coordinateQuadPlus (K := K) i).hypPair
    (isHypCoord_coordinateQuadPlus (K := K) j).hypPair

noncomputable abbrev plusLevi (i j : Fin n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  rootLeviBar (coordinateQuadPlus n K) (isHypCoord_coordinateQuadPlus (K := K) i).hypPair
    (isHypCoord_coordinateQuadPlus (K := K) j).hypPair

variable {K} [Finite K] [CharP K 2]

theorem plusRootElt_decomp (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    plusRootElt K (by omega) hij hik hjk ∈ pairPerp k ∧
      IsLongRoot _ (plusRootElt K (by omega) hij hik hjk) ∧
      perfectCore (centralizer ({plusRootElt K (by omega) hij hik hjk} :
        Set (matrixProjectiveDerived (coordinateQuadPlus n K)))) =
        plusRadical K i j ⊔ plusLevi K i j ∧
      IsPGroup 2 (plusRadical K i j) ∧
      plusLevi K i j ≤ normalizer (plusRadical K i j :
        Set (matrixProjectiveDerived (coordinateQuadPlus n K))) ∧
      Disjoint (plusRadical K i j) (plusLevi K i j) ∧
      (∀ N : Subgroup (plusLevi K i j), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      pairTorus k ≤ plusLevi K i j := by
  have hQ := (regular_coordinateQuadPlus n K (by omega)).1
  have hi := isHypCoord_coordinateQuadPlus (K := K) i
  have hj := isHypCoord_coordinateQuadPlus (K := K) j
  have hk := isHypCoord_coordinateQuadPlus (K := K) k
  have h₁₂ := hi.orth hj (pairDisjoint_plus hij)
  have h₁₃ := hi.orth hk (pairDisjoint_plus hik)
  have h₂₃ := hj.orth hk (pairDisjoint_plus hjk)
  refine ⟨?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃, ?_, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot hn hij N hN h2, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
  · rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt hn hq hij hik hjk)]
    exact centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inr rfl)⟩

end CFSG.SeitzReduction.OmegaPilot
