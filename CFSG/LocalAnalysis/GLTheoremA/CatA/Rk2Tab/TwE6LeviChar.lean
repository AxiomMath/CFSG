module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.LieType.Chevalley.ParabolicGradedDet
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Chevalley.GraphFixedParabolicRootFactors
public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.LieType.Chevalley.E6EvenRootTorus
public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenLevi
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem orbitUnion_twE6MaxA2A1 :
    TwistTag.E6.orbitUnion twE6MaxA2A1 = {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} := by
  ext i
  rw [TwistTag.mem_orbitUnion, Set.mem_setOf_eq]
  simp only [twE6MaxA2A1, Set.mem_ofPred_eq, TwistTag.mem_orbit_iff]
  revert i
  decide

theorem orbitUnion_twE6MaxA1A2 :
    TwistTag.E6.orbitUnion twE6MaxA1A2 =
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} := by
  ext i
  rw [TwistTag.mem_orbitUnion, Set.mem_setOf_eq]
  simp only [twE6MaxA1A2, Set.mem_ofPred_eq, TwistTag.mem_orbit_iff]
  revert i
  decide

theorem orbitUnion_twE6MaxD4 :
    TwistTag.E6.orbitUnion twE6MaxD4 =
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} := by
  ext i
  rw [TwistTag.mem_orbitUnion, Set.mem_setOf_eq]
  simp only [twE6MaxD4, Set.mem_ofPred_eq, TwistTag.mem_orbit_iff]
  revert i
  decide

private theorem parabolicDegree_setOf_val_ne {τ : Tag} {k : ℕ} (hk : k < τ.rank)
    (v : Fin τ.rank → ℤ) :
    parabolicDegree τ {i : Fin τ.rank | i.val ≠ k} v = v ⟨k, hk⟩ := by
  classical
  rw [parabolicDegree, Finset.sum_eq_single (⟨k, hk⟩ : Fin τ.rank)]
  · rw [if_neg]
    intro hmem
    exact hmem (by simp)
  · intro b _ hb
    rw [if_pos]
    exact fun h' => hb (Fin.ext h')
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem parabolicDegree_setOf_val_ne_pair {τ : Tag} {k l : ℕ} (hk : k < τ.rank)
    (hl : l < τ.rank) (hkl : k ≠ l) (v : Fin τ.rank → ℤ) :
    parabolicDegree τ {i : Fin τ.rank | i.val ≠ k ∧ i.val ≠ l} v =
      v ⟨k, hk⟩ + v ⟨l, hl⟩ := by
  classical
  rw [parabolicDegree]
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ (⟨k, hk⟩ : Fin τ.rank))]
  rw [Finset.sum_eq_single (⟨l, hl⟩ : Fin τ.rank)]
  · simp
    ring
  · intro b hb hbne
    rw [if_pos]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
    exact ⟨fun h => hb (Fin.ext h), fun h => hbne (Fin.ext h)⟩
  · intro h
    exact absurd (Finset.mem_erase.mpr ⟨fun h' => hkl (congrArg Fin.val h').symm,
      Finset.mem_univ _⟩) h

private theorem gradedRoots_eq_filter {τ : Tag} {J : Set (Fin τ.rank)} {d : ℤ}
    {g : (Fin τ.rank → ℤ) → ℤ} (hpd : ∀ α, parabolicDegree τ J α = g α) :
    gradedRoots τ J d = (rootFinset τ).filter (fun α => g α = d) := by
  classical
  ext α
  rw [gradedRoots, Finset.mem_filter, Finset.mem_filter, mem_rootFinset, hpd α]

theorem gradedWeight_twE6MaxA2A1 :
    gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3 =
      fun i => if i = (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) then 1 else 0 := by
  funext i
  rw [gradedWeight, gradedRoots_eq_filter (τ := TwistTag.E6.tag)
    (J := {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3}) (d := 3)
    (g := fun α => α (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank))
    (fun α => parabolicDegree_setOf_val_ne (by decide) α)]
  fin_cases i <;> decide +kernel

theorem gradedWeight_twE6MaxA1A2 :
    gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4 =
      fun i => (if i = (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) then 1 else 0) +
        (if i = (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) then 1 else 0) := by
  funext i
  rw [gradedWeight, gradedRoots_eq_filter (τ := TwistTag.E6.tag)
    (J := {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4}) (d := 4)
    (g := fun α => α (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) +
      α (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank))
    (fun α => parabolicDegree_setOf_val_ne_pair (by decide) (by decide) (by decide) α)]
  fin_cases i <;> decide +kernel

theorem gradedWeight_twE6MaxD4 :
    gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2 =
      fun i => 4 * (if i = (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) then 1 else 0) +
        4 * (if i = (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) then 1 else 0) := by
  funext i
  rw [gradedWeight, gradedRoots_eq_filter (τ := TwistTag.E6.tag)
    (J := {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5}) (d := 2)
    (g := fun α => α (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) +
      α (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank))
    (fun α => parabolicDegree_setOf_val_ne_pair (by decide) (by decide) (by decide) α)]
  fin_cases i <;> decide +kernel

private theorem perm_mem_setA2A1 {i : Fin TwistTag.E6.tag.rank} (hi : i.val ≠ 3) :
    (TwistTag.E6.perm i).val ≠ 3 := by
  revert i
  decide

private theorem perm_mem_setA1A2 {i : Fin TwistTag.E6.tag.rank} (hi : i.val ≠ 2 ∧ i.val ≠ 4) :
    (TwistTag.E6.perm i).val ≠ 2 ∧ (TwistTag.E6.perm i).val ≠ 4 := by
  revert i
  decide

private theorem perm_mem_setD4 {i : Fin TwistTag.E6.tag.rank} (hi : i.val ≠ 0 ∧ i.val ≠ 5) :
    (TwistTag.E6.perm i).val ≠ 0 ∧ (TwistTag.E6.perm i).val ≠ 5 := by
  revert i
  decide

private theorem gradedWeight_twE6MaxA2A1_perm (i : Fin TwistTag.E6.tag.rank) :
    gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3
        (TwistTag.E6.perm i) =
      gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3 i := by
  rw [gradedWeight_twE6MaxA2A1]
  simp only
  revert i
  decide

private theorem gradedWeight_twE6MaxA1A2_perm (i : Fin TwistTag.E6.tag.rank) :
    gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4
        (TwistTag.E6.perm i) =
      gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4 i := by
  rw [gradedWeight_twE6MaxA1A2]
  simp only
  revert i
  decide

private theorem gradedWeight_twE6MaxD4_perm (i : Fin TwistTag.E6.tag.rank) :
    gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2
        (TwistTag.E6.perm i) =
      gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2 i := by
  rw [gradedWeight_twE6MaxD4]
  simp only
  revert i
  decide

section TwistEquivariance

variable {K : Type} [Field K] (σ : K →+* K)

theorem twistHom_mem_parabolicLevi {t : TwistTag} {A : Set (Fin t.tag.rank)}
    (hA : ∀ i ∈ A, t.perm i ∈ A) {g : ModGL t.tag K}
    (hg : g ∈ parabolicLevi t.tag K A) :
    twistHom t K σ g ∈ parabolicLevi t.tag K A := by
  have hM : parabolicLevi t.tag K A = Subgroup.closure
      (Set.range (fun p : Fin t.tag.rank × Kˣ => torusElt t.tag K p.1 p.2) ∪
        {g | ∃ j ∈ A, ∃ c : K, g = xUnit t.tag K j c ∨ g = yUnit t.tag K j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hM] at hg ⊢
  induction hg using Subgroup.closure_induction'' with
  | mem g hgs =>
    rcases hgs with ⟨⟨i, u⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · rw [twistHom_torusElt]
      exact Subgroup.subset_closure (Or.inl ⟨(t.perm i, Units.map σ.toMonoidHom u), rfl⟩)
    · rw [twistHom_xUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inl rfl⟩)
    · rw [twistHom_yUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inr rfl⟩)
  | inv_mem g hgs =>
    rw [map_inv]
    refine Subgroup.inv_mem _ ?_
    rcases hgs with ⟨⟨i, u⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · rw [twistHom_torusElt]
      exact Subgroup.subset_closure (Or.inl ⟨(t.perm i, Units.map σ.toMonoidHom u), rfl⟩)
    · rw [twistHom_xUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inl rfl⟩)
    · rw [twistHom_yUnit]
      exact Subgroup.subset_closure (Or.inr ⟨t.perm j, hA j hj, σ c, Or.inr rfl⟩)
  | one => simp
  | mul g h hg hh ihg ihh =>
    rw [map_mul]
    exact Subgroup.mul_mem _ ihg ihh

private theorem gradedDet_twistHom_generator {t : TwistTag} {A : Set (Fin t.tag.rank)} {d : ℤ}
    (hd : d ≠ 0) (hA : ∀ i ∈ A, t.perm i ∈ A)
    (hw : ∀ i, gradedWeight t.tag A d (t.perm i) = gradedWeight t.tag A d i)
    (u₀ : Kˣ) (hu₀ : ((u₀ : K)) ^ 2 ≠ 1) {y : ModGL t.tag K}
    (hy : y ∈ Set.range (fun p : Fin t.tag.rank × Kˣ => torusElt t.tag K p.1 p.2) ∪
      {g | ∃ j ∈ A, ∃ c : K, g = xUnit t.tag K j c ∨ g = yUnit t.tag K j c}) :
    ∀ (h : y ∈ parabolicLevi t.tag K A),
      parabolicGradedDet (τ := t.tag) (K := K) A d ⟨twistHom t K σ y,
          twistHom_mem_parabolicLevi σ hA h⟩ =
        Units.map σ.toMonoidHom (parabolicGradedDet (τ := t.tag) (K := K) A d ⟨y, h⟩) := by
  rcases hy with ⟨⟨i, u⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
  · intro h
    have e1 : (⟨twistHom t K σ ((fun p : Fin t.tag.rank × Kˣ => torusElt t.tag K p.1 p.2) (i, u)),
        twistHom_mem_parabolicLevi σ hA h⟩ : ↥(parabolicLevi t.tag K A)) =
        ⟨torusElt t.tag K (t.perm i) (Units.map σ.toMonoidHom u),
          torusGroup_le_parabolicLevi _ (torusElt_mem_torusGroup _ _)⟩ :=
      Subtype.ext (twistHom_torusElt t K σ i u)
    have e2 : (⟨(fun p : Fin t.tag.rank × Kˣ => torusElt t.tag K p.1 p.2) (i, u), h⟩ :
        ↥(parabolicLevi t.tag K A)) =
        ⟨torusElt t.tag K i u, torusGroup_le_parabolicLevi _ (torusElt_mem_torusGroup _ _)⟩ := Subtype.ext rfl
    rw [e1, e2, parabolicGradedDet_torusElt hd (t.perm i) (Units.map σ.toMonoidHom u),
      parabolicGradedDet_torusElt hd i u, hw i, map_zpow]
  · intro h
    have e1 : (⟨twistHom t K σ (xUnit t.tag K j c),
        twistHom_mem_parabolicLevi σ hA h⟩ : ↥(parabolicLevi t.tag K A)) =
        ⟨xUnit t.tag K (t.perm j) (σ c),
          xUnit_mem_parabolicLevi (hA j hj) (σ c)⟩ :=
      Subtype.ext (twistHom_xUnit t K σ j c)
    have h1 : parabolicGradedDet (τ := t.tag) (K := K) A d
        (⟨twistHom t K σ (xUnit t.tag K j c),
          twistHom_mem_parabolicLevi σ hA h⟩ : ↥(parabolicLevi t.tag K A)) = 1 := by
      rw [e1]
      exact parabolicGradedDet_xUnit_eq_one d (hA j hj) u₀ hu₀ (σ c)
    have h2 : parabolicGradedDet (τ := t.tag) (K := K) A d
        (⟨xUnit t.tag K j c, h⟩ : ↥(parabolicLevi t.tag K A)) = 1 :=
      parabolicGradedDet_xUnit_eq_one d hj u₀ hu₀ c
    rw [h1, h2, map_one]
  · intro h
    have e1 : (⟨twistHom t K σ (yUnit t.tag K j c),
        twistHom_mem_parabolicLevi σ hA h⟩ : ↥(parabolicLevi t.tag K A)) =
        ⟨yUnit t.tag K (t.perm j) (σ c),
          yUnit_mem_parabolicLevi (hA j hj) (σ c)⟩ :=
      Subtype.ext (twistHom_yUnit t K σ j c)
    have h1 : parabolicGradedDet (τ := t.tag) (K := K) A d
        (⟨twistHom t K σ (yUnit t.tag K j c),
          twistHom_mem_parabolicLevi σ hA h⟩ : ↥(parabolicLevi t.tag K A)) = 1 := by
      rw [e1]
      exact parabolicGradedDet_yUnit_eq_one d (hA j hj) u₀ hu₀ (σ c)
    have h2 : parabolicGradedDet (τ := t.tag) (K := K) A d
        (⟨yUnit t.tag K j c, h⟩ : ↥(parabolicLevi t.tag K A)) = 1 :=
      parabolicGradedDet_yUnit_eq_one d hj u₀ hu₀ c
    rw [h1, h2, map_one]

theorem gradedDet_twistHom {t : TwistTag} {A : Set (Fin t.tag.rank)} {d : ℤ}
    (hd : d ≠ 0) (hA : ∀ i ∈ A, t.perm i ∈ A)
    (hw : ∀ i, gradedWeight t.tag A d (t.perm i) = gradedWeight t.tag A d i)
    (hK : ∃ u : Kˣ, ((u : K)) ^ 2 ≠ 1) {g : ModGL t.tag K}
    (hg : g ∈ parabolicLevi t.tag K A) :
    parabolicGradedDet (τ := t.tag) (K := K) A d
        ⟨twistHom t K σ g, twistHom_mem_parabolicLevi σ hA hg⟩ =
      Units.map σ.toMonoidHom (parabolicGradedDet (τ := t.tag) (K := K) A d ⟨g, hg⟩) := by
  obtain ⟨u₀, hu₀⟩ := hK
  have hS : parabolicLevi t.tag K A = Subgroup.closure
      (Set.range (fun p : Fin t.tag.rank × Kˣ => torusElt t.tag K p.1 p.2) ∪
        {g | ∃ j ∈ A, ∃ c : K, g = xUnit t.tag K j c ∨ g = yUnit t.tag K j c}) := by
    rw [Subgroup.closure_union]
    rfl
  have key : ∀ (x : ModGL t.tag K), x ∈ Subgroup.closure
      (Set.range (fun p : Fin t.tag.rank × Kˣ => torusElt t.tag K p.1 p.2) ∪
        {g | ∃ j ∈ A, ∃ c : K, g = xUnit t.tag K j c ∨ g = yUnit t.tag K j c}) →
      ∀ (h : x ∈ parabolicLevi t.tag K A),
        parabolicGradedDet (τ := t.tag) (K := K) A d ⟨twistHom t K σ x,
            twistHom_mem_parabolicLevi σ hA h⟩ =
          Units.map σ.toMonoidHom (parabolicGradedDet (τ := t.tag) (K := K) A d ⟨x, h⟩) := by
    intro x hx
    induction hx using Subgroup.closure_induction'' with
    | mem y hys => exact gradedDet_twistHom_generator σ hd hA hw u₀ hu₀ hys
    | inv_mem y hys =>
      intro h
      have hyM : y ∈ parabolicLevi t.tag K A :=
        hS.symm ▸ Subgroup.subset_closure hys
      have hgen := gradedDet_twistHom_generator σ hd hA hw u₀ hu₀ hys hyM
      have e1 : (⟨y⁻¹, h⟩ : ↥(parabolicLevi t.tag K A)) = (⟨y, hyM⟩ : ↥(parabolicLevi t.tag K A))⁻¹ :=
        Subtype.ext rfl
      have e2 : (⟨twistHom t K σ y⁻¹, twistHom_mem_parabolicLevi σ hA h⟩ :
          ↥(parabolicLevi t.tag K A)) =
          (⟨twistHom t K σ y, twistHom_mem_parabolicLevi σ hA hyM⟩ :
            ↥(parabolicLevi t.tag K A))⁻¹ := by
        refine Subtype.ext ?_
        exact map_inv (twistHom t K σ) y
      rw [e1, e2, map_inv, hgen]
      simp only [map_inv]
    | one =>
      intro h
      have e1 : (⟨twistHom t K σ 1, twistHom_mem_parabolicLevi σ hA h⟩ :
          ↥(parabolicLevi t.tag K A)) = 1 :=
        Subtype.ext (map_one (twistHom t K σ))
      have e2 : (⟨(1 : ModGL t.tag K), h⟩ : ↥(parabolicLevi t.tag K A)) = 1 :=
        Subtype.ext rfl
      rw [e1, e2, map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro h
      have hyM : y ∈ parabolicLevi t.tag K A := hS.symm ▸ hy
      have hzM : z ∈ parabolicLevi t.tag K A := hS.symm ▸ hz
      have e1 : (⟨y * z, h⟩ : ↥(parabolicLevi t.tag K A)) =
          (⟨y, hyM⟩ : ↥(parabolicLevi t.tag K A)) * ⟨z, hzM⟩ := Subtype.ext rfl
      have e2 : (⟨twistHom t K σ (y * z), twistHom_mem_parabolicLevi σ hA h⟩ :
          ↥(parabolicLevi t.tag K A)) =
          (⟨twistHom t K σ y, twistHom_mem_parabolicLevi σ hA hyM⟩ :
            ↥(parabolicLevi t.tag K A)) *
            ⟨twistHom t K σ z, twistHom_mem_parabolicLevi σ hA hzM⟩ :=
        Subtype.ext (map_mul (twistHom t K σ) y z)
      rw [e1, e2, map_mul, map_mul, ihy hyM, ihz hzM, map_mul]
  exact key g (hS ▸ hg) hg

end TwistEquivariance

section TorusCoord

variable (τ : Tag) (K : Type) [Field K]

private theorem gradedRestrictHom_torusCoordHom {A : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0)
    (u : Fin τ.rank → Kˣ) (α : {α // α ∈ gradedRoots τ A d}) :
    gradedRestrictHom (K := K) A d
        (Subgroup.inclusion (le_sup_left : torusGroup τ K ≤ parabolicLevi τ K A)
          (torusCoordHom τ K u))
        (gradedBasis (K := K) hd α) =
      ((∏ i, (u i) ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K) •
        gradedBasis (K := K) hd α := by
  refine Subtype.ext ?_
  rw [Submodule.coe_smul]
  change (((torusCoordHom τ K u : ↥(torusGroup τ K)) : ModGL τ K) :
      Module.End K (RootModule τ K)) (((gradedBasis (K := K) hd α : parabolicGraded τ K A d)) :
        RootModule τ K) =
    ((∏ i, (u i) ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K) •
      (((gradedBasis (K := K) hd α : parabolicGraded τ K A d)) : RootModule τ K)
  rw [gradedBasis_apply]
  have h := list_prod_torusElt_rootVec (R := K) (τ := τ) (α := α.1)
    (mem_gradedRoots.1 α.2).1 (List.ofFn fun i : Fin τ.rank => (i, u i))
  have e1 : ((List.ofFn fun i : Fin τ.rank => (i, u i)).map
      fun p => torusElt τ K p.1 p.2) = List.ofFn fun i => torusElt τ K i (u i) := by
    rw [List.map_ofFn]
    rfl
  have e2 : ((List.ofFn fun i : Fin τ.rank => (i, u i)).map
      fun p => p.2 ^ (∑ k, τ.cartan p.1 k * α.1 k)) =
      List.ofFn fun i => (u i) ^ (∑ k, τ.cartan i k * α.1 k) := by
    rw [List.map_ofFn]
    rfl
  rw [e1, e2, List.prod_ofFn] at h
  rw [coe_torusCoordHom]
  exact h

theorem parabolicGradedDet_torusCoordHom {A : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0)
    (u : Fin τ.rank → Kˣ) :
    parabolicGradedDet (τ := τ) (K := K) A d
        (Subgroup.inclusion (le_sup_left : torusGroup τ K ≤ parabolicLevi τ K A)
          (torusCoordHom τ K u)) =
      ∏ i, (u i) ^ gradedWeight τ A d i := by
  refine Units.ext ?_
  change LinearMap.det (M := parabolicGraded τ K A d) (gradedRestrictHom (K := K) A d
      (Subgroup.inclusion (le_sup_left : torusGroup τ K ≤ parabolicLevi τ K A)
        (torusCoordHom τ K u))) = ↑(∏ i, (u i) ^ gradedWeight τ A d i)
  rw [← LinearMap.det_toMatrix (gradedBasis (K := K) hd)]
  have hdiag : LinearMap.toMatrix (gradedBasis (K := K) hd) (gradedBasis (K := K) hd)
      (gradedRestrictHom (K := K) A d
        (Subgroup.inclusion (le_sup_left : torusGroup τ K ≤ parabolicLevi τ K A)
          (torusCoordHom τ K u))) =
      Matrix.diagonal
        (fun α : {α // α ∈ gradedRoots τ A d} =>
          ((∏ i, (u i) ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K)) := by
    ext α β
    rw [LinearMap.toMatrix_apply, gradedRestrictHom_torusCoordHom (τ := τ) (K := K) hd, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, Matrix.diagonal_apply]
    by_cases h : α = β
    · subst h; simp
    · simp [h]
  rw [hdiag, Matrix.det_diagonal, ← Units.coe_prod]
  have hprod : (∏ α : {α // α ∈ gradedRoots τ A d},
      ∏ i, (u i) ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) =
      ∏ i, (u i) ^ gradedWeight τ A d i := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_zpow_eq_zpow_sum]
    congr 1
    simpa [gradedWeight] using
      (Finset.sum_coe_sort (gradedRoots τ A d)
        (fun α => ∑ j, τ.cartan i j * α j))
  rw [hprod]

theorem exists_eq_torusCoordHom_of_mem_torusGroup {t : ModGL τ K}
    (ht : t ∈ torusGroup τ K) :
    ∃ u : Fin τ.rank → Kˣ, t = ((torusCoordHom τ K u : ↥(torusGroup τ K)) : ModGL τ K) := by
  obtain ⟨u, hu⟩ := torusCoordHom_surjective (R := K) ⟨t, ht⟩
  exact ⟨u, (congrArg Subtype.val hu).symm⟩

end TorusCoord

section Arithmetic

variable {F : Type} [Field F] [Finite F] {n : ℕ}

private theorem two_le_two_pow_of_card (hF : Nat.card F = (2 ^ n) ^ 2) : 2 ≤ 2 ^ n := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : 2 ≤ Nat.card F := by
    have h := Fintype.one_lt_card (α := F)
    rwa [Nat.card_eq_fintype_card]
  have hn : n ≠ 0 := by
    intro hn
    rw [hn] at hF
    have h1 : Nat.card F = 1 := by simpa using hF
    omega
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem card_eq_two_pow_of_card (hF : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card F = 2 ^ (2 * n) := by
  calc Nat.card F = (2 ^ n) ^ 2 := hF
    _ = 2 ^ (n * 2) := by rw [pow_mul]
    _ = 2 ^ (2 * n) := by rw [Nat.mul_comm n 2]

private theorem one_le_two_pow_of_card (hF : Nat.card F = (2 ^ n) ^ 2) : 1 ≤ 2 ^ n :=
  le_trans (by norm_num) (two_le_two_pow_of_card hF)

private theorem exists_unit_sq_ne_one_of_card (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∃ u : Fˣ, ((u : F)) ^ 2 ≠ 1 := by
  by_contra h
  simp only [not_exists, not_not] at h
  haveI : Fintype F := Fintype.ofFinite F
  have hdvd : Fintype.card F - 1 ∣ 2 := by
    rw [← FiniteField.forall_pow_eq_one_iff F 2]
    intro u
    exact Units.ext (by simpa using h u)
  have hcard : Fintype.card F = (2 ^ n) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have h2 := two_le_two_pow_of_card hF
  have hge : 3 ≤ Fintype.card F - 1 := by
    have h4 : 4 ≤ Fintype.card F := by nlinarith
    omega
  have hle : Fintype.card F - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem not_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) : ¬ p ∣ 2 ^ n - 1 := by
  intro h
  have h2 : p ∣ 2 := by
    have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpq h
    rwa [show (2 ^ n + 1) - (2 ^ n - 1) = 2 by
      have := Nat.one_le_two_pow (n := n); omega] at hsub
  rcases Nat.prime_two.eq_one_or_self_of_dvd p h2 with h1 | h1
  · exact hp.ne_one h1
  · exact hp2 h1

private theorem coprime_two_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) : Nat.Coprime (2 ^ n - 1) p := by
  have hnd := not_dvd_two_pow_sub_one hp hp2 hpq
  rcases hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right (2 ^ n - 1) p) with h | h
  · exact h
  · exact absurd (h ▸ Nat.gcd_dvd_left (2 ^ n - 1) p) hnd

private theorem coprime_four_card_sub_one (hF : Nat.card F = (2 ^ n) ^ 2) :
    Nat.Coprime 4 (Nat.card F - 1) := by
  have hq := card_eq_two_pow_of_card hF
  have h2 := two_le_two_pow_of_card hF
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at h2
      norm_num at h2
    · exact h
  have hodd : Odd (Nat.card F - 1) := by
    rw [hq]
    have h1 : 1 ≤ 2 * n := by omega
    refine ⟨2 ^ (2 * n - 1) - 1, ?_⟩
    have hpos : 1 ≤ 2 ^ (2 * n - 1) := Nat.one_le_two_pow
    have hsplit : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel h1]
      rw [pow_succ']
    omega
  have hcop2 : Nat.Coprime (Nat.card F - 1) 2 := hodd.coprime_two_right
  have hcop4 : Nat.Coprime (Nat.card F - 1) 4 := by
    have h := hcop2.pow_right 2
    simpa using h
  exact hcop4.symm

private theorem eq_one_of_pow_four_eq_one (hF : Nat.card F = (2 ^ n) ^ 2) {x : Fˣ} (hx : x ^ 4 = 1) :
    x = 1 := by
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcop := coprime_four_card_sub_one hF
  have h1 : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hx
  have h2 : orderOf x ∣ Nat.card Fˣ := by
    rw [Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  rw [Nat.card_units] at h2
  have h3 : orderOf x ∣ Nat.gcd 4 (Nat.card F - 1) := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 4 (Nat.card F - 1) = 1 from hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end Arithmetic

section Vanishing

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem gradedDet_eq_one_of_twist_fixed (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) {A : Set (Fin TwistTag.E6.tag.rank)} {d : ℤ} (hd : d ≠ 0)
    (hA : ∀ i ∈ A, TwistTag.E6.perm i ∈ A)
    (hw : ∀ i, gradedWeight TwistTag.E6.tag A d (TwistTag.E6.perm i) =
      gradedWeight TwistTag.E6.tag A d i)
    {g : ModGL TwistTag.E6.tag F} (hgM : g ∈ parabolicLevi TwistTag.E6.tag F A)
    (hgfix : twistHom TwistTag.E6 F σ.toRingHom g = g) (hgp : g ^ p = 1) :
    parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩ = 1 := by
  obtain ⟨u₀, hu₀⟩ := exists_unit_sq_ne_one_of_card hF
  have heq := gradedDet_twistHom (K := F) σ.toRingHom hd hA hw ⟨u₀, hu₀⟩ hgM
  have hfixe : (⟨twistHom TwistTag.E6 F σ.toRingHom g,
      twistHom_mem_parabolicLevi (K := F) σ.toRingHom hA hgM⟩ :
        ↥(parabolicLevi TwistTag.E6.tag F A)) = ⟨g, hgM⟩ := Subtype.ext hgfix
  rw [hfixe] at heq
  have hχ : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩ =
      Units.map σ.toRingHom.toMonoidHom
        (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) := by
    rw [← heq]
  have hpow : (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) ^ (2 ^ n) =
      parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩ := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    have h := congrArg Units.val hχ
    rw [Units.coe_map] at h
    change ((parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩ : Fˣ) : F) =
      σ ((parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩ : Fˣ) : F) at h
    rw [hσ] at h
    exact h.symm
  have h1 : (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) ^ (2 ^ n - 1) =
      1 := by
    have hn : 1 ≤ 2 ^ n := one_le_two_pow_of_card hF
    have h2 : (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) ^ (2 ^ n - 1) *
        (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) =
        1 * (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) := by
      rw [← pow_succ, Nat.sub_add_cancel hn, hpow, one_mul]
    exact mul_right_cancel h2
  have h2 : (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) ^ p = 1 := by
    have h : (⟨g, hgM⟩ : ↥(parabolicLevi TwistTag.E6.tag F A)) ^ p = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, hgp, Subgroup.coe_one]
    rw [← map_pow, h, map_one]
  have h3 : orderOf (parabolicGradedDet (τ := TwistTag.E6.tag) (K := F) A d ⟨g, hgM⟩) ∣
      Nat.gcd (2 ^ n - 1) p :=
    Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h1) (orderOf_dvd_iff_pow_eq_one.mpr h2)
  rw [show Nat.gcd (2 ^ n - 1) p = 1 from coprime_two_pow_sub_one hp hp2 hpq] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end Vanishing

section Contracts

variable {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
  (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
  {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
  {E : Subgroup (ModGL TwistTag.E6.tag F)}

include hF σ hσ hp hp2 hpq

theorem le_subsystemGroup_of_le_graphFixedParabolicLevi_A2A1
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    E ≤ subsystemGroup TwistTag.E6.tag F {i | i.val ≠ 3} := by
  intro g hgE
  have hEM := hE hgE
  have hgM0 : g ∈ parabolicLevi TwistTag.E6.tag F (TwistTag.E6.orbitUnion twE6MaxA2A1) := hEM.1
  have hgΓ : g ∈ graphFixedRootGroup TwistTag.E6 F σ.toRingHom := hEM.2
  rw [orbitUnion_twE6MaxA2A1] at hgM0
  have hgfix : twistHom TwistTag.E6 F σ.toRingHom g = g :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 F σ.toRingHom).1
      (graphFixedRootGroup_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom) hgΓ)).2
  have hgp : g ^ p = 1 := hEel.2 g hgE
  have hA2A1 : ∀ i ∈ {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3},
      TwistTag.E6.perm i ∈ {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} :=
    fun i hi => perm_mem_setA2A1 hi
  have hw2A1 : ∀ i, gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3
      (TwistTag.E6.perm i) =
      gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3 i :=
    fun i => gradedWeight_twE6MaxA2A1_perm i
  have hχg : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F)
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3 ⟨g, hgM0⟩ = 1 :=
    gradedDet_eq_one_of_twist_fixed hF σ hσ hp hp2 hpq (by norm_num) hA2A1 hw2A1 hgM0 hgfix hgp
  have hsup : g ∈ torusGroup TwistTag.E6.tag F ⊔ subsystemGroup TwistTag.E6.tag F
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} := hgM0
  have hmul : (↑(torusGroup TwistTag.E6.tag F ⊔ subsystemGroup TwistTag.E6.tag F
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3}) : Set (ModGL TwistTag.E6.tag F)) =
      (torusGroup TwistTag.E6.tag F : Set (ModGL TwistTag.E6.tag F)) *
        (subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} :
          Set (ModGL TwistTag.E6.tag F)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (RootTorus.torusGroup_le_normalizer_subsystemGroup _)
  have hsup' : g ∈ (↑(torusGroup TwistTag.E6.tag F ⊔ subsystemGroup TwistTag.E6.tag F
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3}) : Set (ModGL TwistTag.E6.tag F)) := hsup
  rw [hmul] at hsup'
  obtain ⟨t, htT, l, hlL, htl⟩ := hsup'
  have hχl : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F)
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3
      ⟨l, Subgroup.mem_sup_right hlL⟩ = 1 := by
    obtain ⟨u₀, hu₀⟩ := exists_unit_sq_ne_one_of_card hF
    exact parabolicGradedDet_eq_one_of_mem_leviGenerators 3 u₀ hu₀ l hlL
  have hχt : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F)
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3
      ⟨t, Subgroup.mem_sup_left htT⟩ = 1 := by
    have he : (⟨g, hgM0⟩ : ↥(parabolicLevi TwistTag.E6.tag F
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3})) =
        (⟨t, Subgroup.mem_sup_left htT⟩ : ↥(parabolicLevi TwistTag.E6.tag F
          {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3})) *
          ⟨l, Subgroup.mem_sup_right hlL⟩ := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul]
      exact htl.symm
    rw [he, map_mul, hχl, mul_one] at hχg
    exact hχg
  obtain ⟨u, hu⟩ := exists_eq_torusCoordHom_of_mem_torusGroup (τ := TwistTag.E6.tag) (K := F) htT
  have htcoe : (⟨t, Subgroup.mem_sup_left htT⟩ : ↥(parabolicLevi TwistTag.E6.tag F
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3})) =
      Subgroup.inclusion (le_sup_left : torusGroup TwistTag.E6.tag F ≤ parabolicLevi
        TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3}) (torusCoordHom TwistTag.E6.tag F u) :=
    Subtype.ext hu
  have hχtu : (∏ i, (u i) ^ gradedWeight TwistTag.E6.tag
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} 3 i) = 1 := by
    rw [← parabolicGradedDet_torusCoordHom (τ := TwistTag.E6.tag) (K := F) (A :=
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3}) (d := 3) (by norm_num)]
    rw [← htcoe]
    exact hχt
  have hprod3 : (∏ i, (u i) ^ (if i = (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ)
      else 0)) = u ⟨3, by decide⟩ := by
    rw [Finset.prod_eq_single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu3 : u ⟨3, by decide⟩ = 1 := by
    rw [gradedWeight_twE6MaxA2A1] at hχtu
    rw [← hprod3]
    exact hχtu
  have htA : t ∈ subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 3} := by
    rw [hu, coe_torusCoordHom]
    refine subsystemTorus_le_subsystemGroup (Subgroup.list_prod_mem _ fun x hx => ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    by_cases hi : i = (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank)
    · rw [hi, hu3, torusElt_one]
      exact Subgroup.one_mem _
    · refine Subgroup.subset_closure ⟨i, ?_, u i, rfl⟩
      have hne : i.val ≠ 3 := fun h3 => hi (Fin.ext h3)
      simpa using hne
  rw [← htl]
  exact Subgroup.mul_mem _ htA hlL

end Contracts

section GeneralGroupTheory

private theorem card_le_prime_of_cyclic_of_pow_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {p : ℕ} (hp : p.Prime) (h : ∀ x : A, x ^ p = 1) : Nat.card A ≤ p := by
  have hexp : Monoid.exponent A ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one h
  rw [IsCyclic.exponent_eq_card] at hexp
  rcases hp.eq_one_or_self_of_dvd (Nat.card A) hexp with h1 | h1
  · rw [h1]
    exact hp.one_lt.le
  · rw [h1]

private theorem card_subgroupOf_inf {G : Type*} [Group G] (E N : Subgroup G) :
    Nat.card ↥((E ⊓ N).subgroupOf E) = Nat.card ↥(E ⊓ N) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ N ≤ E)).toEquiv

theorem card_le_mul_card_inf_of_le_sup_cyclic {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {E C N : Subgroup G} (hC : IsCyclic ↥C)
    (hCN : C ≤ Subgroup.normalizer (N : Set G)) (hE : E ≤ C ⊔ N)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ N) := by
  classical
  set H : Subgroup G := C ⊔ N with hH
  have hCH : C ≤ H := hH ▸ le_sup_left
  have hNH : N ≤ H := hH ▸ le_sup_right
  have hEH : E ≤ H := hH ▸ hE
  have hNnorm : H ≤ Subgroup.normalizer (N : Set G) := by
    rw [hH]
    refine sup_le hCN ?_
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact N.mul_mem (N.mul_mem hn hg) (N.inv_mem hn)
    · intro hg
      have h' := N.mul_mem (N.mul_mem (N.inv_mem hn) hg) hn
      rwa [show n⁻¹ * (n * g * n⁻¹) * n = g from by group] at h'
  haveI hN' : (N.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNH]
    intro h k hh hk
    exact (Subgroup.le_normalizer_iff.mp hNnorm) k hk h hh
  let q : ↥H →* H ⧸ N.subgroupOf H := QuotientGroup.mk' _
  let f : ↥E →* H ⧸ N.subgroupOf H := q.comp (Subgroup.inclusion hEH)
  have hqker : ∀ y : ↥H, q y = 1 ↔ (y : G) ∈ N := by
    intro y
    rw [← MonoidHom.mem_ker, show q.ker = N.subgroupOf H from QuotientGroup.ker_mk' _]
    exact Subgroup.mem_subgroupOf
  have hker : f.ker = (E ⊓ N).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change q (Subgroup.inclusion hEH x) = 1 ↔ (x : G) ∈ E ∧ (x : G) ∈ N
    rw [hqker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcard : Nat.card ↥E = Nat.card ↥f.range * Nat.card ↥(E ⊓ N) := by
    have h1 : Nat.card ↥E = Nat.card (↥E ⧸ f.ker) * Nat.card ↥f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥E ⧸ f.ker) = Nat.card ↥f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h1, h2, hker, card_subgroupOf_inf]
  let ψ : ↥C →* H ⧸ N.subgroupOf H := q.comp (Subgroup.inclusion hCH)
  have hψcyc : IsCyclic ↥ψ.range := by
    haveI : IsCyclic ↥C := hC
    exact isCyclic_of_surjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
  have hle_range : f.range ≤ ψ.range := by
    rintro y ⟨x, rfl⟩
    have hxmem : (x : G) ∈ (↑C : Set G) * (↑N : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right C N hCN]
      exact hE x.2
    obtain ⟨c, hc, n, hn, hcn⟩ := hxmem
    refine ⟨⟨c, hc⟩, ?_⟩
    show q (Subgroup.inclusion hCH ⟨c, hc⟩) = q (Subgroup.inclusion hEH x)
    have hsub : (Subgroup.inclusion hEH x : ↥H) =
        Subgroup.inclusion hCH ⟨c, hc⟩ * ⟨n, hNH hn⟩ := by
      refine Subtype.ext ?_
      show (x : G) = c * n
      rw [← hcn]
    rw [hsub, map_mul, hqker ⟨n, hNH hn⟩ |>.2 hn, mul_one]
  have hexp : ∀ y : ↥f.range, y ^ p = 1 := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    have hxp : x ^ p = 1 := Subtype.ext (by simpa using hEel.2 x.1 x.2)
    refine Subtype.ext ?_
    show (y : H ⧸ N.subgroupOf H) ^ p = 1
    rw [show (y : H ⧸ N.subgroupOf H) = f x from hx.symm, ← map_pow, hxp, map_one]
  haveI : IsCyclic ↥f.range := Subgroup.isCyclic_of_le hle_range
  have hpr : Nat.card ↥f.range ≤ p :=
    card_le_prime_of_cyclic_of_pow_eq_one hp hexp
  calc Nat.card ↥E = Nat.card ↥f.range * Nat.card ↥(E ⊓ N) := hcard
    _ ≤ p * Nat.card ↥(E ⊓ N) := Nat.mul_le_mul_right _ hpr

end GeneralGroupTheory

section TwistedTorus

variable (τ : Tag) (K : Type) [Field K]

private def twistDiagHom (i j : Fin τ.rank) (hij : i ≠ j) : Kˣ →* (Fin τ.rank → Kˣ) where
  toFun a := Pi.mulSingle i a * Pi.mulSingle j a⁻¹
  map_one' := by
    funext k
    by_cases hki : k = i
    · subst hki
      simp [Pi.mulSingle_eq_of_ne hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]
      · simp [Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj]
  map_mul' a b := by
    funext k
    by_cases hki : k = i
    · subst hki
      simp [Pi.mulSingle_eq_of_ne hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [Pi.mulSingle_eq_of_ne (Ne.symm hij), mul_comm]
      · simp [Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj]

private theorem coe_torusCoordHom_twistDiagHom {i j : Fin τ.rank} (hij : i ≠ j) (a : Kˣ) :
    ((torusCoordHom τ K (twistDiagHom (K := K) (τ := τ) i j hij a) : ↥(torusGroup τ K)) :
        ModGL τ K) = torusElt τ K i a * torusElt τ K j a⁻¹ := by
  rw [show twistDiagHom (K := K) (τ := τ) i j hij a =
    Pi.mulSingle i a * Pi.mulSingle j a⁻¹ from rfl]
  rw [map_mul]
  simp only [Subgroup.coe_mul, coe_torusCoordHom_mulSingle]

def twistedTorusSub (i j : Fin τ.rank) (hij : i ≠ j) : Subgroup (ModGL τ K) :=
  ((Subgroup.subtype (torusGroup τ K)).comp
    ((torusCoordHom τ K).comp (twistDiagHom (K := K) (τ := τ) i j hij))).range

theorem mem_twistedTorusSub {i j : Fin τ.rank} (hij : i ≠ j) {g : ModGL τ K} :
    g ∈ twistedTorusSub τ K i j hij ↔ ∃ a : Kˣ, torusElt τ K i a * torusElt τ K j a⁻¹ = g := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (coe_torusCoordHom_twistDiagHom (τ := τ) (K := K) hij a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, coe_torusCoordHom_twistDiagHom (τ := τ) (K := K) hij a⟩

theorem twistedTorusSub_le_torusGroup {i j : Fin τ.rank} (hij : i ≠ j) :
    twistedTorusSub τ K i j hij ≤ torusGroup τ K := by
  rintro g ⟨a, rfl⟩
  exact (torusCoordHom τ K (twistDiagHom (τ := τ) (K := K) i j hij a)).2

theorem twistedTorusSub_le_normalizer {i j : Fin τ.rank} (hij : i ≠ j)
    (A : Set (Fin τ.rank)) :
    twistedTorusSub τ K i j hij ≤
      Subgroup.normalizer (subsystemGroup τ K A : Set (ModGL τ K)) :=
  (twistedTorusSub_le_torusGroup (τ := τ) (K := K) (i := i) (j := j) hij).trans
    (RootTorus.torusGroup_le_normalizer_subsystemGroup A)

private theorem torusCoordHom_mem_sup {i j : Fin τ.rank} (hij : i ≠ j)
    {A : Set (Fin τ.rank)} (hAcompl : ∀ k, k ∉ A ↔ k = i ∨ k = j)
    (u : Fin τ.rank → Kˣ) (huv : u i * u j = 1) :
    ((torusCoordHom τ K u : ↥(torusGroup τ K)) : ModGL τ K) ∈
      twistedTorusSub τ K i j hij ⊔ subsystemGroup τ K A := by
  classical
  have hiA : i ∉ A := (hAcompl i).mpr (Or.inl rfl)
  have hjA : j ∉ A := (hAcompl j).mpr (Or.inr rfl)
  have huj : u j = (u i)⁻¹ := eq_inv_of_mul_eq_one_right huv
  let uA : Fin τ.rank → Kˣ := fun k => if k ∈ A then u k else 1
  let uC : Fin τ.rank → Kˣ := Pi.mulSingle i (u i) * Pi.mulSingle j (u j)
  have hu_eq : u = uA * uC := by
    funext k
    by_cases hk : k ∈ A
    · have hki : k ≠ i := fun h => hiA (h ▸ hk)
      have hkj : k ≠ j := fun h => hjA (h ▸ hk)
      have h1 : uA k = u k := by simp [uA, hk]
      have h2 : uC k = 1 := by
        simp [uC, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj]
      simp [Pi.mul_apply, h1, h2]
    · have h1 : uA k = 1 := by simp [uA, hk]
      rcases (hAcompl k).mp hk with hk' | hk'
      · subst hk'
        have h2 : uC k = u k := by
          simp [uC, Pi.mulSingle_eq_of_ne hij]
        simp [Pi.mul_apply, h1, h2]
      · subst hk'
        have h2 : uC k = u k := by
          simp [uC, Pi.mulSingle_eq_of_ne (Ne.symm hij)]
        simp [Pi.mul_apply, h1, h2]
  have hmemA : ((torusCoordHom τ K uA : ↥(torusGroup τ K)) : ModGL τ K) ∈
      subsystemGroup τ K A := by
    rw [coe_torusCoordHom]
    refine subsystemTorus_le_subsystemGroup (Subgroup.list_prod_mem _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    by_cases hk : k ∈ A
    · exact Subgroup.subset_closure ⟨k, hk, uA k, rfl⟩
    · rw [show uA k = 1 from by simp [uA, hk], torusElt_one]
      exact Subgroup.one_mem _
  have hmemC : ((torusCoordHom τ K uC : ↥(torusGroup τ K)) : ModGL τ K) ∈
      twistedTorusSub τ K i j hij := by
    have hCeq : uC = twistDiagHom (K := K) (τ := τ) i j hij (u i) := by
      funext k
      by_cases hki : k = i
      · subst hki
        simp [uC, twistDiagHom, Pi.mulSingle_eq_of_ne hij]
      · by_cases hkj : k = j
        · subst hkj
          simp [uC, twistDiagHom, huj, Pi.mulSingle_eq_of_ne (Ne.symm hij)]
        · simp [uC, hki, hkj, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj,
            twistDiagHom]
    rw [hCeq]
    exact (mem_twistedTorusSub (τ := τ) (K := K) hij).mpr
      ⟨u i, (coe_torusCoordHom_twistDiagHom (τ := τ) (K := K) hij (u i)).symm⟩
  have hC := twistedTorusSub_le_normalizer (τ := τ) (K := K) hij A
  have htg : ((torusCoordHom τ K u : ↥(torusGroup τ K)) : ModGL τ K) =
      ((torusCoordHom τ K uC : ↥(torusGroup τ K)) : ModGL τ K) *
        ((torusCoordHom τ K uA : ↥(torusGroup τ K)) : ModGL τ K) := by
    have h1 : torusCoordHom τ K u = torusCoordHom τ K uA * torusCoordHom τ K uC := by
      rw [hu_eq, map_mul]
    have h2 : torusCoordHom τ K uA * torusCoordHom τ K uC =
        torusCoordHom τ K uC * torusCoordHom τ K uA :=
      Subtype.ext (RootTorus.torusGroup_mul_comm (torusCoordHom τ K uA).2
        (torusCoordHom τ K uC).2)
    simpa [Subgroup.coe_mul] using congrArg Subtype.val (h1.trans h2)
  have hprod : ((torusCoordHom τ K u : ↥(torusGroup τ K)) : ModGL τ K) ∈
      (↑(twistedTorusSub τ K i j hij) : Set (ModGL τ K)) *
        (↑(subsystemGroup τ K A) : Set (ModGL τ K)) := by
    rw [htg]
    exact ⟨_, hmemC, _, hmemA, rfl⟩
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right (twistedTorusSub τ K i j hij)
    (subsystemGroup τ K A) hC] at hprod
  exact hprod

end TwistedTorus

section ContractsA1A2

variable {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
  (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
  {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
  {E : Subgroup (ModGL TwistTag.E6.tag F)}

include hF σ hσ hp hp2 hpq

theorem card_le_mul_card_inf_subsystemGroup_A1A2
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ subsystemGroup TwistTag.E6.tag F
      {i | i.val ≠ 2 ∧ i.val ≠ 4}) := by
  have hAcompl : ∀ k : Fin TwistTag.E6.tag.rank,
      k ∉ {i | i.val ≠ 2 ∧ i.val ≠ 4} ↔
        k = (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) ∨
          k = (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) := by
    intro k
    constructor
    · intro hk
      have h : k.val = 2 ∨ k.val = 4 := by
        simp only [Set.mem_setOf_eq, not_and_or, not_not] at hk
        exact hk
      rcases h with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    · rintro (h | h) <;> rw [h] <;> simp
  have hw4 : gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧
      i.val ≠ 4} 4 =
      fun k => (if k = (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0) +
        (if k = (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0) :=
    gradedWeight_twE6MaxA1A2
  have hA2 : ∀ i ∈ {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4},
      TwistTag.E6.perm i ∈ {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} :=
    fun i hi => perm_mem_setA1A2 hi
  have hw2 : ∀ i, gradedWeight TwistTag.E6.tag
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4 (TwistTag.E6.perm i) =
      gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4 i :=
    fun i => gradedWeight_twE6MaxA1A2_perm i
  have hEsub : E ≤ twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
      (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank)
      (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) ⊔
      subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} := by
    intro g hgE
    have hEM := hE hgE
    have hgM : g ∈ parabolicLevi TwistTag.E6.tag F
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} := by
      have h := hEM.1
      rw [orbitUnion_twE6MaxA1A2] at h
      exact h
    have hgfix : twistHom TwistTag.E6 F σ.toRingHom g = g :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 F σ.toRingHom).1
        (graphFixedRootGroup_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom) hEM.2)).2
    have hgp : g ^ p = 1 := hEel.2 g hgE
    have hχg := gradedDet_eq_one_of_twist_fixed hF σ hσ hp hp2 hpq (d := 4) (by norm_num)
      hA2 hw2 hgM hgfix hgp
    have hsup' : g ∈ (↑(torusGroup TwistTag.E6.tag F ⊔
        subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧
          i.val ≠ 4}) : Set (ModGL TwistTag.E6.tag F)) := hgM
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup TwistTag.E6.tag F)
      (subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4})
      (RootTorus.torusGroup_le_normalizer_subsystemGroup _)] at hsup'
    obtain ⟨t, htT, l, hlL, htl⟩ := hsup'
    have hχl : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F)
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4
        ⟨l, Subgroup.mem_sup_right hlL⟩ = 1 := by
      obtain ⟨u₀, hu₀⟩ := exists_unit_sq_ne_one_of_card hF
      exact parabolicGradedDet_eq_one_of_mem_leviGenerators 4 u₀ hu₀ l hlL
    have hχt : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F)
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4
        ⟨t, Subgroup.mem_sup_left htT⟩ = 1 := by
      have he : (⟨g, hgM⟩ : ↥(parabolicLevi TwistTag.E6.tag F
          {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4})) =
          (⟨t, Subgroup.mem_sup_left htT⟩ : ↥(parabolicLevi TwistTag.E6.tag F
            {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4})) *
            ⟨l, Subgroup.mem_sup_right hlL⟩ := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_mul]
        exact htl.symm
      rw [he, map_mul, hχl, mul_one] at hχg
      exact hχg
    obtain ⟨u, hu⟩ := exists_eq_torusCoordHom_of_mem_torusGroup (τ := TwistTag.E6.tag) (K := F) htT
    have htcoe : (⟨t, Subgroup.mem_sup_left htT⟩ : ↥(parabolicLevi TwistTag.E6.tag F
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4})) =
        Subgroup.inclusion (le_sup_left : torusGroup TwistTag.E6.tag F ≤ parabolicLevi
          TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4})
          (torusCoordHom TwistTag.E6.tag F u) := Subtype.ext hu
    have hχtu : (∏ i, (u i) ^ gradedWeight TwistTag.E6.tag
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} 4 i) = 1 := by
      rw [← parabolicGradedDet_torusCoordHom (τ := TwistTag.E6.tag) (K := F)
        (A := {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4}) (d := 4) (by norm_num),
        ← htcoe]
      exact hχt
    have hu24 : u (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) *
        u (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) = 1 := by
      rw [hw4] at hχtu
      have hprod : (∏ k, (u k) ^ ((if k = (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) then
          (1 : ℤ) else 0) + (if k = (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) then
            (1 : ℤ) else 0))) =
          u (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) *
            u (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) := by
        have hsub : (∏ k, (u k) ^ ((if k = (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) then
            (1 : ℤ) else 0) + (if k = (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) then
              (1 : ℤ) else 0))) =
            ∏ k ∈ ({(⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank),
              (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank)} : Finset (Fin TwistTag.E6.tag.rank)),
              (u k) ^ ((if k = (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0) +
                (if k = (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0)) := by
          refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
          intro x _ hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hx2 : x ≠ (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) := hx.1
          have hx4 : x ≠ (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) := hx.2
          simp only [if_neg hx2, if_neg hx4, add_zero, zpow_zero]
        rw [hsub, Finset.prod_insert (by simp), Finset.prod_singleton]
        simp
      rw [← hprod]
      exact hχtu
    have htC : t ∈ twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
        (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank)
        (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) ⊔
        subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧
          i.val ≠ 4} := by
      have h := torusCoordHom_mem_sup (τ := TwistTag.E6.tag) (K := F) (by decide) hAcompl u hu24
      rw [← hu] at h
      exact h
    rw [← htl]
    exact Subgroup.mul_mem _ htC (Subgroup.mem_sup_right hlL)
  have hCcyc : IsCyclic ↥(twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
      (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank)
      (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide)) := by
    haveI hfin : Finite Fˣ := Finite.of_injective (fun u : Fˣ => (u : F))
      (fun a b h => Units.ext h)
    haveI : IsCyclic Fˣ := instIsCyclicUnitsOfFinite
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hCN : twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
      (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank)
      (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) ≤
      Subgroup.normalizer (subsystemGroup TwistTag.E6.tag F
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 2 ∧ i.val ≠ 4} :
          Set (ModGL TwistTag.E6.tag F)) := by
    intro g hg
    have hgT : g ∈ torusGroup TwistTag.E6.tag F := by
      rcases hg with ⟨a, rfl⟩
      exact (torusCoordHom TwistTag.E6.tag F
        (twistDiagHom (K := F) (τ := TwistTag.E6.tag)
          (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank)
          (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) a)).2
    exact RootTorus.torusGroup_le_normalizer_subsystemGroup _ hgT
  exact card_le_mul_card_inf_of_le_sup_cyclic hp hCcyc hCN hEsub hEel

end ContractsA1A2

section ContractsD4

variable {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2)
  (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n))
  {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
  {E : Subgroup (ModGL TwistTag.E6.tag F)}

include hF σ hσ hp hp2 hpq

theorem card_le_mul_card_inf_subsystemGroup_D4
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxD4)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ subsystemGroup TwistTag.E6.tag F
      {i | i.val ≠ 0 ∧ i.val ≠ 5}) := by
  have hAcompl : ∀ k : Fin TwistTag.E6.tag.rank,
      k ∉ {i | i.val ≠ 0 ∧ i.val ≠ 5} ↔
        k = (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) ∨
          k = (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) := by
    intro k
    constructor
    · intro hk
      have h : k.val = 0 ∨ k.val = 5 := by
        simp only [Set.mem_setOf_eq, not_and_or, not_not] at hk
        exact hk
      rcases h with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    · rintro (h | h) <;> rw [h] <;> simp
  have hw4 : gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧
      i.val ≠ 5} 2 =
      fun k => 4 * (if k = (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0) +
        4 * (if k = (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0) :=
    gradedWeight_twE6MaxD4
  have hA2 : ∀ i ∈ {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5},
      TwistTag.E6.perm i ∈ {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} :=
    fun i hi => perm_mem_setD4 hi
  have hw2 : ∀ i, gradedWeight TwistTag.E6.tag
      {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2 (TwistTag.E6.perm i) =
      gradedWeight TwistTag.E6.tag {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2 i :=
    fun i => gradedWeight_twE6MaxD4_perm i
  have hEsub : E ≤ twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
      (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank)
      (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) ⊔
      subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} := by
    intro g hgE
    have hEM := hE hgE
    have hgM : g ∈ parabolicLevi TwistTag.E6.tag F
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} := by
      have h := hEM.1
      rw [orbitUnion_twE6MaxD4] at h
      exact h
    have hgfix : twistHom TwistTag.E6 F σ.toRingHom g = g :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 F σ.toRingHom).1
        (graphFixedRootGroup_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom) hEM.2)).2
    have hgp : g ^ p = 1 := hEel.2 g hgE
    have hχg := gradedDet_eq_one_of_twist_fixed hF σ hσ hp hp2 hpq (d := 2) (by norm_num)
      hA2 hw2 hgM hgfix hgp
    have hsup' : g ∈ (↑(torusGroup TwistTag.E6.tag F ⊔
        subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧
          i.val ≠ 5}) : Set (ModGL TwistTag.E6.tag F)) := hgM
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup TwistTag.E6.tag F)
      (subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5})
      (RootTorus.torusGroup_le_normalizer_subsystemGroup _)] at hsup'
    obtain ⟨t, htT, l, hlL, htl⟩ := hsup'
    have hχl : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F)
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2
        ⟨l, Subgroup.mem_sup_right hlL⟩ = 1 := by
      obtain ⟨u₀, hu₀⟩ := exists_unit_sq_ne_one_of_card hF
      exact parabolicGradedDet_eq_one_of_mem_leviGenerators 2 u₀ hu₀ l hlL
    have hχt : parabolicGradedDet (τ := TwistTag.E6.tag) (K := F)
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2
        ⟨t, Subgroup.mem_sup_left htT⟩ = 1 := by
      have he : (⟨g, hgM⟩ : ↥(parabolicLevi TwistTag.E6.tag F
          {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5})) =
          (⟨t, Subgroup.mem_sup_left htT⟩ : ↥(parabolicLevi TwistTag.E6.tag F
            {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5})) *
            ⟨l, Subgroup.mem_sup_right hlL⟩ := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_mul]
        exact htl.symm
      rw [he, map_mul, hχl, mul_one] at hχg
      exact hχg
    obtain ⟨u, hu⟩ := exists_eq_torusCoordHom_of_mem_torusGroup (τ := TwistTag.E6.tag) (K := F) htT
    have htcoe : (⟨t, Subgroup.mem_sup_left htT⟩ : ↥(parabolicLevi TwistTag.E6.tag F
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5})) =
        Subgroup.inclusion (le_sup_left : torusGroup TwistTag.E6.tag F ≤ parabolicLevi
          TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5})
          (torusCoordHom TwistTag.E6.tag F u) := Subtype.ext hu
    have hχtu : (∏ i, (u i) ^ gradedWeight TwistTag.E6.tag
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} 2 i) = 1 := by
      rw [← parabolicGradedDet_torusCoordHom (τ := TwistTag.E6.tag) (K := F)
        (A := {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5}) (d := 2) (by norm_num),
        ← htcoe]
      exact hχt
    have hu24 : u (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) *
        u (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) = 1 := by
      rw [hw4] at hχtu
      have hprod : (∏ k, (u k) ^ (4 * (if k = (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) then
          (1 : ℤ) else 0) + 4 * (if k = (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) then
            (1 : ℤ) else 0))) =
          u (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) ^ 4 *
            u (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) ^ 4 := by
        have hsub : (∏ k, (u k) ^ (4 * (if k = (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) then
            (1 : ℤ) else 0) + 4 * (if k = (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) then
              (1 : ℤ) else 0))) =
            ∏ k ∈ ({(⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank),
              (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank)} : Finset (Fin TwistTag.E6.tag.rank)),
              (u k) ^ (4 * (if k = (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0) +
                4 * (if k = (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) then (1 : ℤ) else 0)) := by
          refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
          intro x _ hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hx0 : x ≠ (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) := by simpa using hx.1
          simp [hx0, hx.2]
        rw [hsub, Finset.prod_insert (by simp), Finset.prod_singleton]
        simp
      have h45 : (u (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) *
          u (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank)) ^ 4 = 1 := by
        rw [mul_pow]
        rw [← hprod]
        exact hχtu
      exact eq_one_of_pow_four_eq_one hF h45
    have htC : t ∈ twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
        (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank)
        (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) ⊔
        subsystemGroup TwistTag.E6.tag F {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧
          i.val ≠ 5} := by
      have h := torusCoordHom_mem_sup (τ := TwistTag.E6.tag) (K := F) (by decide) hAcompl u hu24
      rw [← hu] at h
      exact h
    rw [← htl]
    exact Subgroup.mul_mem _ htC (Subgroup.mem_sup_right hlL)
  have hCcyc : IsCyclic ↥(twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
      (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank)
      (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide)) := by
    haveI hfin : Finite Fˣ := Finite.of_injective (fun u : Fˣ => (u : F))
      (fun a b h => Units.ext h)
    haveI : IsCyclic Fˣ := instIsCyclicUnitsOfFinite
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hCN : twistedTorusSub (τ := TwistTag.E6.tag) (K := F)
      (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank)
      (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) ≤
      Subgroup.normalizer (subsystemGroup TwistTag.E6.tag F
        {i : Fin TwistTag.E6.tag.rank | i.val ≠ 0 ∧ i.val ≠ 5} :
          Set (ModGL TwistTag.E6.tag F)) := by
    intro g hg
    have hgT : g ∈ torusGroup TwistTag.E6.tag F := by
      rcases hg with ⟨a, rfl⟩
      exact (torusCoordHom TwistTag.E6.tag F
        (twistDiagHom (K := F) (τ := TwistTag.E6.tag)
          (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank)
          (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) (by decide) a)).2
    exact RootTorus.torusGroup_le_normalizer_subsystemGroup _ hgT
  exact card_le_mul_card_inf_of_le_sup_cyclic hp hCcyc hCN hEsub hEel

end ContractsD4

end CFSG.LocalAnalysis.GLTheoremA
