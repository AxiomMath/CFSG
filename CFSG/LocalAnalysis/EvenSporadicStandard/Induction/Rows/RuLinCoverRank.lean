module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuCoverRankGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuOrders
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.RankThree.PartTwo.Sec4.Census CFSG.Blueprint
open scoped commutatorElement

section Linear

variable {n : ℕ} {K : Type} [Field K]

noncomputable def projSLn (n : ℕ) (K : Type) [Field K] :
    SpecialLinearGroup (Fin n) K →* StatedProj (StatedSL n K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).comp
    (specialLinearGroupEquivStatedSL n K).toMonoidHom

theorem projSLn_eq_one_iff (g : SpecialLinearGroup (Fin n) K) :
    projSLn n K g = 1 ↔ g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
  rw [projSLn, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← map_center_eq_statedScalars n K]
  exact Subgroup.mem_map_iff_mem (specialLinearGroupEquivStatedSL n K).injective

theorem eq_zero_of_rootElt_mem_center {i l : Fin n} (hil : i ≠ l) {a : K}
    (h : rootElt i l a ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) : a = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h1 := congrFun (congrFun hr i) l
  rw [coe_rootElt_of_ne hil] at h1
  simp [Matrix.scalar_apply, transvection, hil] at h1
  exact h1.symm

theorem three_le_pRank_of_psl_cover {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    [Finite K] [CharP K 2] (h8 : 8 ≤ Nat.card K) {J : Type} [Group J] [Finite J]
    {φ : J →* StatedProj (StatedSL n K)} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) : 3 ≤ CFSG.pRank 2 J := by
  let r : Multiplicative K →* StatedProj (StatedSL n K) :=
    { toFun := fun t => projSLn n K (rootElt i l (Multiplicative.toAdd t))
      map_one' := by simp [rootElt_zero]
      map_mul' := fun s t => by simp [rootElt_add] }
  have hr : ∀ t : K, r (Multiplicative.ofAdd t) = projSLn n K (rootElt i l t) := fun t => rfl
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : projSLn n K (rootElt i l (Multiplicative.toAdd t)) = 1 := ht
    have := eq_zero_of_rootElt_mem_center hil ((projSLn_eq_one_iff _).1 h1)
    exact Multiplicative.toAdd.injective this
  have hW2 : ∀ x ∈ r.range, x ^ 2 = 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have : t ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul]
      exact CharTwo.add_self_eq_zero _
    rw [this, map_one]
  have hW8 : 8 ≤ Nat.card r.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact h8
  have htr : ∀ x ∈ r.range, x ≠ 1 → ∃ g : StatedProj (StatedSL n K),
      g * r (Multiplicative.ofAdd 1) * g⁻¹ = x := by
    rintro _ ⟨t, rfl⟩ ht1
    have ht0 : Multiplicative.toAdd t ≠ 0 := fun h => ht1 (by
      have : t = 1 := Multiplicative.toAdd.injective (by simpa using h)
      rw [this, map_one])
    refine ⟨projSLn n K (diagElt (corootVec i j (Multiplicative.toAdd t))
      (prod_corootVec i j ht0)), ?_⟩
    rw [hr, ← map_inv, ← map_mul, ← map_mul, diagElt_conj_rootElt,
      corootVec_apply_left hij, corootVec_apply_of_ne hil.symm hjl.symm, inv_one, mul_one, mul_one]
    rfl
  have hcomm : ∀ y y' : J, φ y ∈ r.range → φ y' ∈ r.range → y * y' = y' * y := by
    intro y y' hy hy'
    obtain ⟨t₁, ht₁⟩ := hy
    obtain ⟨t₂, ht₂⟩ := hy'
    obtain ⟨p, hp⟩ := hφ (projSLn n K (rootElt i j (Multiplicative.toAdd t₂)))
    obtain ⟨q, hq⟩ := hφ (projSLn n K (rootElt j l 1))
    refine TransitiveLift.commute_of_map_eq_commutatorElement hker (p := p) (q := q) ?_ ?_ ?_
    · rw [← ht₁, hp]
      exact (show Commute (rootElt i l (Multiplicative.toAdd t₁))
        (rootElt i j (Multiplicative.toAdd t₂)) from
          rootElt_mul_comm hil.symm hij.symm _ _).map (projSLn n K)
    · rw [← ht₁, hq]
      exact (show Commute (rootElt i l (Multiplicative.toAdd t₁)) (rootElt j l 1) from
          rootElt_mul_comm hjl.symm hil.symm _ _).map (projSLn n K)
    · rw [map_commutatorElement, hp, hq, ← map_commutatorElement,
        commutatorElement_rootElt hij hjl hil, mul_one, ← ht₂]
      rfl
  exact three_le_pRank_of_isotropic hφ hker hW2 hW8 htr hcomm

end Linear

theorem three_le_pRank_of_psl_model_cover {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m) {X : Type}
    [Group X] [Finite X] (h : LieModel (X ⧸ center X) .PSL n 2 m) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by omega) h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  let φ : X →* StatedProj (StatedSL n K) := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ center X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  exact three_le_pRank_of_psl_cover (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
    (l := ⟨2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) h8 hφ hker

end CFSG.EvenSporadicStandard.Induction
