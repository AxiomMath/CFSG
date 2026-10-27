module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidComm

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Root

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)

omit [CharP K 2] in
theorem oRhoOneGL_slTr_eq (c : K) :
    ((oRhoOneGL oe (slTr c) : GL ι K) : Matrix ι ι K) = 1 + c • oN₀ K oe := by
  ext i j
  obtain ⟨d, rfl⟩ := oe.surjective i
  obtain ⟨d', rfl⟩ := oe.surjective j
  rw [coe_oRhoOneGL, oblk_apply, rhoOneMat_apply]
  rcases d with a | s | s <;> rcases d' with b | t | t
  all_goals (try fin_cases s) <;> (try fin_cases t) <;>
    simp [oN₀, slTr, swapM, Matrix.one_apply, fromBlocks]

omit [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_zero_left (Q₂ : QuadraticForm K (ι₂ → K)) (c : K) :
    qE oe Q₂ 0 c = 1 + c • oN₀ K oe := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [Matrix.add_mulVec, one_mulVec, Matrix.smul_mulVec, oN₀_mulVec]
  funext i
  obtain ⟨d, rfl⟩ := oe.surjective i
  rcases d with a | s | s
  · rw [qE_mulVec_ou]
    simp
  · rw [qE_mulVec_ox]
    fin_cases s <;> simp [qAlpha]
  · rw [qE_mulVec_oy]
    simp

theorem qEGL_zero (Q₂ : QuadraticForm K (ι₂ → K)) (c : K) :
    qEGL oe Q₂ 0 c = oRhoOneGL oe (slTr c) :=
  Units.ext ((qE_zero_left oe Q₂ c).trans (oRhoOneGL_slTr_eq oe c).symm)

end Root

section Omega

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit hQ in
theorem add_one_ne_zero_of_ne_one {t : K} (ht1 : t ≠ 1) : t + 1 ≠ 0 := fun h =>
  ht1 (by linear_combination h - CharTwo.two_eq_zero (R := K))

theorem exists_qE_eq_commutator {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (u : Fin 2 → ι₂ → K)
    (c : K) :
    ∃ (A : SL(2, K)) (u' : Fin 2 → ι₂ → K) (e : K),
      (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹] ∧
      qEGL oe Q₂ u c = ⁅oRhoTwoGL oe A, qEGL oe Q₂ u' 0⁆ * oRhoOneGL oe (slTr e) := by
  obtain ⟨A, hA⟩ := exists_torusSL ht0
  have h1 := add_one_ne_zero_of_ne_one ht1
  have h2 : t⁻¹ + 1 ≠ 0 := add_one_ne_zero_of_ne_one fun h => ht1 (inv_eq_one.mp h)
  set u' : Fin 2 → ι₂ → K := fun s => if s = 0 then (t + 1)⁻¹ • u 0 else (t⁻¹ + 1)⁻¹ • u 1
    with hu'
  obtain ⟨c'', hc''⟩ := qE_torus_commutator hQ hA u' 0
  have hu : (fun s => if s = 0 then (t + 1) • u' 0 else (t⁻¹ + 1) • u' 1) = u := by
    funext s
    fin_cases s <;> simp [hu', smul_smul, h1, h2]
  rw [hu] at hc''
  refine ⟨A, u', c + c'', hA, ?_⟩
  rw [hc'', ← qEGL_zero oe Q₂]
  apply Units.ext
  rw [Units.val_mul, coe_qEGL, coe_qEGL, coe_qEGL, qE_mul]
  congr 1
  · simp
  · simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, add_zero]
    linear_combination (-c'') * CharTwo.two_eq_zero (R := K)

theorem qEGL_mem_statedOmega (hSL : commutator SL(2, K) = ⊤) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (u : Fin 2 → ι₂ → K) (c : K) : qEGL oe Q₂ u c ∈ StatedOmega ⇑Q := by
  obtain ⟨A, u', e, -, h⟩ := exists_qE_eq_commutator hQ ht0 ht1 u c
  rw [h]
  refine mul_mem ?_ (oRhoOne oe hQ hSL (slTr e)).2
  exact commutator_mem_commutator (oRhoTwoGL_mem_closure oe hQ A)
    (subset_closure (qE_isometry hQ u' 0))

end Omega

section Groups

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

@[expose] noncomputable def oL₀ : Subgroup (GL ι K) :=
  (oRhoTwoGL oe).range ⊔ (StatedOmega ⇑Q₂).map (oKappaGL oe)

@[expose] noncomputable def oXt : Subgroup (GL ι K) := oQE oe Q₂ ⊔ oL₀ oe Q₂

theorem oL₀_le_cenM₀ : oL₀ oe Q₂ ≤ cenM₀ K oe := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact oRhoTwoGL_mem_cenM₀ A
  · rintro _ ⟨Y, -, rfl⟩
    exact oKappaGL_mem_cenM₀ Y

theorem oXt_le_cenM₀ : oXt oe Q₂ ≤ cenM₀ K oe :=
  sup_le (oQE_le_cenM₀ oe Q₂) (oL₀_le_cenM₀ oe Q₂)

variable {oe Q₂} {Q : QuadraticForm K (ι → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit [CharP K 2] in
theorem oL₀_le_statedOmega (hSL : commutator SL(2, K) = ⊤) :
    oL₀ oe Q₂ ≤ StatedOmega ⇑Q := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact (oRhoTwo oe hQ hSL A).2
  · rintro _ ⟨Y, hY, rfl⟩
    exact oKappaGL_mem oe hQ hY

theorem oXt_le_statedOmega (hSL : commutator SL(2, K) = ⊤) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) : oXt oe Q₂ ≤ StatedOmega ⇑Q := by
  refine sup_le ?_ (oL₀_le_statedOmega hQ hSL)
  rintro _ ⟨⟨u, c⟩, rfl⟩
  exact qEGL_mem_statedOmega hQ hSL ht0 ht1 u c

end Groups

end CFSG.ComponentClassification.RankTwoClassical.ORigid
