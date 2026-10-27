module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks5
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
variable {p : ℕ} {σ : F →+* F}

private theorem map_avgCoeff_of_mul_card_eq_one (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (C : Subgroup ↥A)
    (hC : avgCoeff A C * (((Fintype.card ↥C : ℕ) : F)) = 1) :
    σ (avgCoeff A C) = avgCoeff A C := by
  have hn : (((Fintype.card ↥C : ℕ) : F)) ≠ 0 :=
    natCast_card_subgroup_ne_zero' A hp hpF hA C
  refine mul_right_cancel₀ hn ?_
  calc σ (avgCoeff A C) * ((Fintype.card ↥C : ℕ) : F)
      = σ (avgCoeff A C) * σ ((Fintype.card ↥C : ℕ) : F) := by rw [map_natCast]
    _ = σ (avgCoeff A C * ((Fintype.card ↥C : ℕ) : F)) := (map_mul σ _ _).symm
    _ = σ 1 := by rw [hC]
    _ = 1 := map_one σ
    _ = avgCoeff A C * ((Fintype.card ↥C : ℕ) : F) := hC.symm

theorem sumOp_sesq_adjoint (B : V →ₛₗ[σ] V →ₗ[F] F)
    (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
    (C : Subgroup ↥A) (x y : V) :
    B (sumOp (actionEnd A) C x) y = B x (sumOp (actionEnd A) C y) := by
  unfold sumOp
  simp only [LinearMap.sum_apply, LinearMap.map_sum₂, map_sum]
  have h : ∀ a : C, B (actionEnd A (a : ↥A) x) y =
      B x (actionEnd A ((a⁻¹ : C) : ↥A) y) := fun a => by
    have h1 := hB (a : ↥A) x (actionEnd A ((a⁻¹ : C) : ↥A) y)
    have h2 : ((a : ↥A) : V ≃ₗ[F] V) (actionEnd A ((a⁻¹ : C) : ↥A) y) = y := by
      show (((a : ↥A) * ((a⁻¹ : C) : ↥A) : ↥A) : V ≃ₗ[F] V) y = y
      simp
    rw [h2] at h1
    simpa using h1
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.inv C) _ _ (fun a => rfl)

theorem projBlock_sesq (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (B : V →ₛₗ[σ] V →ₗ[F] F)
    (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
    (D : Hyperplane A p) (u v : V) :
    B (projBlock A hp hpF hA D u) v = B u (projBlock A hp hpF hA D v) := by
  have hsum : ∀ C : Subgroup ↥A,
      B (sumOp (actionEnd A) C u) v = B u (sumOp (actionEnd A) C v) :=
    fun C => sumOp_sesq_adjoint A B hB C u v
  have hnD : (((Fintype.card ↥D.1 : ℕ) : F)) ≠ 0 :=
    natCast_card_subgroup_ne_zero' A hp hpF hA D.1
  by_cases hblock : blockSpace A D.1 = ⊥
  · have hP : projBlock A hp hpF hA D = 0 := LinearMap.ext fun x => by
      simpa [hblock] using projBlock_apply_mem A hp hpF hA D x
    rw [hP]
    simp
  ·
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hblock
    have hcD : avgCoeff A D.1 * (((Fintype.card ↥D.1 : ℕ) : F)) = 1 := by
      have h1 : sumOp (actionEnd A) D.1 w = (((Fintype.card ↥D.1 : ℕ) : F)) • w :=
        sumOp_apply_of_fix (actionEnd A) D.1
          ((mem_fixSub_iff' A).mpr ((mem_blockSpace A).mp hw).1)
      have h2 : sumOp (actionEnd A) ⊤ w = 0 := ((mem_blockSpace A).mp hw).2
      have h3 := projBlock_apply_of_mem A hp hpF hA D hw
      rw [projBlock_apply_eq, h1, h2, smul_zero, sub_zero, smul_smul] at h3
      have h4 : (avgCoeff A D.1 * (((Fintype.card ↥D.1 : ℕ) : F)) - 1) • w = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]
        exact h3
      rcases smul_eq_zero.mp h4 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hw0
    have hσD := map_avgCoeff_of_mul_card_eq_one (σ := σ) A hp hpF hA D.1 hcD
    by_cases hfix : fixedSpaceOf A = ⊥
    ·
      have htop : sumOp (actionEnd A) ⊤ = 0 := LinearMap.ext fun x => by
        have := sumOp_mem_fixSub (actionEnd A) (⊤ : Subgroup ↥A) x
        simpa [hfix] using this
      simp only [projBlock, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smulₛₗ,
        hsum, hσD, htop, LinearMap.zero_apply, smul_zero, sub_zero, RingHom.id_apply]
    ·
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
      have hrel : avgCoeff A D.1 * (((Fintype.card ↥D.1 : ℕ) : F)) =
          avgCoeff A ⊤ * (((Fintype.card ↥(⊤ : Subgroup ↥A) : ℕ) : F)) := by
        have h1 : sumOp (actionEnd A) D.1 c = (((Fintype.card ↥D.1 : ℕ) : F)) • c :=
          sumOp_apply_of_fix (actionEnd A) D.1 ((mem_fixSub_iff' A).mpr fun d _ =>
            (mem_fixedSpaceOf A).mp hc d)
        have h2 : sumOp (actionEnd A) ⊤ c =
            (((Fintype.card ↥(⊤ : Subgroup ↥A) : ℕ) : F)) • c :=
          sumOp_apply_of_fix (actionEnd A) ⊤ ((mem_fixSub_iff' A).mpr fun d _ =>
            (mem_fixedSpaceOf A).mp hc d)
        have h3 := projBlock_apply_fixed A hp hpF hA D hc
        rw [projBlock_apply_eq, h1, h2, smul_smul, smul_smul, sub_eq_zero] at h3
        have h4 : (avgCoeff A D.1 * (((Fintype.card ↥D.1 : ℕ) : F)) -
            avgCoeff A ⊤ * (((Fintype.card ↥(⊤ : Subgroup ↥A) : ℕ) : F))) • c = 0 := by
          rw [sub_smul, h3, sub_self]
        rcases smul_eq_zero.mp h4 with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hc0
      have hcT : avgCoeff A ⊤ * (((Fintype.card ↥(⊤ : Subgroup ↥A) : ℕ) : F)) = 1 :=
        hrel.symm.trans hcD
      have hσT := map_avgCoeff_of_mul_card_eq_one (σ := σ) A hp hpF hA ⊤ hcT
      simp only [projBlock, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smulₛₗ,
        hsum, hσD, hσT, RingHom.id_apply]

theorem blockSpace_sesq_orthogonal (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (B : V →ₛₗ[σ] V →ₗ[F] F)
    (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
    {D E : Hyperplane A p} (hDE : D ≠ E) {u v : V} (hu : u ∈ blockSpace A D.1)
    (hv : v ∈ blockSpace A E.1) : B u v = 0 := by
  haveI : IsMulCommutative ↥A := hA.1
  have hcomm : ∀ a ∈ (⊤ : Subgroup ↥A), ∀ b ∈ (⊤ : Subgroup ↥A), a * b = b * a :=
    fun a _ b _ => mul_comm' a b
  have hgen : D.1 ⊔ E.1 = ⊤ := by
    refine HyperBlocks.sup_eq_of_ne_relIndex_prime hp le_top le_top ?_ ?_ ?_
    · rw [Subgroup.relIndex_top_right]; exact D.2
    · rw [Subgroup.relIndex_top_right]; exact E.2
    · intro h
      exact hDE (Subtype.ext h.symm).symm
  have hcE : ∀ f' ∈ E.1, actionEnd A f' * sumOp (actionEnd A) D.1 =
      sumOp (actionEnd A) D.1 * actionEnd A f' := fun f' hf' => by
    unfold sumOp
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← map_mul, ← map_mul, mul_comm' f' f]
  have hu0 : sumOp (actionEnd A) D.1 v = 0 := by
    have h1 : sumOp (actionEnd A) D.1 v ∈ fixSub (actionEnd A) (⊤ : Subgroup ↥A) := by
      have htop : (⊤ : Subgroup ↥A) ≤ stabVec (actionEnd A) (sumOp (actionEnd A) D.1 v) := by
        rw [← hgen]
        refine sup_le (sumOp_mem_fixSub (actionEnd A) D.1 v) (fun f' hf' => ?_)
        show actionEnd A f' (sumOp (actionEnd A) D.1 v) = sumOp (actionEnd A) D.1 v
        rw [← Module.End.mul_apply, hcE f' hf', Module.End.mul_apply, hv.1 f' hf']
      exact htop
    have h2 : sumOp (actionEnd A) ⊤ (sumOp (actionEnd A) D.1 v) = 0 := by
      have hSS : sumOp (actionEnd A) ⊤ * sumOp (actionEnd A) D.1 =
          ((Fintype.card ↥D.1 : ℕ) : F) • sumOp (actionEnd A) ⊤ := by
        unfold sumOp
        rw [Finset.mul_sum]
        have : ∀ f : D.1, sumOp (actionEnd A) ⊤ * actionEnd A (f : ↥A) =
            sumOp (actionEnd A) ⊤ := fun f => sumOp_mul (actionEnd A) ⊤ (Subgroup.mem_top _)
        unfold sumOp at this
        simp_rw [this]
        simp [Nat.cast_smul_eq_nsmul]
      rw [← Module.End.mul_apply, hSS, LinearMap.smul_apply, LinearMap.mem_ker.mp hv.2,
        smul_zero]
    have h3 := sumOp_apply_of_fix (actionEnd A) ⊤ h1
    rw [h2] at h3
    have h4 := congrArg (fun z => (((Fintype.card A : ℕ) : F))⁻¹ • z) h3.symm
    simpa [smul_smul, inv_mul_cancel₀ (natCast_card_ne_zero A hp hpF hA)] using h4
  have hu' : sumOp (actionEnd A) D.1 u = ((Fintype.card ↥D.1 : ℕ) : F) • u :=
    sumOp_apply_of_fix (actionEnd A) D.1 hu.1
  have h5 : B (sumOp (actionEnd A) D.1 u) v = B u (sumOp (actionEnd A) D.1 v) :=
    sumOp_sesq_adjoint A B hB D.1 u v
  rw [hu', hu0, map_zero] at h5
  simp only [map_smulₛₗ, map_natCast, smul_eq_mul] at h5
  exact (mul_eq_zero.mp h5).resolve_left (natCast_card_subgroup_ne_zero' A hp hpF hA D.1)

theorem blockSpace_ker_sesq_orthogonal (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (B : V →ₛₗ[σ] V →ₗ[F] F)
    (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
    (D : Hyperplane A p) {u v : V} (hu : u ∈ blockSpace A D.1)
    (hv : v ∈ LinearMap.ker (projBlock A hp hpF hA D)) : B u v = 0 := by
  have h1 := projBlock_sesq A hp hpF hA B hB D u v
  rw [projBlock_apply_of_mem A hp hpF hA D hu, LinearMap.mem_ker.mp hv, map_zero] at h1
  exact h1

theorem blockEnd_sesq (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (B : V →ₛₗ[σ] V →ₗ[F] F)
    (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) (u v : V) :
    B (blockEnd A hp hpF hA t ht D u) (blockEnd A hp hpF hA t ht D v) = B u v := by
  have hsup : blockSpace A D.1 ⊔ LinearMap.ker (projBlock A hp hpF hA D) = ⊤ :=
    codisjoint_iff.mp (isCompl_blockSpace_ker A hp hpF hA D).codisjoint
  obtain ⟨u₁, hu₁mem, u₂, hu₂mem, hu⟩ := Submodule.mem_sup.mp (by
    rw [hsup]; exact Submodule.mem_top : u ∈ blockSpace A D.1 ⊔
      LinearMap.ker (projBlock A hp hpF hA D))
  obtain ⟨v₁, hv₁mem, v₂, hv₂mem, hv⟩ := Submodule.mem_sup.mp (by
    rw [hsup]; exact Submodule.mem_top : v ∈ blockSpace A D.1 ⊔
      LinearMap.ker (projBlock A hp hpF hA D))
  have hu₂ : u₂ ∈ LinearMap.ker (projBlock A hp hpF hA D) := hu₂mem
  have hv₂ : v₂ ∈ LinearMap.ker (projBlock A hp hpF hA D) := hv₂mem
  have hu₁ : (t D : V ≃ₗ[F] V) u₁ ∈ blockSpace A D.1 := blockSpace_invariant A hp hpF hA hu₁mem
  have hv₁ : (t D : V ≃ₗ[F] V) v₁ ∈ blockSpace A D.1 := blockSpace_invariant A hp hpF hA hv₁mem
  have e1 : blockEnd A hp hpF hA t ht D u = (t D : V ≃ₗ[F] V) u₁ + u₂ := by
    rw [← hu, map_add, blockEnd_apply_mem A hp hpF hA t ht D hu₁mem,
      blockEnd_apply_of_ker A hp hpF hA t ht D hu₂]
  have e2 : blockEnd A hp hpF hA t ht D v = (t D : V ≃ₗ[F] V) v₁ + v₂ := by
    rw [← hv, map_add, blockEnd_apply_mem A hp hpF hA t ht D hv₁mem,
      blockEnd_apply_of_ker A hp hpF hA t ht D hv₂]
  rw [e1, e2, ← hu, ← hv]
  have hcross : ∀ (x y : V), x ∈ blockSpace A D.1 →
      y ∈ LinearMap.ker (projBlock A hp hpF hA D) → B x y = 0 :=
    fun x y hx hy => blockSpace_ker_sesq_orthogonal A hp hpF hA B hB D hx hy
  have hcross' : ∀ (x y : V), x ∈ LinearMap.ker (projBlock A hp hpF hA D) →
      y ∈ blockSpace A D.1 → B x y = 0 := by
    intro x y hx hy
    have h1 := projBlock_sesq A hp hpF hA B hB D x y
    rw [LinearMap.mem_ker.mp hx, projBlock_apply_of_mem A hp hpF hA D hy] at h1
    simpa using h1.symm
  have k1 : B ((t D : V ≃ₗ[F] V) u₁) v₂ = 0 := hcross _ _ hu₁ hv₂
  have k2 : B u₂ ((t D : V ≃ₗ[F] V) v₁) = 0 := hcross' _ _ hu₂ hv₁
  have k3 : B u₁ v₂ = 0 := hcross _ _ hu₁mem hv₂
  have k4 : B u₂ v₁ = 0 := hcross' _ _ hu₂ hv₁mem
  simp only [map_add, LinearMap.add_apply, k1, k2, k3, k4, hB (t D) u₁ v₁, add_zero,
    zero_add]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
