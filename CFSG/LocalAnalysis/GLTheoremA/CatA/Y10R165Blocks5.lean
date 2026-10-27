module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks4

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)
open scoped DirectSum CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
variable {p : ℕ}

theorem projBlock_bilinear (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (B : V →ₗ[F] V →ₗ[F] F) (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
    (D : Hyperplane A p) (u v : V) :
    B (projBlock A hp hpF hA D u) v = B u (projBlock A hp hpF hA D v) := by
  have hsum : ∀ H : Subgroup ↥A,
      B (sumOp (actionEnd A) H u) v = B u (sumOp (actionEnd A) H v) :=
    fun H => sumOp_adjoint (actionEnd A) B (fun g _ _ => hB g _ _) H u v
  simp only [projBlock, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hsum]

theorem blockSpace_bilinear_orthogonal (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (B : V →ₗ[F] V →ₗ[F] F) (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
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
  exact HyperBlocks.block_orthogonal (ρ := actionEnd A) (natCast_card_top_ne_zero A hp hpF hA) B
    (fun g _ _ => hB g _ _) hcomm le_top le_top hgen
    (natCast_card_subgroup_ne_zero' A hp hpF hA D.1) hu hv

theorem blockSpace_ker_orthogonal (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (B : V →ₗ[F] V →ₗ[F] F) (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
    (D : Hyperplane A p) {u v : V} (hu : u ∈ blockSpace A D.1)
    (hv : v ∈ LinearMap.ker (projBlock A hp hpF hA D)) : B u v = 0 := by
  have h1 := projBlock_bilinear A hp hpF hA B hB D u v
  rw [projBlock_apply_of_mem A hp hpF hA D hu, LinearMap.mem_ker.mp hv, map_zero] at h1
  exact h1

theorem blockEnd_bilinear (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (B : V →ₗ[F] V →ₗ[F] F) (hB : ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v)
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
    fun x y hx hy => blockSpace_ker_orthogonal A hp hpF hA B hB D hx hy
  have hcross' : ∀ (x y : V), x ∈ LinearMap.ker (projBlock A hp hpF hA D) →
      y ∈ blockSpace A D.1 → B x y = 0 := by
    intro x y hx hy
    have h1 := projBlock_bilinear A hp hpF hA B hB D x y
    rw [LinearMap.mem_ker.mp hx, projBlock_apply_of_mem A hp hpF hA D hy] at h1
    simpa using h1.symm
  have k1 : B ((t D : V ≃ₗ[F] V) u₁) v₂ = 0 := hcross _ _ hu₁ hv₂
  have k2 : B u₂ ((t D : V ≃ₗ[F] V) v₁) = 0 := hcross' _ _ hu₂ hv₁
  have k3 : B u₁ v₂ = 0 := hcross _ _ hu₁mem hv₂
  have k4 : B u₂ v₁ = 0 := hcross' _ _ hu₂ hv₁mem
  simp only [map_add, LinearMap.add_apply, k1, k2, k3, k4, hB (t D) u₁ v₁, add_zero,
    zero_add]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

