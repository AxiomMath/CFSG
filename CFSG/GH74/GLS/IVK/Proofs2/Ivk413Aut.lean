module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Inner
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Clauses
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5 Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

namespace CFSG.GH74.Ivk413

variable {F : Type} [Field F] {M : ModelData F}

theorem semiconj_fixes_blkL [Finite F] (hG : GoodModel M) (B : GL (Fin 4) F) (φ : F ≃+* F)
    (β : MulAut (PG M))
    (hβ : ∀ g : ↥M.K4, ∃ hg : B * glAut φ (g : GL (Fin 4) F) * B⁻¹ ∈ M.K4,
      β (mkP M g) = mkP M ⟨_, hg⟩)
    (hfix : ∀ g ∈ K1 M, β g = g) (a : ↥M.H2) :
    B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹ = blkL F a := by
  have hP : Group.IsPerfect ↥M.H2 := hG.qs.1
  let φ₁ : ↥M.H2 →* GL (Fin 4) F := (blkL F).comp M.H2.subtype
  let ψ : ↥M.H2 →* GL (Fin 4) F :=
    ((MulAut.conj B).toMonoidHom.comp (glAut φ).toMonoidHom).comp φ₁
  have key : ∀ a : ↥M.H2, ∃ c ∈ Subgroup.center (GL (Fin 4) F), ψ a = c * φ₁ a := by
    intro a
    obtain ⟨hg, h1⟩ := hβ ⟨blkL F a, M.blkL_mem_K4 a.2⟩
    have h2 := hfix (iota1 M a) ⟨a, rfl⟩
    rw [iota1_apply] at h2
    rw [h1] at h2
    obtain ⟨c, hc⟩ := mkP_eq_iff.1 h2
    refine ⟨(Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (scalar_mem_center c)
    · show B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹ = _ * blkL F (a : GL (Fin 2) F)
      have e : blkL F (a : GL (Fin 2) F) =
          (B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin 4) c :=
        inv_mul_eq_iff_eq_mul.1 hc
      have hcen := Subgroup.mem_center_iff.1 (scalar_mem_center (F := F) c)
      calc B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹
          = (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ *
              ((Matrix.GeneralLinearGroup.scalar (Fin 4) c) *
                (B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹)) := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ *
              ((B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹) *
                (Matrix.GeneralLinearGroup.scalar (Fin 4) c)) := by
            rw [hcen (B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹)]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ * blkL F (a : GL (Fin 2) F) := by
            rw [← e]
  have := eq_of_forall_central_mul hP φ₁ ψ key
  exact (DFunLike.congr_fun this a).symm

theorem trace_blk4 (X Y : Matrix (Fin 2) (Fin 2) F) : (blk4 X Y).trace = X.trace + Y.trace := by
  have h : (blk4 X Y).trace = (fromBlocks X 0 0 Y).trace := by
    have := Equiv.sum_comp (finSumFinEquiv (m := 2) (n := 2)) (fun i => (blk4 X Y) i i)
    simp only [Matrix.trace, Matrix.diag]
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    simp [blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock, reindex_apply]
  rw [h]
  simp [Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem trace_blkL (a : GL (Fin 2) F) :
    ((blkL F a : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace =
      ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace + 2 := by
  rw [blkL_apply, coe_diagGL, trace_blk4]
  have : ((1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 2 := by
    simp [Matrix.trace]
  rw [this]

theorem trace_glAut (φ : F ≃+* F) (g : GL (Fin 4) F) :
    ((glAut φ g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace =
      φ ((g : Matrix (Fin 4) (Fin 4) F).trace) := by
  rw [coe_glAut]
  simp [Matrix.trace, map_sum]

theorem phi_fixes_trace (B : GL (Fin 4) F) (φ : F ≃+* F) (a : GL (Fin 2) F)
    (h : B * glAut φ (blkL F a) * B⁻¹ = blkL F a) :
    φ (((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace) =
      ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  have h1 := congrArg (fun u : GL (Fin 4) F => ((u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).trace) h
  simp only [Units.val_mul] at h1
  rw [Matrix.trace_units_conj, trace_glAut] at h1
  simp only [trace_blkL, map_add, map_ofNat] at h1
  exact add_right_cancel h1

@[expose] def SemiRep (M : ModelData F) : Prop :=
  ∀ β : MulAut (PG M), Odd (orderOf β) →
    ∃ (B : GL (Fin 4) F) (φ : F ≃+* F), B ∈ M.U4 ∧
      ∀ g : ↥M.K4, ∃ hg : B * glAut φ (g : GL (Fin 4) F) * B⁻¹ ∈ M.K4,
        β (mkP M g) = mkP M ⟨_, hg⟩

theorem autInner_of_semiRep [Finite F] (hG : GoodModel M) (hSR : SemiRep M)
    (hdet : ∀ C ∈ M.U4, sc4 (Matrix.GeneralLinearGroup.det C) ∈ M.U4)
    (hphiU : ∀ (φ : F ≃+* F) (C : GL (Fin 4) F), C ∈ M.U4 → glAut φ C ∈ M.U4)
    (hphi : ∀ φ : F ≃+* F, (∀ a ∈ M.H2,
      φ ((a : Matrix (Fin 2) (Fin 2) F).trace) = (a : Matrix (Fin 2) (Fin 2) F).trace) →
        ∀ x, φ (φ x) = x) :
    AutInner M := by
  intro β hodd hfix
  obtain ⟨B, φ, hBU, hrep⟩ := hSR β hodd
  have hcomm : ∀ a : ↥M.H2, B * glAut φ (blkL F (a : GL (Fin 2) F)) * B⁻¹ = blkL F a :=
    semiconj_fixes_blkL hG B φ β hrep hfix
  have hφtr : ∀ a ∈ M.H2, φ ((a : Matrix (Fin 2) (Fin 2) F).trace) =
      (a : Matrix (Fin 2) (Fin 2) F).trace := fun a ha => phi_fixes_trace B φ a (hcomm ⟨a, ha⟩)
  have hφ2 : ∀ x, φ (φ x) = x := hphi φ hφtr
  have hgl2 : ∀ g : GL (Fin 4) F, glAut φ (glAut φ g) = g := by
    intro g
    apply Units.ext
    rw [coe_glAut, coe_glAut]
    ext i j
    simp [hφ2]
  let B₂ : GL (Fin 4) F := B * glAut φ B
  have hB₂U : B₂ ∈ M.U4 := M.U4.mul_mem hBU (hphiU φ B hBU)
  let β₂ : MulAut (PG M) := β * β
  have hβ₂ : ∀ g : ↥M.K4, ∃ hg : B₂ * (g : GL (Fin 4) F) * B₂⁻¹ ∈ M.K4,
      β₂ (mkP M g) = mkP M ⟨_, hg⟩ := by
    intro g
    obtain ⟨hg1, h1⟩ := hrep g
    obtain ⟨hg2, h2⟩ := hrep ⟨B * glAut φ (g : GL (Fin 4) F) * B⁻¹, hg1⟩
    refine ⟨conj_mem_K4 B₂ hB₂U g.2, ?_⟩
    show β (β (mkP M g)) = _
    rw [h1, h2]
    congr 1
    apply Subtype.ext
    show B * glAut φ (B * glAut φ (g : GL (Fin 4) F) * B⁻¹) * B⁻¹ =
      (B * glAut φ B) * (g : GL (Fin 4) F) * (B * glAut φ B)⁻¹
    simp only [map_mul, map_inv, hgl2, _root_.mul_inv_rev]
    group
  have hfix₂ : ∀ g ∈ K1 M, β₂ g = g := fun g hg => by
    show β (β g) = g
    rw [hfix g hg, hfix g hg]
  have hβm : β ^ orderOf β = 1 := pow_orderOf_eq_one β
  have hβ₂m : β₂ ^ orderOf β = 1 := by
    show (β * β) ^ orderOf β = 1
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hβm, one_pow]
  obtain ⟨k, hk⟩ := inner_step hG hdet B₂ hB₂U β₂ hβ₂ hodd hβ₂m hfix₂
  obtain ⟨j, hj⟩ := hodd
  refine ⟨k ^ (j + 1), ?_⟩
  have hbeta : β = β₂ ^ (j + 1) := by
    have : β₂ ^ (j + 1) = β ^ (2 * j + 1) * β := by
      show (β * β) ^ (j + 1) = _
      rw [← sq, ← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ]
    rw [this, ← hj, hβm, one_mul]
  rw [hbeta, hk, map_pow]

end CFSG.GH74.Ivk413
