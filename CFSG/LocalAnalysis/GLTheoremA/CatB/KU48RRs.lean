module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KU48RRoot

public section

noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8 (Xs Rs act dotB mem_Rs act_sub_mem_Xs)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem Fv_add' (φ : KF ≃+* KF) (u v : Fin 4 → KF) : Fv φ (u + v) = Fv φ u + Fv φ v := by
  ext i
  simp [Fv]

theorem Fv_sub' (φ : KF ≃+* KF) (u v : Fin 4 → KF) : Fv φ (u - v) = Fv φ u - Fv φ v := by
  ext i
  simp [Fv]

theorem Fv_smul' (φ : KF ≃+* KF) (c : KF) (w : Fin 4 → KF) : Fv φ (c • w) = φ c • Fv φ w := by
  ext i
  simp [Fv]

theorem Fv_zero' (φ : KF ≃+* KF) : Fv φ 0 = 0 := by
  ext i
  simp [Fv]

theorem sF_add (g : SU4) (φ : KF ≃+* KF) (u v : Fin 4 → KF) :
    sF g φ (u + v) = sF g φ u + sF g φ v := by
  unfold sF
  rw [Fv_add', Matrix.mulVec_add]

theorem sF_sub (g : SU4) (φ : KF ≃+* KF) (u v : Fin 4 → KF) :
    sF g φ (u - v) = sF g φ u - sF g φ v := by
  unfold sF
  rw [Fv_sub', Matrix.mulVec_sub]

theorem sF_smul (g : SU4) (φ : KF ≃+* KF) (c : KF) (w : Fin 4 → KF) :
    sF g φ (c • w) = φ c • sF g φ w := by
  unfold sF
  rw [Fv_smul', Matrix.mulVec_smul]

theorem sF_zero (g : SU4) (φ : KF ≃+* KF) : sF g φ 0 = 0 := by
  unfold sF
  rw [Fv_zero', Matrix.mulVec_zero]

theorem mapMulVec_Fv (φ : KF ≃+* KF) (M : Matrix (Fin 4) (Fin 4) KF) (u : Fin 4 → KF) :
    M.map φ *ᵥ Fv φ u = Fv φ (M *ᵥ u) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fv, map_sum, map_mul]

theorem act_sF (g : SU4) (φ : KF ≃+* KF) (t : GL (Fin 4) KF) (u : Fin 4 → KF) :
    act ((g : GL (Fin 4) KF) * glAut φ t * (g : GL (Fin 4) KF)⁻¹) (sF g φ u) = sF g φ (act t u) := by
  have hinv : (((g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
      ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) = 1 := Units.inv_mul _
  unfold act sF
  rw [Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, coe_glAut]
  have key : ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
      ((t : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF).map φ *
      (((g : GL (Fin 4) KF)⁻¹ : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
      ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) =
      ((g : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF) *
      ((t : GL (Fin 4) KF) : Matrix (Fin 4) (Fin 4) KF).map φ := by
    simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [key, ← Matrix.mulVec_mulVec, mapMulVec_Fv]

theorem sF_mem_Xs (g : SU4) (φ : KF ≃+* KF) (W : Subgroup (GL (Fin 4) KF))
    (hW2 : ∀ t ∈ W, (g : GL (Fin 4) KF) * glAut φ t * (g : GL (Fin 4) KF)⁻¹ ∈ W) :
    ∀ v ∈ Xs W, sF g φ v ∈ Xs W := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, u, rfl⟩ := hx
    have h1 : sF g φ (act t u - u) =
        act ((g : GL (Fin 4) KF) * glAut φ t * (g : GL (Fin 4) KF)⁻¹) (sF g φ u) - sF g φ u := by
      rw [act_sF, sF_sub]
    rw [h1]
    exact act_sub_mem_Xs (hW2 t ht) (sF g φ u)
  | zero => rw [sF_zero]; exact (Xs W).zero_mem
  | add x y _ _ hx hy => rw [sF_add]; exact (Xs W).add_mem hx hy
  | smul c x _ hx => rw [sF_smul]; exact (Xs W).smul_mem _ hx

theorem sF_mem_Rs (g : SU4) (φ : KF ≃+* KF) (W : Subgroup (GL (Fin 4) KF))
    (hW1 : ∀ t ∈ W, ∃ t' ∈ W, (g : GL (Fin 4) KF) * glAut φ t' * (g : GL (Fin 4) KF)⁻¹ = t)
    (hW2 : ∀ t ∈ W, (g : GL (Fin 4) KF) * glAut φ t * (g : GL (Fin 4) KF)⁻¹ ∈ W)
    {x : Fin 4 → KF} (hx : x ∈ Rs W) : sF g φ x ∈ Rs W := by
  rw [mem_Rs] at hx ⊢
  refine ⟨sF_mem_Xs g φ W hW2 x hx.1, fun t ht => ?_⟩
  obtain ⟨t', ht', rfl⟩ := hW1 t ht
  rw [act_sF, hx.2 t' ht']

theorem finrank_le_two_of_isotropic (R : Submodule KF (Fin 4 → KF))
    (hR : ∀ x ∈ R, ∀ y ∈ R, dotB hKF x y = 0) : Module.finrank KF R ≤ 2 := by
  set d := Module.finrank KF R with hd
  let b := Module.finBasis KF R
  let v : Fin d → (Fin 4 → KF) := fun j => (b j : Fin 4 → KF)
  have hv : LinearIndependent KF v := by
    have h := b.linearIndependent.map' R.subtype (LinearMap.ker_eq_bot.2 R.injective_subtype)
    exact h
  let M : Matrix (Fin d) (Fin 4) KF := fun j i => hKF.bar (v j i)
  have hΨ : Function.Injective (Matrix.mulVecLin Mᵀ) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
    rw [Submodule.mem_bot]
    have hsum : ∑ j, hKF.bar (c j) • v j = 0 := by
      funext i
      have hi : ∑ j, M j i * c j = 0 := by
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
      have h2 := congrArg hKF.bar hi
      simp only [map_sum, map_mul, hKF.bar_bar, map_zero, M] at h2
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h2
    funext j
    have := Fintype.linearIndependent_iff.1 hv (fun j => hKF.bar (c j)) hsum j
    have h3 : c j = 0 := by
      have h4 : hKF.bar (c j) = 0 := this
      rw [bar_pow] at h4
      simpa using h4
    simpa using h3
  have hrank : Matrix.rank Mᵀ = d := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hΨ, Module.finrank_fin_fun]
  have hM : Matrix.rank M = d := by
    rw [← Matrix.rank_transpose]
    exact hrank
  let Φ := Matrix.mulVecLin M
  have hR_ker : R ≤ LinearMap.ker Φ := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext j
    have := hR (v j) (b j).2 y hy
    simpa [Matrix.mulVec, dotProduct, M, dotB, v, mul_comm] using this
  have h1 := Submodule.finrank_mono hR_ker
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  have h3 : Module.finrank KF (LinearMap.range Φ) = d := hM
  rw [Module.finrank_fin_fun, h3] at h2
  omega

end CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R
