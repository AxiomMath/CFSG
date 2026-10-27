module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Ad
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUa
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls3Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Emb
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Hom

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open scoped MatrixGroups

section Std

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {A : GL (HypIndex 2 0) K}
  {E : Matrix (HypIndex 2 0) (Fin 4) K} {d : Fin 4 → h.fixedField}

theorem u4_cls3_proj_mem_fix {σ : K ≃+* K}
    {hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0}
    {α : MulAut (hypPSU h 2 0)}
    (hα : α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩)
    (hσ : ∀ c, σ c = h.bar c) (g : ↥(hypSU h 2 0))
    (hg : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
        ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) :
    hypProj h 2 0 g ∈ fixSub α := by
  rw [mem_fixSub, hα, semilinearAutHom_apply]
  congr 1
  apply Subtype.ext
  apply Units.ext
  have hmap : ((glAut σ (g : GL (HypIndex 2 0) K) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar := by
    rw [coe_glAut]
    congr 1
    funext c
    exact hσ c
  change ((A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
    ((glAut σ (g : GL (HypIndex 2 0) K) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) * ((A⁻¹ : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
    ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
  rw [hmap, hg, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem U4Frame.exists_homs [Finite K] (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1) (hp : p ≠ 2) :
    ∃ (YA YB : SL(2, h.fixedField) →* Matrix (Fin 3) (Fin 3) K)
      (ψA ψB : SL(2, h.fixedField) →* ↥(hypSU h 2 0)),
      AdFam (fun i : Fin 3 => ((d i.succ : h.fixedField) : K)) YA ∧
      AdFam (fun i : Fin 3 => ((d i.castSucc : h.fixedField) : K)) YB ∧
      (∀ S, ((ψA S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        E * eFirst (YA S) * U4Frame.fm h E d) ∧
      (∀ S, ((ψB S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        E * eLast (YB S) * U4Frame.fm h E d) ∧
      (∀ S, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((ψA S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
          ((ψA S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) ∧
      (∀ S, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((ψB S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
          ((ψB S : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
  have hodd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hp).pow
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp
  have hreal : ∀ (Y : SL(2, h.fixedField) →* Matrix (Fin 3) (Fin 3) K),
      (∀ S, ∃ M : Matrix (Fin 3) (Fin 3) h.fixedField, Y S = M.map h.fixedField.subtype) →
      ∀ S, (Y S).map h.bar = Y S := by
    intro Y hY S
    obtain ⟨M, hM⟩ := hY S
    rw [hM]
    ext i j
    simp only [Matrix.map_apply]
    exact h.mem_fixedField.mp (M i j).2
  obtain ⟨YA, hYA, hYAdet, hYAreal⟩ := exists_adFam_base h.fixedField.subtype hodd h2K
    (fun i : Fin 3 => d i.succ) (fun i => fr.ne _)
  obtain ⟨YB, hYB, hYBdet, hYBreal⟩ := exists_adFam_base h.fixedField.subtype hodd h2K
    (fun i : Fin 3 => d i.castSucc) (fun i => fr.ne _)
  obtain ⟨ψA, hψAf, hψAc⟩ := fr.exists_hom_of_emb hA hAA (emb := eFirst) eFirst_mul eFirst_one
    det_eFirst (eFirst_bar h.bar) (fun i : Fin 3 => ((d i.succ : h.fixedField) : K))
    (fun M hM => eFirst_iso (fun i => ((d i : h.fixedField) : K)) hM) YA (hreal YA hYAreal) hYAdet
    hYA.iso
  obtain ⟨ψB, hψBf, hψBc⟩ := fr.exists_hom_of_emb hA hAA (emb := eLast) eLast_mul eLast_one
    det_eLast (eLast_bar h.bar) (fun i : Fin 3 => ((d i.castSucc : h.fixedField) : K))
    (fun M hM => eLast_iso (fun i => ((d i : h.fixedField) : K)) hM) YB (hreal YB hYBreal) hYBdet
    hYB.iso
  exact ⟨YA, YB, ψA, ψB, hYA, hYB, hψAf, hψBf, hψAc, hψBc⟩

theorem u4_cls3_irred_frame [Finite K] (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1) (hp : p ≠ 2) {σ : K ≃+* K}
    {hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0}
    {α : MulAut (hypPSU h 2 0)}
    (hα : α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) (hσ : ∀ c, σ c = h.bar c)
    (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨YA, YB, ψA, ψB, hYA, hYB, hψAf, hψBf, hψAc, hψBc⟩ := fr.exists_homs hA hAA hp
  have hFE := fr.fm_mul_E
  have hEF := fr.E_mul_fm
  let W' : Submodule K (Fin 4 → K) := W.comap (Matrix.mulVecLin E)
  have hmem : ∀ w' : Fin 4 → K, w' ∈ W' ↔ E *ᵥ w' ∈ W := fun w' => Iff.rfl
  have hstabA : ∀ S, ∀ w' ∈ W', eFirst (YA S) *ᵥ w' ∈ W' := by
    intro S w' hw'
    rw [hmem] at hw' ⊢
    have h1 := hW (ψA S) (u4_cls3_proj_mem_fix hα hσ (ψA S) (hψAc S)) _ hw'
    rw [hψAf S, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hFE, Matrix.mul_one,
      ← Matrix.mulVec_mulVec] at h1
    exact h1
  have hstabB : ∀ S, ∀ w' ∈ W', eLast (YB S) *ᵥ w' ∈ W' := by
    intro S w' hw'
    rw [hmem] at hw' ⊢
    have h1 := hW (ψB S) (u4_cls3_proj_mem_fix hα hσ (ψB S) (hψBc S)) _ hw'
    rw [hψBf S, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hFE, Matrix.mul_one,
      ← Matrix.mulVec_mulVec] at h1
    exact h1
  have hW' := cls3_irred_of_dichotomy (hYA.dichotomyA W' hstabA) (hYB.dichotomyB W' hstabB)
  rcases hW' with h0 | h1
  · left
    rw [eq_bot_iff]
    intro w hw
    have h2 : U4Frame.fm h E d *ᵥ w ∈ W' := by
      rw [hmem, Matrix.mulVec_mulVec, hEF, Matrix.one_mulVec]
      exact hw
    rw [h0, Submodule.mem_bot] at h2
    have h3 : w = E *ᵥ (U4Frame.fm h E d *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, hEF, Matrix.one_mulVec]
    rw [Submodule.mem_bot, h3, h2, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have h2 : U4Frame.fm h E d *ᵥ v ∈ W' := by rw [h1]; exact Submodule.mem_top
    rw [hmem, Matrix.mulVec_mulVec, hEF, Matrix.one_mulVec] at h2
    exact h2

theorem frame_comm_transfer {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {E : Matrix ι κ K} {Fm : Matrix κ ι K} (hFE : Fm * E = 1) {X : Matrix ι ι K}
    {Y : Matrix κ κ K} (h : X * (E * Y * Fm) = (E * Y * Fm) * X) :
    (Fm * X * E) * Y = Y * (Fm * X * E) := by
  have h2 := congrArg (fun M => Fm * M * E) h
  have e1 : Fm * (X * (E * Y * Fm)) * E = (Fm * X * E) * Y := by
    calc Fm * (X * (E * Y * Fm)) * E = Fm * X * E * Y * (Fm * E) := by simp only [Matrix.mul_assoc]
      _ = (Fm * X * E) * Y := by rw [hFE, Matrix.mul_one]
  have e2 : Fm * ((E * Y * Fm) * X) * E = Y * (Fm * X * E) := by
    calc Fm * ((E * Y * Fm) * X) * E = (Fm * E) * Y * (Fm * X * E) := by simp only [Matrix.mul_assoc]
      _ = Y * (Fm * X * E) := by rw [hFE, Matrix.one_mul]
  rw [← e1, ← e2]
  exact h2

theorem mem_hypScalars_of_smul (x : ↥(hypSU h 2 0)) {c : K}
    (hx : ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = c • 1) :
    x ∈ hypScalars h 2 0 := by
  have hdet : c ^ 4 = 1 := by
    have h1 := (mem_hypSU.mp x.2).2
    rw [hx, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    simpa [HypIndex] using h1
  have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  have hU : (x : GL (HypIndex 2 0) K) ∈ hypUnitary h 2 0 :=
    mem_hypUnitary.mpr (mem_hypSU.mp x.2).1
  have hnorm : h.norm c = 1 :=
    CFSG.ComponentClassification.CatFactsL4U4.InvClassU.norm_eq_one_of_smul h (by norm_num) hU hx
  refine mem_normOneScalars.mpr ⟨Units.mk0 c hc0, hnorm, Units.ext (by simpa using hdet), ?_⟩
  apply Units.ext
  rw [hx, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem u4_cls3_cent_frame [Finite K] (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1) (hp : p ≠ 2) {σ : K ≃+* K}
    {hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0}
    {α : MulAut (hypPSU h 2 0)}
    (hα : α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) (hσ : ∀ c, σ c = h.bar c)
    (x : ↥(hypSU h 2 0))
    (hxc : ∀ ι : SL(2, h.fixedField) →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
      ∀ g, x * ι g = ι g * x) :
    x ∈ hypScalars h 2 0 := by
  obtain ⟨YA, YB, ψA, ψB, hYA, hYB, hψAf, hψBf, hψAc, hψBc⟩ := fr.exists_homs hA hAA hp
  have hFE := fr.fm_mul_E
  have hEF := fr.E_mul_fm
  set X : Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
    ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) with hX
  have hdne : ∀ i : Fin 3, ((d i.succ : h.fixedField) : K) ≠ 0 := fun i h0 =>
    fr.ne _ (Subtype.ext h0)
  have hdne' : ∀ i : Fin 3, ((d i.castSucc : h.fixedField) : K) ≠ 0 := fun i h0 =>
    fr.ne _ (Subtype.ext h0)
  have hcommA : ∀ S, (U4Frame.fm h E d * X * E) * eFirst (YA S) =
      eFirst (YA S) * (U4Frame.fm h E d * X * E) := by
    intro S
    have h1 := congrArg (fun g : ↥(hypSU h 2 0) => ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K))
      (hxc ψA (fun g => u4_cls3_proj_mem_fix hα hσ (ψA g) (hψAc g)) S)
    simp only [Subgroup.coe_mul, Units.val_mul] at h1
    rw [hψAf S] at h1
    exact frame_comm_transfer hFE h1
  have hcommB : ∀ S, (U4Frame.fm h E d * X * E) * eLast (YB S) =
      eLast (YB S) * (U4Frame.fm h E d * X * E) := by
    intro S
    have h1 := congrArg (fun g : ↥(hypSU h 2 0) => ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K))
      (hxc ψB (fun g => u4_cls3_proj_mem_fix hα hσ (ψB g) (hψBc g)) S)
    simp only [Subgroup.coe_mul, Units.val_mul] at h1
    rw [hψBf S] at h1
    exact frame_comm_transfer hFE h1
  obtain ⟨c, a11, a22, a33, a12, a13, a21, a23, a31, a32, a10, a20, a30, a01, a02, a03⟩ :=
    hYA.cent_A (fun i => hdne i) hcommA
  obtain ⟨c', b00, b11, -⟩ := hYB.cent_B (fun i => hdne' i) hcommB
  have hxm : U4Frame.fm h E d * X * E = Matrix.scalar (Fin 4) c :=
    cls3_scalar_of_entries a11 a22 a33 a12 a13 a21 a23 a31 a32 a10 a20 a30 a01 a02 a03 b00 b11
  have hXeq : X = c • 1 := by
    have h1 : X = E * (U4Frame.fm h E d * X * E) * U4Frame.fm h E d := by
      calc X = (E * U4Frame.fm h E d) * X * (E * U4Frame.fm h E d) := by
            rw [hEF, Matrix.one_mul, Matrix.mul_one]
        _ = E * (U4Frame.fm h E d * X * E) * U4Frame.fm h E d := by simp only [Matrix.mul_assoc]
    rw [h1, hxm, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hEF]
  exact mem_hypScalars_of_smul x hXeq

end Std

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
