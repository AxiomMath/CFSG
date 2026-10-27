module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Comps
public import CFSG.GH74.GLS.Stage2.Final.ModelLUData

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5 Matrix

namespace CFSG.GH74.Ivk413

theorem eq_of_forall_central_mul {G A : Type*} [Group G] [Group A] (hP : Group.IsPerfect G)
    (φ ψ : G →* A) (h : ∀ g, ∃ c ∈ Subgroup.center A, ψ g = c * φ g) : φ = ψ := by
  have hz : ∀ g, ψ g * (φ g)⁻¹ ∈ Subgroup.center A := by
    intro g
    obtain ⟨c, hc, hg⟩ := h g
    rw [hg, mul_assoc, mul_inv_cancel, mul_one]
    exact hc
  let θ : G →* Subgroup.center A :=
    { toFun := fun g => ⟨ψ g * (φ g)⁻¹, hz g⟩
      map_one' := by simp
      map_mul' := fun g₁ g₂ => by
        apply Subtype.ext
        show ψ (g₁ * g₂) * (φ (g₁ * g₂))⁻¹ = (ψ g₁ * (φ g₁)⁻¹) * (ψ g₂ * (φ g₂)⁻¹)
        have hc := Subgroup.mem_center_iff.1 (hz g₂)
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc ψ g₁ * ψ g₂ * ((φ g₂)⁻¹ * (φ g₁)⁻¹)
            = ψ g₁ * (ψ g₂ * (φ g₂)⁻¹) * (φ g₁)⁻¹ := by group
          _ = ψ g₁ * ((ψ g₂ * (φ g₂)⁻¹)) * (φ g₁)⁻¹ := rfl
          _ = ψ g₁ * (φ g₁)⁻¹ * (ψ g₂ * (φ g₂)⁻¹) := by
            rw [mul_assoc, ← hc ((φ g₁)⁻¹), ← mul_assoc]
          _ = _ := rfl }
  have hker : commutator G ≤ θ.ker := Abelianization.commutator_subset_ker θ
  have hθ : ∀ g, θ g = 1 := fun g => by
    have : g ∈ θ.ker := hker (by rw [hP.commutator_eq_top]; trivial)
    exact this
  ext g
  have h1 := hθ g
  have h2 : ψ g * (φ g)⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_one.1 h2).symm

variable {F : Type} [Field F] {M : ModelData F}

theorem scalar_mem_center (c : Fˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) ∈ Subgroup.center (GL (Fin 4) F) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

theorem conj_mem_K4 (C : GL (Fin 4) F) (hC : C ∈ M.U4) {g : GL (Fin 4) F} (hg : g ∈ M.K4) :
    C * g * C⁻¹ ∈ M.K4 := by
  rw [M.mem_K4] at hg ⊢
  refine ⟨M.U4.mul_mem (M.U4.mul_mem hC hg.1) (M.U4.inv_mem hC), ?_⟩
  have := Matrix.det_units_conj C (g : Matrix (Fin 4) (Fin 4) F)
  simpa [hg.2] using this

theorem conj_fixes_blkL [Finite F] (hG : GoodModel M) (B : GL (Fin 4) F)
    (β : MulAut (PG M))
    (hβ : ∀ g : ↥M.K4, ∃ hg : B * (g : GL (Fin 4) F) * B⁻¹ ∈ M.K4, β (mkP M g) = mkP M ⟨_, hg⟩)
    (hfix : ∀ g ∈ K1 M, β g = g) (a : ↥M.H2) : B * blkL F (a : GL (Fin 2) F) * B⁻¹ = blkL F a := by
  have hP : Group.IsPerfect ↥M.H2 := hG.qs.1
  let φ : ↥M.H2 →* GL (Fin 4) F := (blkL F).comp M.H2.subtype
  let ψ : ↥M.H2 →* GL (Fin 4) F := (MulAut.conj B).toMonoidHom.comp φ
  have key : ∀ a : ↥M.H2, ∃ c ∈ Subgroup.center (GL (Fin 4) F), ψ a = c * φ a := by
    intro a
    obtain ⟨hg, h1⟩ := hβ ⟨blkL F a, M.blkL_mem_K4 a.2⟩
    have h2 := hfix (iota1 M a) ⟨a, rfl⟩
    rw [iota1_apply] at h2
    rw [h1] at h2
    obtain ⟨c, hc⟩ := mkP_eq_iff.1 h2
    refine ⟨(Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (scalar_mem_center c)
    · show B * blkL F (a : GL (Fin 2) F) * B⁻¹ = _ * blkL F (a : GL (Fin 2) F)
      have e : blkL F (a : GL (Fin 2) F) =
          (B * blkL F (a : GL (Fin 2) F) * B⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 4) c :=
        inv_mul_eq_iff_eq_mul.1 hc
      have hcen := Subgroup.mem_center_iff.1 (scalar_mem_center (F := F) c)
      calc B * blkL F (a : GL (Fin 2) F) * B⁻¹
          = (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ *
              ((Matrix.GeneralLinearGroup.scalar (Fin 4) c) * (B * blkL F (a : GL (Fin 2) F) * B⁻¹)) := by
            group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ *
              ((B * blkL F (a : GL (Fin 2) F) * B⁻¹) * (Matrix.GeneralLinearGroup.scalar (Fin 4) c)) := by
            rw [hcen (B * blkL F (a : GL (Fin 2) F) * B⁻¹)]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ * blkL F (a : GL (Fin 2) F) := by rw [← e]
  have := eq_of_forall_central_mul hP φ ψ key
  exact (DFunLike.congr_fun this a).symm

theorem exists_block_of_centralizes [Finite F] (hG : GoodModel M) (B : GL (Fin 4) F)
    (hcomm : ∀ a : ↥M.H2, B * blkL F (a : GL (Fin 2) F) * B⁻¹ = blkL F a) :
    ∃ (l : Fˣ) (D : GL (Fin 2) F), B = diagGL (sc2 l) D := by
  have h2 := hG.two_ne_zero
  have hcomm' : ∀ a : ↥M.H2, B * blkL F (a : GL (Fin 2) F) = blkL F (a : GL (Fin 2) F) * B := fun a =>
    mul_inv_eq_iff_eq_mul.1 (hcomm a)
  have hy := hcomm' ⟨-1, M.neg_one_mem_H2⟩
  have hyM : ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 (-1) 1 := by
    rw [yGL, coe_diagGL]
    simp
  obtain ⟨A, D, hAD⟩ := exists_blk4_of_comm h2 (g := (B : Matrix (Fin 4) (Fin 4) F)) (by
    have h := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hy
    simp only [Units.val_mul] at h
    rw [show (((blkL F (-1 : GL (Fin 2) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blk4 (-1) 1
      from hyM] at h
    exact h)
  have hdet : (A.det * D.det) ≠ 0 := by
    rw [← det_blk4, ← hAD]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit |>.ne_zero
  have hA : A.det ≠ 0 := left_ne_zero_of_mul hdet
  have hD : D.det ≠ 0 := right_ne_zero_of_mul hdet
  let Ag : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
  let Dg : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero D hD
  have hB : B = diagGL Ag Dg := Units.ext (by rw [coe_diagGL]; exact hAD)
  obtain ⟨a₀, b₀, hab, hH⟩ := hG.quat
  have hAcomm : ∀ c, Ag * rhoQ hab c = rhoQ hab c * Ag := by
    intro c
    have h1 := hcomm' ⟨rhoQ hab c, hH c⟩
    rw [hB, blkL_apply, diagGL_mul, diagGL_mul] at h1
    have := (diagGL_inj h1).1
    simpa using this
  obtain ⟨l, hl⟩ := rhoQ_irr hab h2 Ag hAcomm
  exact ⟨l, Dg, by rw [hB, hl]⟩

theorem inner_step [Finite F] (hG : GoodModel M)
    (hdet : ∀ C ∈ M.U4, sc4 (Matrix.GeneralLinearGroup.det C) ∈ M.U4)
    (B : GL (Fin 4) F) (hB : B ∈ M.U4) (β : MulAut (PG M))
    (hβ : ∀ g : ↥M.K4, ∃ hg : B * (g : GL (Fin 4) F) * B⁻¹ ∈ M.K4, β (mkP M g) = mkP M ⟨_, hg⟩)
    {m : ℕ} (hm : Odd m) (hβm : β ^ m = 1) (hfix : ∀ g ∈ K1 M, β g = g) :
    ∃ k : PG M, β = MulAut.conj k := by
  have h2 := hG.two_ne_zero
  have hcomm := conj_fixes_blkL hG B β hβ hfix
  obtain ⟨l, D₀, hBdiag⟩ := exists_block_of_centralizes hG B hcomm
  have hBU := hB
  rw [hBdiag, M.diag_mem_iff] at hBU
  obtain ⟨hl, hD₀⟩ := hBU
  have hs4 : sc4 l ∈ M.U4 := by
    show Matrix.GeneralLinearGroup.scalar (Fin 4) l ∈ M.U4
    rw [scalar4_eq, M.diag_mem_iff]
    exact ⟨hl, hl⟩
  let D : GL (Fin 2) F := (sc2 l)⁻¹ * D₀
  let B' : GL (Fin 4) F := diagGL 1 D
  have hDU : D ∈ M.U2 := M.U2.mul_mem (M.U2.inv_mem hl) hD₀
  have hB'U : B' ∈ M.U4 := (M.diag_mem_iff _ _).2 ⟨M.U2.one_mem, hDU⟩
  have hBB' : B = sc4 l * B' := by
    show B = Matrix.GeneralLinearGroup.scalar (Fin 4) l * diagGL 1 D
    rw [scalar4_eq, diagGL_mul, hBdiag]
    simp [D]
  have hcen : ∀ (c : Fˣ) (X : GL (Fin 4) F), sc4 c * X = X * sc4 c := fun c X =>
    (scalar_comm c X).symm
  have hconj : ∀ g : GL (Fin 4) F, B * g * B⁻¹ = B' * g * B'⁻¹ := by
    intro g
    rw [hBB', _root_.mul_inv_rev]
    calc sc4 l * B' * g * (B'⁻¹ * (sc4 l)⁻¹)
        = sc4 l * (B' * g * B'⁻¹) * (sc4 l)⁻¹ := by group
      _ = (B' * g * B'⁻¹) * sc4 l * (sc4 l)⁻¹ := by rw [hcen]
      _ = B' * g * B'⁻¹ := by group
  have hβ' : ∀ g : ↥M.K4, ∃ hg : B' * (g : GL (Fin 4) F) * B'⁻¹ ∈ M.K4,
      β (mkP M g) = mkP M ⟨_, hg⟩ := by
    intro g
    obtain ⟨hg, h⟩ := hβ g
    refine ⟨conj_mem_K4 B' hB'U g.2, ?_⟩
    rw [h]
    congr 1
    exact Subtype.ext (hconj g)
  have hpow : ∀ k : ℕ, ∀ g : ↥M.K4, ∃ hg : B' ^ k * (g : GL (Fin 4) F) * (B' ^ k)⁻¹ ∈ M.K4,
      (β ^ k) (mkP M g) = mkP M ⟨_, hg⟩ := by
    intro k
    induction k with
    | zero =>
      intro g
      refine ⟨by simp, ?_⟩
      have : (⟨B' ^ 0 * (g : GL (Fin 4) F) * (B' ^ 0)⁻¹, by simp⟩ : ↥M.K4) = g :=
        Subtype.ext (by simp)
      rw [this]
      rfl
    | succ k ih =>
      intro g
      obtain ⟨hg, h⟩ := ih g
      obtain ⟨hg2, h2'⟩ := hβ' ⟨B' ^ k * (g : GL (Fin 4) F) * (B' ^ k)⁻¹, hg⟩
      have hmem : B' ^ (k + 1) * (g : GL (Fin 4) F) * (B' ^ (k + 1))⁻¹ ∈ M.K4 :=
        conj_mem_K4 _ (M.U4.pow_mem hB'U _) g.2
      refine ⟨hmem, ?_⟩
      rw [pow_succ', MulAut.mul_apply, h, h2']
      congr 1
      apply Subtype.ext
      have e : B' * (B' ^ k * (g : GL (Fin 4) F) * (B' ^ k)⁻¹) * B'⁻¹ =
          B' ^ (k + 1) * (g : GL (Fin 4) F) * (B' ^ (k + 1))⁻¹ := by
        rw [pow_succ', _root_.mul_inv_rev]
        group
      exact e
  have hdiagpow : ∀ k : ℕ, B' ^ k = diagGL 1 (D ^ k) := by
    intro k
    induction k with
    | zero => simp [diagGL_one]
    | succ k ih => rw [pow_succ, ih, show B' = diagGL 1 D from rfl, diagGL_mul, pow_succ, one_mul]
  set E : GL (Fin 2) F := D ^ m with hE
  obtain ⟨hgw, hw⟩ := hpow m ⟨(swapGL F), M.swapGL_mem_K4⟩
  rw [hβm, MulAut.one_apply] at hw
  obtain ⟨c, hc⟩ := mkP_eq_iff.1 hw.symm
  have hX : diagGL 1 E * swapGL F * (diagGL 1 E)⁻¹ = diagGL E⁻¹ E * swapGL F := by
    have h1 := swapGL_mul_diagGL_mul_inv (1 : GL (Fin 2) F) E⁻¹
    have h2' : swapGL F * diagGL 1 E⁻¹ = diagGL E⁻¹ 1 * swapGL F := by
      have := congrArg (· * swapGL F) h1
      simpa [mul_assoc, swapGL_inv, swapGL_mul_self] using this
    rw [diagGL_inv, inv_one, mul_assoc, h2', ← mul_assoc, diagGL_mul]
    simp
  have hEc : diagGL E⁻¹ E = Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
    have h3 : (B' ^ m) * swapGL F * (B' ^ m)⁻¹ = diagGL E⁻¹ E * swapGL F := by
      rw [hdiagpow m]; exact hX
    have h4 : ((B' ^ m * (swapGL F) * (B' ^ m)⁻¹ : GL (Fin 4) F))⁻¹ * swapGL F =
        Matrix.GeneralLinearGroup.scalar (Fin 4) c := hc
    rw [h3, _root_.mul_inv_rev, mul_assoc] at h4
    have h5 := swapGL_mul_diagGL_mul_inv E E⁻¹
    rw [diagGL_inv, inv_inv] at h4
    rw [swapGL_inv] at h4 h5
    rw [← mul_assoc] at h4
    exact h5.symm.trans h4
  obtain ⟨hEc1, hEc2⟩ := diagGL_inj (hEc.trans (scalar4_eq c))
  have hEsc : E = sc2 c := hEc2
  have hEinv : E⁻¹ = sc2 c := hEc1
  have hEeq : E = E⁻¹ := hEsc.trans hEinv.symm
  have hEE : E * E = 1 := by
    have h1 : E * E⁻¹ = 1 := mul_inv_cancel E
    rwa [← hEeq] at h1
  have hcc : c * c = 1 := by
    rw [hEsc, sc2_mul] at hEE
    exact sc2_inj (hEE.trans sc2_one.symm)
  have hdetE : ((E : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [hEsc, det_sc2, sq]
    have := congrArg (fun u : Fˣ => (u : F)) hcc
    simpa using this
  let δ : Fˣ := Matrix.GeneralLinearGroup.det B'
  have hδval : (δ : F) = ((B' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det :=
    Matrix.GeneralLinearGroup.val_det_apply B'
  have hδm : δ ^ m = 1 := by
    apply Units.ext
    have h1 : ((B' ^ m : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      rw [hdiagpow m, coe_diagGL, det_blk4]
      have hE' : (((D ^ m : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
        hdetE
      rw [hE']
      simp
    rw [Units.val_pow_eq_pow_val, hδval, ← Matrix.det_pow, ← Units.val_pow_eq_pow_val]
    simpa using h1
  obtain ⟨j, hj⟩ := hm
  let ν : Fˣ := δ ^ (j + 1) ^ 2
  have hν : ν ^ 4 = δ := by
    have e : 4 * (j + 1) ^ 2 = (2 * j + 1) * (2 * j + 3) + 1 := by ring
    calc ν ^ 4 = δ ^ ((j + 1) ^ 2 * 4) := by rw [← pow_mul]
      _ = δ ^ ((2 * j + 1) * (2 * j + 3) + 1) := by rw [mul_comm, e]
      _ = δ := by rw [pow_succ, pow_mul, ← hj, hδm, one_pow, one_mul]
  have hsν : sc4 ν ∈ M.U4 := by
    have := M.U4.pow_mem (hdet B' hB'U) ((j + 1) ^ 2)
    simpa [ν, map_pow] using this
  let B'' : GL (Fin 4) F := sc4 ν⁻¹ * B'
  have hB''U : B'' ∈ M.U4 :=
    M.U4.mul_mem (by rw [map_inv]; exact M.U4.inv_mem hsν) hB'U
  have hB''det : ((B'' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    show ((sc4 ν⁻¹ * B' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1
    rw [Units.val_mul, Matrix.det_mul, det_sc4, ← hδval]
    have : ((ν : F)) ^ 4 = (δ : F) := by
      have := congrArg (fun u : Fˣ => (u : F)) hν
      simpa using this
    rw [Units.val_inv_eq_inv_val, inv_pow, this]
    exact inv_mul_cancel₀ (δ.ne_zero)
  have hB''K : B'' ∈ M.K4 := (M.mem_K4 _).2 ⟨hB''U, hB''det⟩
  have hB'B'' : B' = sc4 ν * B'' := by
    show B' = sc4 ν * (sc4 ν⁻¹ * B')
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨mkP M ⟨B'', hB''K⟩, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Zs M) x
  obtain ⟨hg, h⟩ := hβ' g
  rw [h, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  show B' * (g : GL (Fin 4) F) * B'⁻¹ = B'' * (g : GL (Fin 4) F) * B''⁻¹
  rw [hB'B'', _root_.mul_inv_rev]
  calc sc4 ν * B'' * (g : GL (Fin 4) F) * (B''⁻¹ * (sc4 ν)⁻¹)
      = sc4 ν * (B'' * (g : GL (Fin 4) F) * B''⁻¹) * (sc4 ν)⁻¹ := by group
    _ = (B'' * (g : GL (Fin 4) F) * B''⁻¹) * sc4 ν * (sc4 ν)⁻¹ := by rw [hcen]
    _ = B'' * (g : GL (Fin 4) F) * B''⁻¹ := by group

end CFSG.GH74.Ivk413
