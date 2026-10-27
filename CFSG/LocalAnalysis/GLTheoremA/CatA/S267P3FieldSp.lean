module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldSL
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.RankThree.PartTwo.KFacts.AutPSpFaithful

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin
open CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form

variable {K : Type} [Field K]

@[expose] def ω2 : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem transpose_mul_ω2_mul (P : Matrix (Fin 2) (Fin 2) K) : Pᵀ * ω2 * P = P.det • ω2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ω2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

@[expose] def spGram : Matrix (Kap (Fin 0)) (Kap (Fin 0)) K :=
  fromBlocks ω2 0 0 (fromBlocks ω2 0 0 0)

@[expose] def spTop : Subgroup (SpecialLinearGroup (Kap (Fin 0)) K) :=
  (CFSG.Open.StatedAPI.gramIsometry (spGram (K := K))).comap Matrix.SpecialLinearGroup.toGL

theorem mem_spTop {g : SpecialLinearGroup (Kap (Fin 0)) K} :
    g ∈ spTop ↔ (g : Matrix (Kap (Fin 0)) (Kap (Fin 0)) K)ᵀ * spGram *
      (g : Matrix (Kap (Fin 0)) (Kap (Fin 0)) K) = spGram := Iff.rfl

theorem map_spGram (σ : K ≃+* K) : (spGram (K := K)).map σ = spGram := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    first | exact i.elim0 | exact j.elim0 | (fin_cases i <;> fin_cases j <;> simp [spGram, ω2])

theorem transpose_mul_ω2_mul' (Y : SpecialLinearGroup (Lam (Fin 0)) K) :
    (Y : Matrix (Lam (Fin 0)) (Lam (Fin 0)) K)ᵀ * fromBlocks ω2 0 0 0 *
      (Y : Matrix (Lam (Fin 0)) (Lam (Fin 0)) K) =
      fromBlocks ω2 (0 : Matrix (Fin 2) (Fin 0) K) 0 0 := by
  set M := (Y : Matrix (Lam (Fin 0)) (Lam (Fin 0)) K) with hM
  have h12 : M.toBlocks₁₂ = 0 := Matrix.ext fun _ j => j.elim0
  have h21 : M.toBlocks₂₁ = 0 := Matrix.ext fun i _ => i.elim0
  have hdet : M.toBlocks₁₁.det = 1 := by
    have h : M.det = 1 := Y.2
    rw [← fromBlocks_toBlocks M, h12, h21, det_fromBlocks_zero₂₁] at h
    have h22 : M.toBlocks₂₂.det = 1 := Matrix.det_isEmpty
    rwa [h22, mul_one] at h
  rw [← fromBlocks_toBlocks M, h12, h21, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, transpose_zero]
  rw [transpose_mul_ω2_mul, hdet, one_smul]

theorem blk_mem_spTop (P : SpecialLinearGroup (Fin 2) K) (Y : SpecialLinearGroup (Lam (Fin 0)) K) :
    blk (Lam (Fin 0)) (P, Y) ∈ spTop := by
  rw [mem_spTop, coe_blk, spGram, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, transpose_zero]
  rw [transpose_mul_ω2_mul, P.2, one_smul, transpose_mul_ω2_mul' Y]

theorem map_mem_spTop (σ : K ≃+* K) {g : SpecialLinearGroup (Kap (Fin 0)) K} (hg : g ∈ spTop) :
    Matrix.SpecialLinearGroup.map (σ : K →+* K) g ∈ spTop := by
  rw [mem_spTop] at hg ⊢
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ← map_spGram σ,
    ← Matrix.transpose_map]
  change ((g : Matrix _ _ K)ᵀ).map σ * spGram.map σ * (g : Matrix _ _ K).map σ = spGram.map σ
  rw [← Matrix.map_mul, ← Matrix.map_mul, hg]

@[expose] noncomputable def spData (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (x : K) (hx : σ x ≠ x) :
    FieldData K (Fin 0) where
  G2 := ⊤
  Gl := ⊤
  Gt := spTop
  blk_top P _ Y _ := blk_mem_spTop P Y
  blk_lam _ _ := Subgroup.mem_top _
  top_inv _ _ := Subgroup.mem_top _
  c := c3
  c_mem := Subgroup.mem_top _
  c_rel := by rw [coe_c3]; exact c3Mat_rel
  c_ne := by rw [coe_c3]; simp [c3Mat]
  x := x
  w := dg x (ne_zero_and_sq_ne_one hx).1
  w_mem := Subgroup.mem_top _
  coe_w := rfl
  x_sq := (ne_zero_and_sq_ne_one hx).2
  negOne_mem := Subgroup.mem_top _
  σ := σ
  σ_cube := hσ3
  σ_x := hx
  map_Gt _ hg := map_mem_spTop σ hg
  map_c := map_c3 _

@[expose] def spIdx : Kap (Fin 0) ≃ Fin 2 ⊕ Fin 2 where
  toFun
    | Sum.inl i => if i = 0 then Sum.inl 0 else Sum.inr 0
    | Sum.inr (Sum.inl i) => if i = 0 then Sum.inl 1 else Sum.inr 1
    | Sum.inr (Sum.inr k) => k.elim0
  invFun
    | Sum.inl i => if i = 0 then Sum.inl 0 else Sum.inr (Sum.inl 0)
    | Sum.inr i => if i = 0 then Sum.inl 1 else Sum.inr (Sum.inl 1)
  left_inv a := by
    rcases a with i | i | k
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · exact k.elim0
  right_inv a := by
    rcases a with i | i <;> fin_cases i <;> rfl

theorem reindex_spGram :
    reindex spIdx spIdx (spGram (K := K)) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spIdx, spGram, ω2, Matrix.one_apply]

theorem reindex_mul_sp (A B : Matrix (Kap (Fin 0)) (Kap (Fin 0)) K) :
    reindex spIdx spIdx (A * B) = reindex spIdx spIdx A * reindex spIdx spIdx B := by
  simp only [reindex_apply, submatrix_mul_equiv]

@[expose] noncomputable def spGL : SpecialLinearGroup (Kap (Fin 0)) K →* GL (Fin 2 ⊕ Fin 2) K :=
  Matrix.SpecialLinearGroup.toGL.comp
    (CFSG.RankThree.PartTwo.Census.slReindex K spIdx).toMonoidHom

theorem coe_spGL (g : SpecialLinearGroup (Kap (Fin 0)) K) :
    ((spGL g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      reindex spIdx spIdx (g : Matrix (Kap (Fin 0)) (Kap (Fin 0)) K) := rfl

theorem det_of_mem_statedSp_two {A : GL (Fin 2 ⊕ Fin 2) K} (hA : A ∈ StatedSp 2 K) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det = 1 :=
  SymplecticGroup.det_eq_one (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp
    ((CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := K)).le hA))

theorem spGL_injective : Function.Injective (spGL (K := K)) := fun a b h => by
  have h' := congrArg (fun A : GL (Fin 2 ⊕ Fin 2) K =>
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_spGL] at h'
  exact Subtype.ext ((reindex spIdx spIdx).injective h')

theorem mem_spTop_iff_spGL {g : SpecialLinearGroup (Kap (Fin 0)) K} :
    g ∈ spTop ↔ spGL g ∈ StatedSp 2 K := by
  rw [mem_spTop, CFSG.Open.StatedAPI.mem_statedSp_iff, coe_spGL, ← reindex_spGram,
    transpose_reindex, ← reindex_mul_sp, ← reindex_mul_sp]
  exact (reindex spIdx spIdx).injective.eq_iff.symm

theorem map_spTop_spGL : spTop.map (spGL (K := K)) = StatedSp 2 K := by
  ext A
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_spTop_iff_spGL.1 hg
  · intro hA
    have hdet := det_of_mem_statedSp_two hA
    set A' : SpecialLinearGroup (Fin 2 ⊕ Fin 2) K :=
      ⟨(A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), hdet⟩ with hA'
    set g := (CFSG.RankThree.PartTwo.Census.slReindex K spIdx).symm A' with hgdef
    have hg : spGL g = A := by
      apply Units.ext
      have h1 : CFSG.RankThree.PartTwo.Census.slReindex K spIdx g = A' :=
        MulEquiv.apply_symm_apply _ _
      change ((CFSG.RankThree.PartTwo.Census.slReindex K spIdx g :
        SpecialLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      rw [h1]
    exact ⟨g, mem_spTop_iff_spGL.2 (hg ▸ hA), hg⟩

@[expose] noncomputable def spEquiv : ↥(spTop (K := K)) ≃* ↥(StatedSp 2 K) :=
  (spTop.equivMapOfInjective spGL spGL_injective).trans (MulEquiv.subgroupCongr map_spTop_spGL)

theorem coe_spEquiv (g : ↥(spTop (K := K))) :
    ((spEquiv g : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) = spGL g := rfl

theorem spGL_mem_scalars_iff {g : SpecialLinearGroup (Kap (Fin 0)) K} :
    spGL g ∈ StatedScalars (Fin 2 ⊕ Fin 2) K ↔ g ∈ Subgroup.center _ := by
  constructor
  · rintro ⟨c, hc⟩
    have hc' := congrArg (fun A : GL (Fin 2 ⊕ Fin 2) K =>
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
    simp only [GeneralLinearGroup.coe_scalar, coe_spGL] at hc'
    have hg : (g : Matrix (Kap (Fin 0)) (Kap (Fin 0)) K) = scalar (Kap (Fin 0)) (c : K) := by
      have h2 := congrArg (reindex spIdx.symm spIdx.symm) hc'
      simp only [reindex_apply, Equiv.symm_symm, submatrix_submatrix, Equiv.symm_comp_self,
        submatrix_id_id] at h2
      rw [← h2, scalar_apply, scalar_apply, submatrix_diagonal_equiv]
      rfl
    refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨c, ?_, hg.symm⟩
    have hdet := g.2
    rw [hg, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at hdet
    exact hdet
  · intro hg
    obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (by simp [Kap, Lam])] at hr
      exact zero_ne_one hr
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, coe_spGL, ← hrg, scalar_apply, scalar_apply, reindex_apply,
      submatrix_diagonal_equiv]
    rfl

variable {σ : K ≃+* K} {hσ3 : σ ^ 3 = 1} {x : K} {hx : σ x ≠ x}

theorem map_Zt_spEquiv :
    (spData σ hσ3 x hx).Zt.map (spEquiv (K := K)).toMonoidHom =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 K := by
  ext A
  obtain ⟨g, rfl⟩ := (spEquiv (K := K)).surjective A
  rw [Subgroup.mem_subgroupOf, coe_spEquiv, spGL_mem_scalars_iff]
  constructor
  · rintro ⟨z, hz, hzg⟩
    rw [← spEquiv.injective hzg]
    exact Subgroup.mem_subgroupOf.1 hz
  · intro hg
    exact ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩

@[expose] noncomputable def spXEquiv (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (x : K) (hx : σ x ≠ x) :
    (spData σ hσ3 x hx).XD ≃* StatedProj (StatedSp 2 K) :=
  QuotientGroup.congr _ _ spEquiv map_Zt_spEquiv

theorem spXEquiv_mk (g : ↥(spData σ hσ3 x hx).Gt) :
    spXEquiv σ hσ3 x hx ((spData σ hσ3 x hx).πD g) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K (spEquiv g) :=
  QuotientGroup.congr_mk' _ _ _ map_Zt_spEquiv g

theorem spEquiv_σt (g : ↥(spData σ hσ3 x hx).Gt) :
    spEquiv ((spData σ hσ3 x hx).σt g) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp 2 K σ (spEquiv g) := by
  apply Subtype.ext
  apply Units.ext
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp]
  ext i j
  rfl

theorem congr_ψD_eq_fieldAut_sp :
    MulAut.congr (spXEquiv σ hσ3 x hx) (spData σ hσ3 x hx).ψD =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K σ := by
  ext p
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 K) p
  obtain ⟨g, rfl⟩ := (spEquiv (K := K)).surjective A
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have e1 : (spXEquiv σ hσ3 x hx).symm (QuotientGroup.mk' _ (spEquiv g)) =
      (spData σ hσ3 x hx).πD g := by
    rw [MulEquiv.symm_apply_eq]
    exact (spXEquiv_mk g).symm
  have e2 := (spData σ hσ3 x hx).ψD_mk g
  have e3 := spEquiv_σt (σ := σ) (hσ3 := hσ3) (x := x) (hx := hx) g
  rw [e1, e2, spXEquiv_mk, e3]
  rfl

theorem conj_proj_eq_conjAut_sp (g : ↥(StatedSp 2 K)) :
    MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K g) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut 2 K
        ⟨g, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.statedSp_le_gsp g.2⟩ := by
  ext p
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 K) p
  change _ = CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut 2 K _
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K h)
  rw [MulAut.conj_apply, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut_proj]
  change QuotientGroup.mk' _ g * QuotientGroup.mk' _ h * (QuotientGroup.mk' _ g)⁻¹ = _
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem modelB_psp4 {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ModelB (StatedProj (StatedSp 2 K))
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K σ) := by
  have hσ3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  obtain ⟨x, hx⟩ := exists_apply_ne hσ1
  have hp := CharP.prime_ringChar K
  have hK5 : 5 ≤ ringChar K := hp.five_le_of_ne_two_of_ne_three hK2 hK3
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hcast : ∀ m : ℕ, m.Prime → ringChar K ≠ m → ((m : ℕ) : K) ≠ 0 := fun m hm hne h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hm).1 ((CharP.cast_eq_zero_iff K (ringChar K) m).1 h))
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast hcast 3 Nat.prime_three hK3
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hcast 2 Nat.prime_two hK2
  set D := spData σ hσ3 x hx with hD
  have hK4 : 4 ≤ Nat.card K := by
    have h1 := ringChar_le_card_fixField σ
    have h2 : Nat.card (fixField σ) ≤ Nat.card K :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    omega
  have hl : CFSG.Open.IsQuasisimple ↥D.Gl :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv
      (isQuasisimple_SL (by simp [Lam]) hK4)
  have hZ3 : ∀ z ∈ D.Zt, z ^ 3 = 1 → z = 1 := D.hZ3_of_card (by simp [Kap, Lam])
  have hout : D.ψD ∉ (MulAut.conj : D.XD →* MulAut D.XD).range := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 K) (spXEquiv σ hσ3 x hx y)
    have h1 : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K σ ∈
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut 2 K).range := by
      rw [← congr_ψD_eq_fieldAut_sp (hσ3 := hσ3) (x := x) (hx := hx), ← hy, congr_conj, ← hg]
      exact ⟨_, (conj_proj_eq_conjAut_sp g).symm⟩
    exact hσ1 ((CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_range_conjAut_iff (by norm_num)).1 h1)
  have hM := D.modelB h3 h2 hl hZ3 (D.layer_of_Gl_eq_top rfl hK5) hout
  have h := ModelB.congr (spXEquiv σ hσ3 x hx) hM
  rwa [congr_ψD_eq_fieldAut_sp (hσ3 := hσ3) (x := x) (hx := hx)] at h

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Field

end
