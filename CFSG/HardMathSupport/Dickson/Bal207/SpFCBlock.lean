module

public import CFSG.HardMathSupport.Dickson.Bal207.SemilinCoord
public import CFSG.HardMathSupport.Dickson.Bal207.SpFCField
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerSemi
import all CFSG.HardMathSupport.Dickson.Bal207.SpShape

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Polynomial Matrix CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem conj_inl_left {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (x : N ⋊[φ] G) (n : N) :
    (x * SemidirectProduct.inl n * x⁻¹).left = x.left * φ x.right n * x.left⁻¹ := by
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one,
    ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

variable {r : ℕ} {F : Type} [Field F]

abbrev SemiSp (r : ℕ) (F : Type) [Field F] : Type := StatedSp r F ⋊[fieldSp r F] (F ≃+* F)

abbrev semiA (y : SemiSp r F) : gsp r F :=
  ⟨(y.left : GL (Fin r ⊕ Fin r) F), statedSp_le_gsp y.left.2⟩

theorem semilinMap_mul (y y' : SemiSp r F) (v : Fin r ⊕ Fin r → F) :
    semilinMap (semiA (y * y')) (y * y').right v =
      semilinMap (semiA y) y.right (semilinMap (semiA y') y'.right v) := by
  have h1 : (((semiA (y * y') : gsp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      ((y.left : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((y'.left : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).map
          y.right := by
    change (((y.left * fieldSp r F y.right y'.left : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = _
    rw [Subgroup.coe_mul, Units.val_mul, coe_fieldSp]
  unfold semilinMap
  rw [h1, ← mulVec_mulVec]
  congr 1
  ext i
  exact (RingHom.map_mulVec (y.right : F →+* F) _ _ i).symm

theorem semilinMap_one (v : Fin r ⊕ Fin r → F) :
    semilinMap (semiA (1 : SemiSp r F)) (1 : SemiSp r F).right v = v := by
  unfold semilinMap
  change (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ v = v
  rw [Matrix.one_mulVec]

theorem spForm_semilinMap (y : SemiSp r F) (u w : Fin r ⊕ Fin r → F) :
    spForm r F (semilinMap (semiA y) y.right u) (semilinMap (semiA y) y.right w) =
      y.right (spForm r F u w) := by
  have h := mem_sesqUnitaryGroup.mp (spLin_mem y.left) (y.right ∘ u) (y.right ∘ w)
  calc _ = spForm r F (y.right ∘ u) (y.right ∘ w) := h
    _ = _ := spForm_comp_ringEquiv _ _ _

theorem semiSp_conj_inl (y : SemiSp r F) (γ : StatedSp r F) :
    y * SemidirectProduct.inl γ * y⁻¹ =
      SemidirectProduct.inl (semiConj (semiA y) y.right γ) := by
  refine SemidirectProduct.ext ?_ (by simp [SemidirectProduct.mul_right])
  rw [conj_inl_left, SemidirectProduct.left_inl]
  exact Subtype.ext (by rw [semiConj_apply, coe_conjSp]; rfl)

abbrev semiStab (x : StatedSp r F) : Subgroup (SemiSp r F) :=
  Subgroup.centralizer {SemidirectProduct.inl x}

theorem semiConj_eq_of_mem_semiStab {x : StatedSp r F} {y : SemiSp r F} (hy : y ∈ semiStab x) :
    semiConj (semiA y) y.right x = x := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hy
  apply SemidirectProduct.inl_injective (φ := fieldSp r F)
  rw [← semiSp_conj_inl, h, mul_inv_cancel_right]

section Block

variable {x : StatedSp r F} {g : primaryFactors (spEnd x)}

theorem map_factor (hg : (g : F[X]) = X ^ 2 + X + 1) (σ : F ≃+* F) :
    (g : F[X]).map (σ : F →+* F) = g :=
  map_ringEquiv_of_cases σ (Or.inr hg)

theorem semilinMap_mem_block (hg : (g : F[X]) = X ^ 2 + X + 1) {y : SemiSp r F}
    (hy : y ∈ semiStab x) {v : Fin r ⊕ Fin r → F}
    (hv : v ∈ primaryComponent (spEnd x) (g : F[X])) :
    semilinMap (semiA y) y.right v ∈ primaryComponent (spEnd x) (g : F[X]) :=
  (semilinMap_mem_primaryComponent_iff _ _ (semiConj_eq_of_mem_semiStab hy)
    (map_factor hg _) v).2 hv

@[expose] noncomputable def blockSemi (hg : (g : F[X]) = X ^ 2 + X + 1) (y : semiStab x) :
    primaryComponent (spEnd x) (g : F[X]) →+ primaryComponent (spEnd x) (g : F[X]) where
  toFun v := ⟨semilinMap (semiA (y : SemiSp r F)) (y : SemiSp r F).right v,
    semilinMap_mem_block hg y.2 v.2⟩
  map_zero' := Subtype.ext (semilinMap_zero (semiA (y : SemiSp r F)) (y : SemiSp r F).right)
  map_add' u v := Subtype.ext (semilinMap_add (semiA (y : SemiSp r F)) (y : SemiSp r F).right
    (u : Fin r ⊕ Fin r → F) (v : Fin r ⊕ Fin r → F))

theorem coe_blockSemi (hg : (g : F[X]) = X ^ 2 + X + 1) (y : semiStab x)
    (v : primaryComponent (spEnd x) (g : F[X])) :
    ((blockSemi hg y v : primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F) =
      semilinMap (semiA (y : SemiSp r F)) (y : SemiSp r F).right v :=
  rfl

theorem blockSemi_mul (hg : (g : F[X]) = X ^ 2 + X + 1) (y y' : semiStab x)
    (v : primaryComponent (spEnd x) (g : F[X])) :
    blockSemi hg (y * y') v = blockSemi hg y (blockSemi hg y' v) :=
  Subtype.ext (semilinMap_mul (y : SemiSp r F) (y' : SemiSp r F) (v : Fin r ⊕ Fin r → F))

theorem blockSemi_one (hg : (g : F[X]) = X ^ 2 + X + 1)
    (v : primaryComponent (spEnd x) (g : F[X])) : blockSemi hg 1 v = v :=
  Subtype.ext (semilinMap_one (v : Fin r ⊕ Fin r → F))

theorem blockSemi_surjective (hg : (g : F[X]) = X ^ 2 + X + 1) (y : semiStab x) :
    Function.Surjective (blockSemi hg y) := fun w =>
  ⟨blockSemi hg y⁻¹ w, by rw [← blockSemi_mul, mul_inv_cancel, blockSemi_one]⟩

theorem blockSemi_smul (hg : (g : F[X]) = X ^ 2 + X + 1) (y : semiStab x)
    (c : AdjoinRoot (g : F[X])) (v : primaryComponent (spEnd x) (g : F[X])) :
    blockSemi hg y (c • v) =
      extAut (g : F[X]) (y : SemiSp r F).right (map_factor hg _) c • blockSemi hg y v := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
  refine Subtype.ext ?_
  rw [coe_blockSemi, coe_mk_smul_primaryComponent,
    semilinMap_aeval _ _ (semiConj_eq_of_mem_semiStab y.2), extAut_mk,
    coe_mk_smul_primaryComponent, coe_blockSemi]

variable {ℓ f : ℕ} (hE : UnitaryFieldData ℓ f (AdjoinRoot (g : F[X])))
  {H : primaryComponent (spEnd x) (g : F[X]) →ₛₗ[hE.bar]
    primaryComponent (spEnd x) (g : F[X]) →ₗ[AdjoinRoot (g : F[X])] AdjoinRoot (g : F[X])}

theorem blockSemi_isometry (hg : (g : F[X]) = X ^ 2 + X + 1)
    (htr : ∀ (v w : primaryComponent (spEnd x) (g : F[X])) (c : AdjoinRoot (g : F[X])),
      Algebra.trace F (AdjoinRoot (g : F[X])) (c * H v w) =
        spForm r F (v : Fin r ⊕ Fin r → F)
          ((c • w : primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F))
    (y : semiStab x) (u w : primaryComponent (spEnd x) (g : F[X])) :
    H (blockSemi hg y u) (blockSemi hg y w) =
      extAut (g : F[X]) (y : SemiSp r F).right (map_factor hg _) (H u w) := by
  refine eq_of_forall_trace_mul_eq hg fun c => ?_
  have hc : c • blockSemi hg y w = blockSemi hg y
      ((extAut (g : F[X]) (y : SemiSp r F).right (map_factor hg _)).symm c • w) := by
    rw [blockSemi_smul, RingEquiv.apply_symm_apply]
  rw [htr, hc, coe_blockSemi, coe_blockSemi, spForm_semilinMap, ← htr,
    ← trace_extAut hg (map_factor hg _), map_mul, RingEquiv.apply_symm_apply]

variable {n : ℕ}
  (b : Module.Basis (Fin n) (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])))

theorem blockMat_unitary (hg : (g : F[X]) = X ^ 2 + X + 1)
    (htr : ∀ (v w : primaryComponent (spEnd x) (g : F[X])) (c : AdjoinRoot (g : F[X])),
      Algebra.trace F (AdjoinRoot (g : F[X])) (c * H v w) =
        spForm r F (v : Fin r ⊕ Fin r → F)
          ((c • w : primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (y : semiStab x) :
    ((semMat b (blockSemi hg y)).map hE.bar)ᵀ * semMat b (blockSemi hg y) = 1 :=
  semMat_unitary b hE hb fun i j => by
    rw [blockSemi_isometry hE hg htr, hb]
    split_ifs <;> simp

@[expose] noncomputable def blockRho (hg : (g : F[X]) = X ^ 2 + X + 1)
    (htr : ∀ (v w : primaryComponent (spEnd x) (g : F[X])) (c : AdjoinRoot (g : F[X])),
      Algebra.trace F (AdjoinRoot (g : F[X])) (c * H v w) =
        spForm r F (v : Fin r ⊕ Fin r → F)
          ((c • w : primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) : semiStab x →* blockGamma hE n where
  toFun y := semGamma b hE (blockMat_unitary hE b hg htr hb y)
    (extAut (g : F[X]) (y : SemiSp r F).right (map_factor hg _))
  map_one' := by
    have h1 : extAut (g : F[X]) ((1 : semiStab x) : SemiSp r F).right (map_factor hg _) = 1 :=
      extAut_one _
    have h2 : ∀ v, blockSemi hg (1 : semiStab x) v =
        ((Matrix.GeneralLinearGroup.toLin' b
          ((1 : primeFormUnitary hE (oneGram (AdjoinRoot (g : F[X])) n)) :
            GL (Fin n) (AdjoinRoot (g : F[X]))) :
          LinearMap.GeneralLinearGroup (AdjoinRoot (g : F[X]))
            (primaryComponent (spEnd x) (g : F[X]))) :
          primaryComponent (spEnd x) (g : F[X]) →ₗ[AdjoinRoot (g : F[X])]
            primaryComponent (spEnd x) (g : F[X])) v := fun v => by
      rw [blockSemi_one, Subgroup.coe_one, map_one, Units.val_one, Module.End.one_apply]
    show semGamma b hE (blockMat_unitary hE b hg htr hb 1) _ = 1
    rw [h1, semGamma_one_eq_inl b hE (blockMat_unitary hE b hg htr hb 1) h2, map_one]
  map_mul' y y' := by
    have he : extAut (g : F[X]) ((y * y' : semiStab x) : SemiSp r F).right (map_factor hg _) =
        extAut (g : F[X]) (y : SemiSp r F).right (map_factor hg _) *
          extAut (g : F[X]) (y' : SemiSp r F).right (map_factor hg _) :=
      extAut_mul (σ := (y : SemiSp r F).right) (σ' := (y' : SemiSp r F).right) _ _ _
    show semGamma b hE (blockMat_unitary hE b hg htr hb (y * y')) _ =
      semGamma b hE (blockMat_unitary hE b hg htr hb y) _ *
        semGamma b hE (blockMat_unitary hE b hg htr hb y') _
    rw [he]
    exact semGamma_mul b hE (blockSemi_smul hg y) (fun v => blockSemi_mul hg y y' v) _ _ _

theorem toLin'_conj_blockSemi (hg : (g : F[X]) = X ^ 2 + X + 1)
    (htr : ∀ (v w : primaryComponent (spEnd x) (g : F[X])) (c : AdjoinRoot (g : F[X])),
      Algebra.trace F (AdjoinRoot (g : F[X])) (c * H v w) =
        spForm r F (v : Fin r ⊕ Fin r → F)
          ((c • w : primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (y : semiStab x)
    (M : primeFormUnitary hE (oneGram (AdjoinRoot (g : F[X])) n))
    (w : primaryComponent (spEnd x) (g : F[X])) :
    ((Matrix.GeneralLinearGroup.toLin' b (((blockRho hE b hg htr hb y * SemidirectProduct.inl M *
      (blockRho hE b hg htr hb y)⁻¹).left : primeFormUnitary hE _) :
        GL (Fin n) (AdjoinRoot (g : F[X]))) :
          LinearMap.GeneralLinearGroup _ _) : _ →ₗ[AdjoinRoot (g : F[X])] _) (blockSemi hg y w) =
      blockSemi hg y (((Matrix.GeneralLinearGroup.toLin' b (M : GL (Fin n) _) :
        LinearMap.GeneralLinearGroup _ _) : _ →ₗ[AdjoinRoot (g : F[X])] _) w) := by
  apply b.equivFun.injective
  have hT := blockSemi_smul hg y
  set τ := extAut (g : F[X]) (y : SemiSp r F).right (map_factor hg _) with hτ
  set u := (blockRho hE b hg htr hb y).left with hu
  have hN : ((u : GL (Fin n) (AdjoinRoot (g : F[X]))) :
      Matrix (Fin n) (Fin n) (AdjoinRoot (g : F[X]))) = semMat b (blockSemi hg y) := rfl
  have hr : (blockRho hE b hg htr hb y).right = τ := rfl
  have hinv : (((u : GL (Fin n) (AdjoinRoot (g : F[X])))⁻¹ : GL (Fin n) (AdjoinRoot (g : F[X]))) :
      Matrix (Fin n) (Fin n) (AdjoinRoot (g : F[X]))) * ((u : GL (Fin n) (AdjoinRoot (g : F[X]))) :
        Matrix (Fin n) (Fin n) (AdjoinRoot (g : F[X]))) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, repr_semilin b (τ := τ) hT,
    repr_semilin b (τ := τ) hT, CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply,
    conj_inl_left, ← hu, hr, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
    Units.val_mul, coe_primeFormFieldU, coe_glAut, ← hN, ← mulVec_mulVec,
    mulVec_mulVec (N := ((u : GL (Fin n) (AdjoinRoot (g : F[X]))) :
      Matrix (Fin n) (Fin n) (AdjoinRoot (g : F[X])))), hinv, one_mulVec, ← mulVec_mulVec]
  congr 1
  ext i
  exact (RingHom.map_mulVec (τ : AdjoinRoot (g : F[X]) →+* AdjoinRoot (g : F[X])) _ _ i).symm

variable (φ : spSupported x {(g : F[X])} ≃* sesqUnitaryGroup H)

@[expose] noncomputable def blockIota (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) :
    primeFormUnitary hE (oneGram (AdjoinRoot (g : F[X])) n) ≃* spSupported x {(g : F[X])} :=
  (unitaryEquivOfBasis b hE hb).trans φ.symm

variable (hφ : ∀ (γ : spSupported x {(g : F[X])}) (v : Fin r ⊕ Fin r → F)
  (hv : v ∈ primaryComponent (spEnd x) (g : F[X])),
    blockApply (φ γ : blockGL (spEnd x) (g : F[X])) v hv = spEnd (γ : StatedSp r F) v)
include hφ

theorem spEnd_blockIota (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0)
    (M : primeFormUnitary hE (oneGram (AdjoinRoot (g : F[X])) n))
    (v : primaryComponent (spEnd x) (g : F[X])) :
    spEnd ((blockIota hE b φ hb M : spSupported x {(g : F[X])}) : StatedSp r F) v =
      ((((Matrix.GeneralLinearGroup.toLin' b (M : GL (Fin n) (AdjoinRoot (g : F[X]))) :
        LinearMap.GeneralLinearGroup _ _) : _ →ₗ[AdjoinRoot (g : F[X])] _) v :
          primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F) := by
  rw [← hφ _ v v.2]
  change blockApply (φ (φ.symm (unitaryEquivOfBasis b hE hb M)) :
    blockGL (spEnd x) (g : F[X])) v v.2 = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem eq_of_spEnd_eq {γ γ' : spSupported x {(g : F[X])}}
    (h : ∀ v : primaryComponent (spEnd x) (g : F[X]),
      spEnd (γ : StatedSp r F) v = spEnd (γ' : StatedSp r F) v) : γ = γ' := by
  refine φ.injective (Subtype.ext (Units.ext (LinearMap.ext fun v => Subtype.ext ?_)))
  exact (hφ γ v v.2).trans ((h v).trans (hφ γ' v v.2).symm)

theorem semiConj_blockIota [Finite F] (hg : (g : F[X]) = X ^ 2 + X + 1)
    (hfac : ∀ k ∈ primaryFactors (spEnd x), k = X - 1 ∨ k = X ^ 2 + X + 1)
    (htr : ∀ (v w : primaryComponent (spEnd x) (g : F[X])) (c : AdjoinRoot (g : F[X])),
      Algebra.trace F (AdjoinRoot (g : F[X])) (c * H v w) =
        spForm r F (v : Fin r ⊕ Fin r → F)
          ((c • w : primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F))
    (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (y : semiStab x)
    (M : primeFormUnitary hE (oneGram (AdjoinRoot (g : F[X])) n)) :
    semiConj (semiA (y : SemiSp r F)) (y : SemiSp r F).right
        ((blockIota hE b φ hb M : spSupported x {(g : F[X])}) : StatedSp r F) =
      ((blockIota hE b φ hb ((blockRho hE b hg htr hb y * SemidirectProduct.inl M *
        (blockRho hE b hg htr hb y)⁻¹).left) : spSupported x {(g : F[X])}) : StatedSp r F) := by
  have hmem := semiConj_mem_spSupported (semiA (y : SemiSp r F)) (y : SemiSp r F).right
    (semiConj_eq_of_mem_semiStab y.2) (fun k hk => map_ringEquiv_of_cases _ (hfac k hk))
    (blockIota hE b φ hb M).2
  refine congrArg Subtype.val (eq_of_spEnd_eq hE φ hφ (γ := ⟨_, hmem⟩) fun v => ?_)
  obtain ⟨u, rfl⟩ := blockSemi_surjective hg y v
  rw [spEnd_blockIota hE b φ hφ hb _ (blockSemi hg y u), toLin'_conj_blockSemi, coe_blockSemi,
    coe_blockSemi]
  change spEnd (semiConj (semiA (y : SemiSp r F)) (y : SemiSp r F).right _) _ = _
  rw [spEnd_semiConj_semilinMap, spEnd_blockIota hE b φ hφ hb M u]

end Block

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
