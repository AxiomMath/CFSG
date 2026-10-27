module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaFacts
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutFixed
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutSimple

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
open scoped commutatorElement

@[expose] def jTwo : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  reindex sixEquiv sixEquiv (fromBlocks 0 1 (-1) 0)

@[expose] def binTv (w : Fin 6 → ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  1 + vecMulVec w (jTwo *ᵥ w)

structure IsBinInvol (X : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop where
  mul_self : X * X = 1
  isometry : Xᵀ * jTwo * X = jTwo

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

theorem map_jTwo : jTwo.map (binCast h) = (sixJ h : Matrix (Fin 6) (Fin 6) F) := by
  rw [jTwo, map_reindex]
  exact binMat_J h

theorem map_binCast_mul_self {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    X.map (binCast h) * X.map (binCast h) = 1 := by
  rw [← Matrix.map_mul, hX.mul_self, Matrix.map_one _ (map_zero _) (map_one _)]

theorem det_eq_one_of_isBinInvol {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    X.det = 1 := by
  have h1 : X.det * X.det = 1 := by rw [← det_mul, hX.mul_self, det_one]
  rcases zmod_two_cases X.det with h0 | h0
  · rw [h0, zero_mul] at h1
    exact absurd h1 zero_ne_one
  · exact h0

theorem binInvol_mem {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    (⟨X.map (binCast h), X.map (binCast h), map_binCast_mul_self h hX,
      map_binCast_mul_self h hX⟩ : GL (Fin 6) F) ∈ sixS h := by
  refine ⟨?_, ?_⟩
  · change ((X.map (binCast h)).map h.bar)ᵀ * (sixJ h : Matrix (Fin 6) (Fin 6) F) *
      X.map (binCast h) = sixJ h
    have hbar : (X.map (binCast h)).map h.bar = X.map (binCast h) := by
      ext i j
      exact bar_binCast h (X i j)
    rw [hbar, ← map_jTwo h, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hX.isometry]
  · change (X.map (binCast h)).det = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_eq_one_of_isBinInvol hX, map_one]

@[expose] noncomputable def binInvol {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    sixS h :=
  ⟨_, binInvol_mem h hX⟩

theorem coe_binInvol {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    ((binInvol h hX : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = X.map (binCast h) :=
  rfl

theorem binInvol_mul_self {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    binInvol h hX * binInvol h hX = 1 :=
  Subtype.ext (Units.ext (map_binCast_mul_self h hX))

theorem binInvol_inv {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    (binInvol h hX)⁻¹ = binInvol h hX :=
  inv_eq_of_mul_eq_one_right (binInvol_mul_self h hX)

theorem binInvol_mem_binarySp {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) :
    binInvol h hX ∈ binarySp h := by
  rw [mem_binarySp_iff]
  intro i j
  exact binCast_mem_bot h (X i j)

theorem binInvol_commute {X Y : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X)
    (hY : IsBinInvol Y) (hXY : X * Y = Y * X) :
    binInvol h hX * binInvol h hY = binInvol h hY * binInvol h hX :=
  Subtype.ext (Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, coe_binInvol, ← Matrix.map_mul, hXY]))

@[expose] def tvA : Matrix (Fin 6) (Fin 6) (ZMod 2) := binTv ![0, 0, 1, 0, 0, 0]

@[expose] def tvB : Matrix (Fin 6) (Fin 6) (ZMod 2) := binTv ![0, 0, 0, 0, 0, 1]

@[expose] def tvC : Matrix (Fin 6) (Fin 6) (ZMod 2) := binTv ![1, 0, 1, 0, 0, 0]

@[expose] def tvD : Matrix (Fin 6) (Fin 6) (ZMod 2) := binTv ![0, 1, 0, 0, 0, 1]

@[expose] def tvT : Matrix (Fin 6) (Fin 6) (ZMod 2) := binTv ![1, 0, 0, 0, 0, 0]

@[expose] def vTwo : Matrix (Fin 6) (Fin 6) (ZMod 2) := nMat !![0, 1, 0; 1, 0, 0; 0, 0, 0]

theorem isBinInvol_tvA : IsBinInvol tvA := ⟨by decide, by decide⟩

theorem isBinInvol_tvB : IsBinInvol tvB := ⟨by decide, by decide⟩

theorem isBinInvol_tvC : IsBinInvol tvC := ⟨by decide, by decide⟩

theorem isBinInvol_tvD : IsBinInvol tvD := ⟨by decide, by decide⟩

theorem isBinInvol_tvT : IsBinInvol tvT := ⟨by decide, by decide⟩

theorem isBinInvol_vTwo : IsBinInvol vTwo := ⟨by decide, by decide⟩

theorem tvA_comm : tvA * tvT = tvT * tvA := by decide

theorem tvB_comm : tvB * tvT = tvT * tvB := by decide

theorem tvC_comm : tvC * tvT = tvT * tvC := by decide

theorem tvD_comm : tvD * tvT = tvT * tvD := by decide

theorem tvT_eq : tvT = 1 + single 0 3 1 := by decide

theorem word_eq_vTwo :
    tvA * tvB * tvA * tvB * (tvC * tvD * tvC * tvD) * (tvB * (tvA * (tvB * tvA))) *
        (tvD * (tvC * (tvD * tvC))) * (tvA * tvB * tvA * tvB * (tvC * tvD * tvC * tvD) *
          (tvB * (tvA * (tvB * tvA))) * (tvD * (tvC * (tvD * tvC)))) = vTwo := by
  decide +kernel

theorem binInvol_vTwo_eq :
    ⁅⁅binInvol h isBinInvol_tvA, binInvol h isBinInvol_tvB⁆,
        ⁅binInvol h isBinInvol_tvC, binInvol h isBinInvol_tvD⁆⁆ *
      ⁅⁅binInvol h isBinInvol_tvA, binInvol h isBinInvol_tvB⁆,
        ⁅binInvol h isBinInvol_tvC, binInvol h isBinInvol_tvD⁆⁆ = binInvol h isBinInvol_vTwo := by
  simp only [commutatorElement_def, _root_.mul_inv_rev, binInvol_inv]
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_binInvol, ← Matrix.map_mul]
  rw [word_eq_vTwo]

theorem nMat_map_of {R R' : Type} [Field R] [Field R'] (f : R → R') (hf0 : f 0 = 0)
    (hf1 : f 1 = 1) (B : Matrix (Fin 3) (Fin 3) R) : (nMat B).map f = nMat (B.map f) := by
  rw [nMat, nMat, map_reindex, fromBlocks_map, Matrix.map_one _ hf0 hf1, Matrix.map_zero _ hf0]

theorem t0Elt_eq_binInvol : t0Elt h = binInvol h isBinInvol_tvT := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_t0Elt_eq, coe_binInvol, tvT_eq, Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), map_single, map_one]

@[expose] def bOne : Matrix (Fin 3) (Fin 3) F :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

theorem bOne_hermitian : ((bOne : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ = bOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bOne]

theorem nElt_bOne_eq : nElt h bOne (bOne_hermitian h) = binInvol h isBinInvol_vTwo := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_nElt, coe_binInvol, vTwo, nMat_map_of _ (map_zero _) (map_one _)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bOne]

theorem sixProj_mem_fixed_sigmaQ {g : sixS h} (hg : g ∈ binarySp h) :
    sixProj h g ∈ fixedSubgroup (sigmaQ h) := by
  rw [mem_fixedSubgroup, sigmaQ_sixProj', (sigmaS_eq_self_iff h g).mpr hg]

theorem sixProj_mem_fixed_alphaOne {g : sixS h} (hg : g ∈ binarySp h)
    (ht : g * t0Elt h = t0Elt h * g) : sixProj h g ∈ fixedSubgroup (alphaOne h) := by
  rw [mem_fixedSubgroup, alphaOne_sixProj, (sigmaS_eq_self_iff h g).mpr hg, ← ht,
    mul_inv_cancel_right]

theorem mem_fixed_of_binInvol {γ : MulAut (sixQ h)}
    (hγ : ∀ g ∈ binarySp h, g * t0Elt h = t0Elt h * g → γ (sixProj h g) = sixProj h g)
    {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : IsBinInvol X) (hXT : X * tvT = tvT * X) :
    sixProj h (binInvol h hX) ∈ fixedSubgroup γ :=
  hγ _ (binInvol_mem_binarySp h hX) (by
    rw [t0Elt_eq_binInvol]
    exact binInvol_commute h hX isBinInvol_tvT hXT)

theorem sixProj_vTwo_mem {γ : MulAut (sixQ h)}
    (hγ : ∀ g ∈ binarySp h, g * t0Elt h = t0Elt h * g → γ (sixProj h g) = sixProj h g) :
    sixProj h (binInvol h isBinInvol_vTwo) ∈
      ⁅⁅fixedSubgroup γ, fixedSubgroup γ⁆, ⁅fixedSubgroup γ, fixedSubgroup γ⁆⁆ := by
  have hd := Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator (mem_fixed_of_binInvol h hγ isBinInvol_tvA tvA_comm)
      (mem_fixed_of_binInvol h hγ isBinInvol_tvB tvB_comm))
    (Subgroup.commutator_mem_commutator (mem_fixed_of_binInvol h hγ isBinInvol_tvC tvC_comm)
      (mem_fixed_of_binInvol h hγ isBinInvol_tvD tvD_comm))
  rw [← binInvol_vTwo_eq, map_mul]
  simp only [map_commutatorElement]
  exact mul_mem hd hd

@[expose] def bOmega (ω : F) : Matrix (Fin 3) (Fin 3) F :=
  !![0, ω, 0; ω ^ 2, 0, 0; 0, 0, 0]

theorem bOmega_hermitian {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ((bOmega ω).map h.bar)ᵀ = bOmega ω := by
  have h3 := omega_pow_three h hω
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bOmega, bar_eq_sq h]
  linear_combination ω * h3

theorem bOmega_add_map {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    bOmega ω + (bOmega ω).map h.bar = bOne := by
  have h3 := omega_pow_three h hω
  have h2 := two_eq_zero h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bOmega, bOne, bar_eq_sq h]
  · linear_combination hω - h2
  · linear_combination hω + ω * h3 - h2

theorem hermitian_map_bar {B : Matrix (Fin 3) (Fin 3) F} (hB : (B.map h.bar)ᵀ = B) :
    ((B.map h.bar).map h.bar)ᵀ = B.map h.bar := by
  rw [← transpose_map, hB]

theorem sigmaS_nElt (B : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B) :
    sigmaS h (nElt h B hB) = nElt h (B.map h.bar) (hermitian_map_bar h hB) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_sigmaS, UnitaryHigher.coe_glAut, coe_nElt, coe_nElt,
    nMat_map_of _ (map_zero _) (map_one _)]
  rfl

theorem nElt_comm (B B' : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B)
    (hB' : (B'.map h.bar)ᵀ = B') : nElt h B hB * nElt h B' hB' = nElt h B' hB' * nElt h B hB :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_nElt, coe_nElt,
      nMat_mul, nMat_mul, add_comm]))

theorem alphaOne_nElt (B : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B) :
    alphaOne h (sixProj h (nElt h B hB)) = sigmaQ h (sixProj h (nElt h B hB)) := by
  rw [alphaOne_sixProj, sigmaQ_sixProj', sigmaS_nElt, t0Elt, tElt, nElt_comm,
    mul_inv_cancel_right]

theorem exists_fusion_of_eq_sigmaQ {ω : F} (hω : ω ^ 2 + ω + 1 = 0) {γ : MulAut (sixQ h)}
    (hγn : ∀ (B : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B),
      γ (sixProj h (nElt h B hB)) = sigmaQ h (sixProj h (nElt h B hB)))
    (hγ : ∀ g ∈ binarySp h, g * t0Elt h = t0Elt h * g → γ (sixProj h g) = sixProj h g) :
    ∃ l : sixQ h, l * (γ l)⁻¹ ≠ 1 ∧
      l * (γ l)⁻¹ ∈ ⁅⁅fixedSubgroup γ, fixedSubgroup γ⁆, ⁅fixedSubgroup γ, fixedSubgroup γ⁆⁆ := by
  have hB := bOmega_hermitian h hω
  have key : sixProj h (nElt h (bOmega ω) hB) * (γ (sixProj h (nElt h (bOmega ω) hB)))⁻¹ =
      sixProj h (binInvol h isBinInvol_vTwo) := by
    rw [hγn, sigmaQ_sixProj', sigmaS_nElt, ← nElt_bOne_eq, ← map_inv, ← map_mul,
      inv_eq_of_mul_eq_one_right (nElt_mul_self h _ _)]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, coe_nElt, coe_nElt, coe_nElt, nMat_mul,
      bOmega_add_map h hω]
  refine ⟨sixProj h (nElt h (bOmega ω) hB), ?_, ?_⟩
  · rw [key, ← nElt_bOne_eq]
    refine sixProj_ne_one_of_apply h (a := 0) (b := 4) (by decide) ?_
    change nMat bOne (sixEquiv (Sum.inl 0)) (sixEquiv (Sum.inr 1)) ≠ 0
    rw [nMat_apply_inl_inr]
    simp [bOne]
  · rw [key]
    exact sixProj_vTwo_mem h hγ

theorem exists_fusion_sigmaQ {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ l : sixQ h, l * (sigmaQ h l)⁻¹ ≠ 1 ∧ l * (sigmaQ h l)⁻¹ ∈
      ⁅⁅fixedSubgroup (sigmaQ h), fixedSubgroup (sigmaQ h)⁆,
        ⁅fixedSubgroup (sigmaQ h), fixedSubgroup (sigmaQ h)⁆⁆ :=
  exists_fusion_of_eq_sigmaQ h hω (fun _ _ => rfl) fun _ hg _ => sixProj_mem_fixed_sigmaQ h hg

theorem exists_fusion_alphaOne {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ l : sixQ h, l * (alphaOne h l)⁻¹ ≠ 1 ∧ l * (alphaOne h l)⁻¹ ∈
      ⁅⁅fixedSubgroup (alphaOne h), fixedSubgroup (alphaOne h)⁆,
        ⁅fixedSubgroup (alphaOne h), fixedSubgroup (alphaOne h)⁆⁆ :=
  exists_fusion_of_eq_sigmaQ h hω (alphaOne_nElt h) fun _ hg ht =>
    sixProj_mem_fixed_alphaOne h hg ht

end CFSG.EvenSmallLie.UnitarySix.Yamada
