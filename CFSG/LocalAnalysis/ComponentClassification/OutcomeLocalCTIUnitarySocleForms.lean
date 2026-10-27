module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalComponentFree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSULinearRadical

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open FourGroupEvenCanonical UnitaryHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open LinearMap (BilinForm)

section Radical

open NonalternatingRadical

variable {k : Type} [Field k] {n : ℕ}

theorem conj_mem_radicalGroup [CharP k 2] (hn : Even n) {i : Fin n} {B : GL (Fin n) k}
    (hB : B ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k}
    (hg : g ∈ radicalGroup i) : B * g * B⁻¹ ∈ radicalGroup i := by
  obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
  refine mem_radicalGroup_of_dotProduct hn (x := (B : Matrix (Fin n) (Fin n) k) *ᵥ v) (c := c)
    ?_ ?_
  · rw [onesVec_dotProduct_mulVec_of_mem hB, (mem_radicalW.mp hv).1]
  · rw [Units.val_mul, Units.val_mul, hc, conj_radicalMatrix hB]

theorem no_component_matrixIsometryGroup_one_of_even [Finite k] [CharP k 2] (hn : Even n)
    (hn3 : 3 ≤ n) (B : Subgroup (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k))) :
    ¬ CFSG.IsComponent B := by
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Finite (GL (Fin n) k) := Finite.of_injective Units.val Units.val_injective
  refine UnbalancingLocal.ComponentFree.no_component_of_two_radical (R := radicalGroup i)
    (radicalGroup_le hn i) (fun x hx => ?_) (fun r hr => ⟨1, ?_⟩) (fun x hx hcx => ?_) B
  · rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => conj_mem_radicalGroup hn hx hg, fun hg => ?_⟩
    have h := conj_mem_radicalGroup hn (inv_mem hx) hg
    rwa [show x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g by group] at h
  · rw [pow_one, sq, mul_self_of_mem_radicalGroup hn hr]
  · have hx' := eq_radical_of_centralizes (K := k) hn hn3 i hx 1 fun g hg => by
      have hcomm : g * x = x * g := mem_centralizer_iff.mp hcx g hg
      rw [map_one, mul_one, ← map_mul, ← map_inv, ← map_mul, ← hcomm, mul_inv_cancel_right]
    exact ⟨1, by rw [pow_one, sq, mul_self_of_mem_radicalGroup hn hx'.2]⟩

end Radical

section OddRestriction

variable {k : Type} [Field k] {n r : ℕ}

theorem dotForm_apply (x y : Fin n → k) :
    Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) x y = x ⬝ᵥ y := by
  rw [Matrix.toBilin'_apply', Units.val_one, one_mulVec]

theorem dotForm_symm (x y : Fin n → k) :
    Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) x y =
      Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) y x := by
  rw [dotForm_apply, dotForm_apply, dotProduct_comm]

theorem dotForm_self [CharP k 2] (x : Fin n → k) :
    Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) x x =
      Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (fun _ => 1) x ^ 2 := by
  rw [dotForm_apply, dotForm_apply]
  simp only [dotProduct, one_mul]
  rw [sum_pow_char]
  simp only [sq]

theorem dotForm_ones [CharP k 2] (hr : n = 2 * r + 1) :
    Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (fun _ => 1) (fun _ => 1) =
      1 := by
  rw [dotForm_apply]
  simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [hr, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add,
    Nat.cast_one]

theorem dotForm_restrict_isAlt [CharP k 2] :
    ((Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).restrict
      (LinearMap.ker (Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
        (fun _ => 1)))).IsAlt :=
  restrict_ker_isAlt _ _ dotForm_self

theorem dotForm_restrict_nondegenerate [CharP k 2] (hr : n = 2 * r + 1) :
    ((Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).restrict
      (LinearMap.ker (Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
        (fun _ => 1)))).Nondegenerate :=
  restrict_ker_nondegenerate _ _ dotForm_symm
    (CatalogueBLinearHigherB.matrixForm_nondegenerate 1).1 (dotForm_ones hr)

theorem finrank_dotForm_ker [CharP k 2] (hr : n = 2 * r + 1) :
    Module.finrank k (LinearMap.ker (Matrix.toBilin' ((1 : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) (fun _ => 1))) = 2 * r := by
  have h := finrank_ker_add_one _ _ (dotForm_ones (k := k) hr)
  rw [Module.finrank_fin_fun] at h
  omega

theorem matrixIsometryGroupEquiv_apply (C : GL (Fin n) k)
    (g : matrixIsometryGroup (C : Matrix (Fin n) (Fin n) k)) (x : Fin n → k) :
    ((matrixIsometryGroupEquiv C g : isometryGroup _) : (Fin n → k) ≃ₗ[k] (Fin n → k)) x =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x := by
  change ((basisMatrixEquiv (Pi.basisFun k (Fin n))).symm (g : GL (Fin n) k)) x = _
  have h := basisMatrixEquiv_mulVec (Pi.basisFun k (Fin n))
    ((basisMatrixEquiv (Pi.basisFun k (Fin n))).symm (g : GL (Fin n) k)) x
  rw [MulEquiv.apply_symm_apply, Pi.basisFun_equivFun] at h
  exact h.symm

@[expose] def oneRestrictEquiv [CharP k 2] (hr : n = 2 * r + 1) :
    matrixIsometryGroup ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ≃*
      isometryGroup ((Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).restrict
        (LinearMap.ker (Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
          (fun _ => 1)))) :=
  (matrixIsometryGroupEquiv 1).trans (isometryGroupRestrictEquiv _ _ dotForm_self dotForm_symm
    (CatalogueBLinearHigherB.matrixForm_nondegenerate 1).1 (dotForm_ones hr))

theorem oneRestrictEquiv_apply [CharP k 2] (hr : n = 2 * r + 1)
    (g : matrixIsometryGroup ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (w : LinearMap.ker (Matrix.toBilin' ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      (fun _ => 1))) :
    ((oneRestrictEquiv hr g).1 w : Fin n → k) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ w :=
  matrixIsometryGroupEquiv_apply 1 g w

theorem mulVec_ones_of_mem_one [CharP k 2]
    (g : matrixIsometryGroup ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ (fun _ => 1) = fun _ => 1 := by
  rw [← matrixIsometryGroupEquiv_apply 1 g]
  exact isometry_fixes_of_sq _ _ dotForm_self
    (CatalogueBLinearHigherB.matrixForm_nondegenerate 1).1 (matrixIsometryGroupEquiv 1 g).2

end OddRestriction

section Reindex

variable {k : Type} [Field k] {n r : ℕ}

abbrev sumFinEquiv (hr : r + r = n) : Fin r ⊕ Fin r ≃ Fin n :=
  finSumFinEquiv.trans (finCongr hr)

theorem blockSwapJ_submatrix [CharP k 2] (hr : r + r = n) :
    (blockSwapJ n r : Matrix (Fin n) (Fin n) k).submatrix (sumFinEquiv hr) (sumFinEquiv hr) =
      fromBlocks 0 1 (-1) 0 := by
  rw [blockSwapJ_eq_submatrix hr, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  have hneg : (-1 : Matrix (Fin r) (Fin r) k) = 1 := by
    ext i j
    rw [Matrix.neg_apply, CharTwo.neg_eq]
  rw [Matrix.J, hneg]

@[expose] def blockSwapIsometryEquivStatedSp [CharP k 2] (hr : r + r = n) :
    matrixIsometryGroup (blockSwapJ n r : Matrix (Fin n) (Fin n) k) ≃* StatedSp r k :=
  ((Units.mapEquiv (Matrix.reindexAlgEquiv k k (sumFinEquiv hr).symm).toMulEquiv).subgroupMap
    _).trans (MulEquiv.subgroupCongr (by
      ext g
      rw [← MulEquiv.toMonoidHom_eq_coe, mem_map_equiv, mem_matrixIsometryGroup,
        SymplecticTorusWeyl.mem_statedSp_iff]
      set σ := sumFinEquiv hr with hσ
      set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) with hM
      have hval : (((Units.mapEquiv (Matrix.reindexAlgEquiv k k σ.symm).toMulEquiv).symm g :
          GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M.submatrix σ.symm σ.symm := rfl
      have hJ : (blockSwapJ n r : Matrix (Fin n) (Fin n) k) =
          (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).submatrix
            σ.symm σ.symm := by
        rw [← blockSwapJ_submatrix hr, submatrix_submatrix, Equiv.self_comp_symm,
          submatrix_id_id]
      rw [hval, hJ, transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
      constructor
      · intro h
        have h2 := congrArg (fun X => X.submatrix σ σ) h
        simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using h2
      · intro h
        rw [h]))

theorem coe_blockSwapIsometryEquivStatedSp [CharP k 2] (hr : r + r = n)
    (g : matrixIsometryGroup (blockSwapJ n r : Matrix (Fin n) (Fin n) k)) :
    ((blockSwapIsometryEquivStatedSp hr g : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).submatrix (sumFinEquiv hr)
        (sumFinEquiv hr) :=
  rfl

end Reindex

section Alternating

theorem antidiagGram_mul_self :
    PresentationLocal.antidiagGram * PresentationLocal.antidiagGram = 1 := by
  decide

theorem antidiagGram_transpose :
    PresentationLocal.antidiagGramᵀ = PresentationLocal.antidiagGram := by
  decide

theorem nonempty_isometryGroup_mulEquiv_of_isometryEquiv {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] {B : BilinForm K V}
    {C : BilinForm K W} (e : B.IsometryEquiv C) :
    Nonempty (isometryGroup B ≃* isometryGroup C) := by
  have hcongr : LinearMap.BilinForm.congr (e : V ≃ₗ[K] W) B = C := by
    refine LinearMap.ext₂ fun x y => ?_
    rw [LinearMap.BilinForm.congr_apply]
    have h1 := e.map_app ((e : V ≃ₗ[K] W).symm y) ((e : V ≃ₗ[K] W).symm x)
    rw [← h1, ← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact ⟨(TauCeti.BilinForm.isometryGroupCongr B (e : V ≃ₗ[K] W)).trans
    (MulEquiv.subgroupCongr (by rw [hcongr]))⟩

theorem nonempty_altIsometry_mulEquiv_statedSp {K : Type} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {r : ℕ} (hdim : Module.finrank K V = 2 * r) :
    Nonempty (isometryGroup B ≃* StatedSp r K) := by
  obtain ⟨e⟩ := exists_form_isometry B (pairedSympForm K r) hB hnd
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [hdim, SymplecticFlag.finrank_standard])
  obtain ⟨φ⟩ := nonempty_isometryGroup_mulEquiv_of_isometryEquiv e
  exact ⟨φ.trans CatalogueBSymplecticB.statedSpIsometryEquiv.symm⟩

theorem map_matrixIsometryGroup_ringEquiv {k k' : Type*} [Field k] [Field k'] (ε : k ≃+* k')
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι k) :
    (matrixIsometryGroup C).map
        ((Units.mapEquiv ε.mapMatrix.toMulEquiv : GL ι k ≃* GL ι k') : GL ι k →* GL ι k') =
      matrixIsometryGroup (ε.mapMatrix C) := by
  ext g
  rw [← MulEquiv.toMonoidHom_eq_coe, mem_map_equiv, mem_matrixIsometryGroup,
    mem_matrixIsometryGroup]
  set M : Matrix ι ι k' := (g : Matrix ι ι k') with hM
  have hval : (((Units.mapEquiv ε.mapMatrix.toMulEquiv).symm g : GL ι k) : Matrix ι ι k) =
      ε.symm.mapMatrix M := rfl
  have hback : ε.mapMatrix (ε.symm.mapMatrix M) = M := by
    ext i j
    simp
  have htr : ∀ X : Matrix ι ι k, ε.mapMatrix Xᵀ = (ε.mapMatrix X)ᵀ := fun X => by
    ext i j
    simp
  rw [hval]
  constructor
  · intro h
    have h2 := congrArg ε.mapMatrix h
    rwa [map_mul, map_mul, htr, hback] at h2
  · intro h
    apply ε.mapMatrix.injective
    rw [map_mul, map_mul, htr, hback, h]

theorem map_matrixIsometryGroup_sympFour {k : Type} [Field k] (ε : ZMod 2 ≃+* k) :
    (matrixIsometryGroup (ε.mapMatrix PresentationLocal.antidiagGram)).map
        ((Units.mapEquiv ε.symm.mapMatrix.toMulEquiv : GL (Fin 4) k ≃* GL (Fin 4) (ZMod 2)) :
          GL (Fin 4) k →* GL (Fin 4) (ZMod 2)) = PresentationLocal.sympFour := by
  ext g
  rw [← MulEquiv.toMonoidHom_eq_coe, mem_map_equiv, mem_matrixIsometryGroup,
    PresentationLocal.mem_sympFour_iff]
  set M : Matrix (Fin 4) (Fin 4) (ZMod 2) := (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hM
  have hval : (((Units.mapEquiv ε.symm.mapMatrix.toMulEquiv).symm g : GL (Fin 4) k) :
      Matrix (Fin 4) (Fin 4) k) = ε.mapMatrix M := rfl
  have htr : ∀ X : Matrix (Fin 4) (Fin 4) (ZMod 2), ε.mapMatrix Xᵀ = (ε.mapMatrix X)ᵀ :=
    fun X => by
      ext i j
      simp
  rw [hval, ← htr, ← map_mul, ← map_mul]
  exact ε.mapMatrix.injective.eq_iff

theorem nonempty_altIsometry_mulEquiv_sympFour {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : BilinForm k V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (hdim : Module.finrank k V = 4) :
    Nonempty (isometryGroup B ≃* PresentationLocal.sympFour) := by
  have := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  have : CharP k 2 := @charP_of_card_eq_prime k _ _ 2 ⟨Nat.prime_two⟩ hk'
  set ε : ZMod 2 ≃+* k := ZMod.ringEquivOfPrime k Nat.prime_two hk' with hε
  set J : Matrix (Fin 4) (Fin 4) k := ε.mapMatrix PresentationLocal.antidiagGram with hJ
  have hJJ : J * J = 1 := by rw [hJ, ← map_mul, antidiagGram_mul_self, map_one]
  set JGL : GL (Fin 4) k := ⟨J, J, hJJ, hJJ⟩ with hJGL
  have hJt : Jᵀ = J := by
    rw [hJ]
    ext i j
    have := congrFun (congrFun antidiagGram_transpose i) j
    simp only [RingEquiv.mapMatrix_apply, transpose_apply, Matrix.map_apply] at this ⊢
    rw [this]
  have hJd : ∀ i, J i i = 0 := by
    intro i
    have hi : ¬ ((i : ℕ) + i = 3) := by omega
    simp only [hJ, RingEquiv.mapMatrix_apply, Matrix.map_apply, PresentationLocal.antidiagGram,
      Matrix.of_apply, hi, ite_false, map_zero]
  have hJalt : (Matrix.toBilin' J).IsAlt := fun x => by
    rw [Matrix.toBilin'_apply']
    exact dotProduct_mulVec_self_eq_zero hJt hJd x
  have hJnd : (Matrix.toBilin' J).Nondegenerate :=
    CatalogueBLinearHigherB.matrixForm_nondegenerate JGL
  obtain ⟨e⟩ := exists_form_isometry B (Matrix.toBilin' J) hB hnd hJalt hJnd
    (by rw [hdim, Module.finrank_fin_fun])
  obtain ⟨φ₁⟩ := nonempty_isometryGroup_mulEquiv_of_isometryEquiv e
  have e₂ : isometryGroup (Matrix.toBilin' J) ≃* matrixIsometryGroup J :=
    (matrixIsometryGroupEquiv JGL).symm
  have e₃ : matrixIsometryGroup J ≃* PresentationLocal.sympFour :=
    ((Units.mapEquiv ε.symm.mapMatrix.toMulEquiv).subgroupMap (matrixIsometryGroup J)).trans
      (MulEquiv.subgroupCongr (map_matrixIsometryGroup_sympFour ε))
  exact ⟨φ₁.trans (e₂.trans e₃)⟩

theorem nonempty_altIsometry_mulEquiv_perm_six {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : BilinForm k V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (hdim : Module.finrank k V = 4) :
    Nonempty (isometryGroup B ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨φ⟩ := nonempty_altIsometry_mulEquiv_sympFour hk B hB hnd hdim
  exact ⟨φ.trans (MulEquiv.ofBijective PresentationLocal.omegaPerm
    ⟨PresentationLocal.omegaPerm_injective, PresentationLocal.omegaPerm_surjective⟩)⟩

end Alternating

end CFSG.ComponentClassification.OutcomeLocal
