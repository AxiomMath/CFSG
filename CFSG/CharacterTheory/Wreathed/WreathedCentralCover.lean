module

public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.CharacterTheory.Wreathed.CentralTwoPowerFieldLift
public import CFSG.CharacterTheory.Semidihedral.MatrixCover

public noncomputable section
namespace CFSG.Wreathed.WreathedCentralCover
universe u v
open Matrix CFSG.Wreathed.CyclicCentralSL2Extension

variable {H : Type v} [Group H]

@[expose] def cyclicPower (tau : H) (m : ℕ) (hm : 0 < m) (htau : tau ^ (2 * m) = 1) :
    Multiplicative (ZMod (2 * m)) →* H := by
  let : NeZero (2 * m) := ⟨by omega⟩
  refine {
    toFun := fun j => tau ^ j.toAdd.val
    map_one' := by simp
    map_mul' := ?_ }
  intro j k
  simp only [toAdd_mul, ZMod.val_add]
  rw [← pow_eq_pow_mod _ htau, pow_add]

theorem cyclicPower_natCast (tau : H) (m : ℕ) (hm : 0 < m) (htau : tau ^ (2 * m) = 1)
    (j : ℕ) : cyclicPower tau m hm htau (Multiplicative.ofAdd (j : ZMod (2 * m))) =
      tau ^ j := by
  let : NeZero (2 * m) := ⟨by omega⟩
  change tau ^ (j : ZMod (2 * m)).val = tau ^ j
  rw [ZMod.val_natCast]
  exact (pow_eq_pow_mod j htau).symm

variable (F : Type u) [Field F]

theorem matrixInclusion_cyclicAction (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (j : Multiplicative (ZMod (2 * m))) (X : SpecialLinearGroup (Fin 2) F) :
    i (cyclicAction F b m hm j X) =
      cyclicPower tau m hm htau j * i X * (cyclicPower tau m hm htau j)⁻¹ := by
  change i ((beta F b ^ j.toAdd.val) X) =
    tau ^ j.toAdd.val * i X * (tau ^ j.toAdd.val)⁻¹
  induction j.toAdd.val generalizing X with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hbeta, pow_succ, _root_.mul_inv_rev]
    group

@[expose] def pairToCover (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹) : PairGroup F b m hm →* H :=
  SemidirectProduct.lift i (cyclicPower tau m hm htau) (fun j => by
    apply MonoidHom.ext
    intro X
    exact matrixInclusion_cyclicAction F b m hm i tau htau hbeta j X)

theorem pairToCover_pair (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    pairToCover F b m hm i tau htau hbeta (pair F b m hm X j) = i X * tau ^ j.val := rfl

theorem pairToCover_diagonalInvolution (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m) :
    pairToCover F b m hm i tau htau hbeta (diagonalInvolution F b m hm) = 1 := by
  rw [diagonalInvolution, pairToCover_pair, hminus,
    ZMod.val_natCast_of_lt (by omega), ← pow_add]
  simpa only [two_mul] using htau

theorem diagonalKernel_le_pairToCover_ker (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (i : SpecialLinearGroup (Fin 2) F →* H)
    (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m) :
    diagonalKernel F b m hm heven ≤ (pairToCover F b m hm i tau htau hbeta).ker :=
  Subgroup.zpowers_le.mpr (pairToCover_diagonalInvolution F b m hm i tau htau hbeta hminus)

@[expose] def quotientToCover (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m) :
    CentralExtension F b m hm heven →* H :=
  QuotientGroup.lift (diagonalKernel F b m hm heven)
    (pairToCover F b m hm i tau htau hbeta)
    (diagonalKernel_le_pairToCover_ker F b m hm heven i tau htau hbeta hminus)

theorem quotientToCover_quotientClass (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    quotientToCover F b m hm heven i tau htau hbeta hminus
      (quotientClass F b m hm heven X j) = i X * tau ^ j.val := rfl

theorem quotientToCover_specialInclusion (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (X : SpecialLinearGroup (Fin 2) F) :
    quotientToCover F b m hm heven i tau htau hbeta hminus
      (specialInclusion F b m hm heven X) = i X := by
  rw [specialInclusion_apply, quotientToCover_quotientClass]
  simp

theorem quotientToCover_cyclicGenerator (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m) :
    quotientToCover F b m hm heven i tau htau hbeta hminus
      (cyclicGenerator F b m hm heven) = tau := by
  rw [cyclicGenerator, quotientToCover_quotientClass]
  have hval : (1 : ZMod (2 * m)).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (show 1 < 2 * m by omega))
  simp only [map_one, one_mul, hval, pow_one]

theorem quotientToCover_fieldAction (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (e : Sigma →* H)
    (hfield : ∀ (sigma : Sigma) X, i (fieldSL F sigma X) = e sigma * i X * (e sigma)⁻¹)
    (hfix : ∀ sigma : Sigma, Commute (e sigma) tau)
    (sigma : Sigma) (q : CentralExtension F b m hm heven) :
    quotientToCover F b m hm heven i tau htau hbeta hminus
      (fieldAction F b m hm heven Sigma hSigma sigma q) =
        e sigma * quotientToCover F b m hm heven i tau htau hbeta hminus q * (e sigma)⁻¹ := by
  induction q using QuotientGroup.induction_on with
  | H v =>
    change quotientToCover F b m hm heven i tau htau hbeta hminus
      (fieldAction F b m hm heven Sigma hSigma sigma
        (quotientClass F b m hm heven v.left v.right.toAdd)) =
        e sigma * quotientToCover F b m hm heven i tau htau hbeta hminus
          (quotientClass F b m hm heven v.left v.right.toAdd) * (e sigma)⁻¹
    rw [fieldAction_quotientClass, quotientToCover_quotientClass,
      quotientToCover_quotientClass, hfield]
    have hc := (hfix sigma).inv_left.pow_right v.right.toAdd.val
    change Commute ((e sigma)⁻¹) (tau ^ v.right.toAdd.val) at hc
    rw [mul_assoc (e sigma * i v.left), hc.eq]
    group

@[expose] def semilinearToCover (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (e : Sigma →* H)
    (hfield : ∀ (sigma : Sigma) X, i (fieldSL F sigma X) = e sigma * i X * (e sigma)⁻¹)
    (hfix : ∀ sigma : Sigma, Commute (e sigma) tau) :
    SemilinearExtension F b m hm heven Sigma hSigma →* H :=
  SemidirectProduct.lift (quotientToCover F b m hm heven i tau htau hbeta hminus) e
    (fun sigma => by
      apply MonoidHom.ext
      intro q
      exact quotientToCover_fieldAction F b m hm heven i tau htau hbeta hminus
        Sigma hSigma e hfield hfix sigma q)

theorem semilinearToCover_formula (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (e : Sigma →* H)
    (hfield : ∀ (sigma : Sigma) X, i (fieldSL F sigma X) = e sigma * i X * (e sigma)⁻¹)
    (hfix : ∀ sigma : Sigma, Commute (e sigma) tau)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (sigma : Sigma) :
    semilinearToCover F b m hm heven i tau htau hbeta hminus Sigma hSigma e hfield hfix
      ⟨quotientClass F b m hm heven X j, sigma⟩ = i X * tau ^ j.val * e sigma := rfl

theorem mem_diagonalKernel_iff (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (v : PairGroup F b m hm) :
    v ∈ diagonalKernel F b m hm heven ↔ v = 1 ∨ v = diagonalInvolution F b m hm := by
  classical
  have horder := diagonalInvolution_order F b m hm heven
  have hfinite : IsOfFinOrder (diagonalInvolution F b m hm) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, diagonalInvolution_square F b m hm heven⟩
  rw [diagonalKernel, hfinite.mem_zpowers_iff_mem_range_orderOf, horder]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with rfl | rfl
    · exact Or.inl (pow_zero _)
    · exact Or.inr (pow_one _)
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, pow_zero _⟩
    · exact ⟨1, by omega, pow_one _⟩

theorem pairToCover_ker (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (hi : Function.Injective i)
    (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (hintersection : ∀ j : ℕ, j < 2 * m → tau ^ j ∈ i.range → j = 0 ∨ j = m) :
    (pairToCover F b m hm i tau htau hbeta).ker = diagonalKernel F b m hm heven := by
  apply le_antisymm
  · intro v hv
    have heq : i v.left * tau ^ v.right.toAdd.val = 1 := hv
    have hmem : tau ^ v.right.toAdd.val ∈ i.range := by
      refine ⟨v.left⁻¹, ?_⟩
      rw [map_inv]
      exact mul_eq_one_iff_inv_eq.mp heq
    let : NeZero (2 * m) := ⟨by omega⟩
    rcases hintersection v.right.toAdd.val (ZMod.val_lt _) hmem with hzero | hmid
    · have hx : v.left = 1 := hi (by simpa only [hzero, pow_zero, mul_one, map_one] using heq)
      have hj : v.right.toAdd = 0 := (ZMod.val_eq_zero _).mp hzero
      rw [mem_diagonalKernel_iff]
      left
      apply SemidirectProduct.ext hx
      exact Multiplicative.toAdd.injective hj
    · have hpower : (tau ^ m)⁻¹ = tau ^ m := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_add]
        simpa only [two_mul] using htau
      have hx : v.left = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
        apply hi
        rw [hminus]
        exact (mul_eq_one_iff_eq_inv.mp (by simpa only [hmid] using heq)).trans hpower
      have hj : v.right.toAdd = (m : ZMod (2 * m)) := by
        apply ZMod.val_injective
        rw [hmid, ZMod.val_natCast_of_lt (by omega)]
      rw [mem_diagonalKernel_iff]
      right
      apply SemidirectProduct.ext hx
      exact Multiplicative.toAdd.injective hj
  · exact diagonalKernel_le_pairToCover_ker F b m hm heven i tau htau hbeta hminus

@[expose] def quotientCoverEquiv (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (hi : Function.Injective i)
    (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (hintersection : ∀ j : ℕ, j < 2 * m → tau ^ j ∈ i.range → j = 0 ∨ j = m)
    (hsurjective : Function.Surjective (pairToCover F b m hm i tau htau hbeta)) :
    CentralExtension F b m hm heven ≃* H :=
  QuotientGroup.liftEquiv (diagonalKernel F b m hm heven) hsurjective
    (pairToCover_ker F b m hm heven i hi tau htau hbeta hminus hintersection).symm

theorem quotientCoverEquiv_quotientClass (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (hi : Function.Injective i)
    (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (hintersection : ∀ j : ℕ, j < 2 * m → tau ^ j ∈ i.range → j = 0 ∨ j = m)
    (hsurjective : Function.Surjective (pairToCover F b m hm i tau htau hbeta))
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    quotientCoverEquiv F b m hm heven i hi tau htau hbeta hminus hintersection hsurjective
      (quotientClass F b m hm heven X j) = i X * tau ^ j.val := rfl

theorem cyclic_involution_intersection_residues [Finite H]
    (tau : H) (m : ℕ) (hm : 0 < m) (horder : orderOf tau = 2 * m)
    (j : ℕ) (hj : j < 2 * m) (hmem : tau ^ j ∈ Subgroup.zpowers (tau ^ m)) :
    j = 0 ∨ j = m := by
  classical
  have hmorder : orderOf (tau ^ m) = 2 := by
    rw [orderOf_pow_of_dvd (by omega : m ≠ 0)
      (horder ▸ (show m ∣ 2 * m from dvd_mul_left m 2)), horder,
      Nat.mul_div_cancel _ hm]
  rw [mem_zpowers_iff_mem_range_orderOf, hmorder] at hmem
  rcases Finset.mem_image.mp hmem with ⟨k, hk, heq⟩
  have hklt : k < 2 := Finset.mem_range.mp hk
  have hcases : k = 0 ∨ k = 1 := by omega
  have htin : j ∈ Set.Iio (orderOf tau) := by simpa only [Set.mem_Iio, horder] using hj
  rcases hcases with rfl | rfl
  · left
    have heq0 : tau ^ j = tau ^ 0 := heq.symm.trans (by simp)
    exact pow_injOn_Iio_orderOf htin (by simpa only [Set.mem_Iio, horder] using (show 0 < 2 * m by omega)) heq0
  · right
    have heqm : tau ^ j = tau ^ m := by simpa only [pow_one] using heq.symm
    exact pow_injOn_Iio_orderOf htin (by simpa only [Set.mem_Iio, horder] using (show m < 2 * m by omega)) heqm


section ActualCompatibleLayer

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.OddFieldLift

theorem slCoordinateAction_range : (slCoordinateAction F).range = coordinateG F := by
  rw [slCoordinateAction, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient_surjective F),
    Subgroup.map_top, coordinatePSLAction_range_eq_G]

theorem compatible_layer_image (M : Subgroup H)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = chi v) :
    M.map chi = coordinateG F := by
  have hhom : chi.comp M.subtype = (slCoordinateAction F).comp eta.toMonoidHom := by
    apply MonoidHom.ext
    intro v
    exact (heta v).symm
  rw [← Subgroup.range_subtype M, ← MonoidHom.range_comp, hhom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr eta.surjective, Subgroup.map_top, slCoordinateAction_range]

theorem compatible_restricted_kernel (M : Subgroup H)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = chi v)
    (x : H) (hx : x ∈ M)
    (hminus : eta ⟨x, hx⟩ = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    (chi.comp M.subtype).ker = Subgroup.zpowers (⟨x, hx⟩ : M) := by
  have hhom : chi.comp M.subtype = (slCoordinateAction F).comp eta.toMonoidHom := by
    apply MonoidHom.ext
    intro v
    exact (heta v).symm
  rw [hhom]
  change (slCoordinateAction F).ker.comap eta.toMonoidHom = _
  rw [slCoordinateAction_ker,
    CFSG.Semidihedral.ProjectiveSL2Cover.center_eq_zpowers_minusIdentity, ← hminus]
  have hmap : (Subgroup.zpowers (⟨x, hx⟩ : M)).map eta.toMonoidHom =
      Subgroup.zpowers (eta ⟨x, hx⟩) := MonoidHom.map_zpowers eta.toMonoidHom (⟨x, hx⟩ : M)
  rw [← hmap]
  exact Subgroup.comap_map_eq_self_of_injective eta.injective _

theorem compatible_kernel_inf_layer (M : Subgroup H)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = chi v)
    (x : H) (hx : x ∈ M)
    (hminus : eta ⟨x, hx⟩ = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    chi.ker ⊓ M = Subgroup.zpowers x := by
  have h := congrArg (Subgroup.map M.subtype)
    (compatible_restricted_kernel F M eta chi heta x hx hminus)
  change (chi.ker.subgroupOf M).map M.subtype =
    (Subgroup.zpowers (⟨x, hx⟩ : M)).map M.subtype at h
  rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers] at h
  exact h

theorem compatible_special_preimage (M : Subgroup H)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = chi v) :
    (coordinateG F).comap chi = chi.ker ⊔ M := by
  rw [← compatible_layer_image F M eta chi heta, Subgroup.comap_map_eq, sup_comm]

theorem slCoordinateAction_matrixConjugation (B : GeneralLinearGroup (Fin 2) F)
    (X : SpecialLinearGroup (Fin 2) F) :
    slCoordinateAction F (matrixConjugation F B X) =
      coordinatePGLAction F (ProjGenLinGroup.mk B) * slCoordinateAction F X *
        (coordinatePGLAction F (ProjGenLinGroup.mk B))⁻¹ := by
  have hsl (Y : SpecialLinearGroup (Fin 2) F) :
      slCoordinateAction F Y =
        coordinatePGLAction F (ProjGenLinGroup.mk (SpecialLinearGroup.toGL Y)) := by
    rw [← ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL]
    rfl
  rw [hsl, matrixConjugation_toGL, map_mul, map_mul, map_inv,
    map_mul, map_mul, map_inv, ← hsl]

theorem compatible_conjugation_matrix [Finite F]
    (p : ℕ) [CharP F p] (hp : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = chi v)
    (h : H) (B : GeneralLinearGroup (Fin 2) F)
    (hh : chi h = coordinatePGLAction F (ProjGenLinGroup.mk B)) (v : M) :
    eta (conjugateIn M h v) = matrixConjugation F B (eta v) := by
  let alpha : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F :=
    eta.toMonoidHom.comp ((conjugateIn M h).toMonoidHom.comp eta.symm.toMonoidHom)
  let beta' : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F :=
    (matrixConjugation F B).toMonoidHom
  have hproj : ∀ X, slCoordinateAction F (alpha X) = slCoordinateAction F (beta' X) := by
    intro X
    change slCoordinateAction F (eta (conjugateIn M h (eta.symm X))) = _
    rw [heta, conjugateIn_coe, map_mul, map_mul, map_inv, hh,
      ← heta (eta.symm X), eta.apply_symm_apply]
    exact (slCoordinateAction_matrixConjugation F B X).symm
  have hab := hom_eq_of_projective_eq p hp alpha beta' hproj
  have heq := DFunLike.congr_fun hab (eta v)
  change eta (conjugateIn M h (eta.symm (eta v))) = _ at heq
  rw [eta.symm_apply_apply] at heq
  exact heq

end ActualCompatibleLayer


section CyclicIntersection

theorem pow_mem_index_two_iff_even (Q : Subgroup H) (hQ : Q.index = 2)
    (tau : H) (htau : tau ∉ Q) (j : ℕ) : tau ^ j ∈ Q ↔ Even j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Q.mul_mem_iff_of_index_two hQ]
    simp only [htau, iff_false, ih]
    exact Nat.even_add_one.symm

theorem cyclic_intersection_of_original_projective [Finite H]
    {Q : Type u} [Group Q] (chi : H →* Q)
    (L : Subgroup Q) (hL : L.index = 2)
    (M : Subgroup H) (hM : M.map chi ≤ L)
    (tau : H) (m : ℕ) (hm : 0 < m) (horder : orderOf tau = 2 * m)
    (houtside : chi tau ∉ L) (hker : chi.ker = Subgroup.zpowers (tau ^ 2))
    (hintersection : chi.ker ⊓ M = Subgroup.zpowers (tau ^ m))
    (j : ℕ) (hj : j < 2 * m) (hjM : tau ^ j ∈ M) : j = 0 ∨ j = m := by
  have hmem : (chi tau) ^ j ∈ L := by
    rw [← map_pow]
    exact hM ⟨tau ^ j, hjM, rfl⟩
  have heven := (pow_mem_index_two_iff_even L hL (chi tau) houtside j).mp hmem
  obtain ⟨r, hr⟩ := heven
  have hker' : tau ^ j ∈ chi.ker := by
    rw [hker, hr, ← two_mul, pow_mul]
    exact (Subgroup.zpowers (tau ^ 2)).pow_mem (Subgroup.mem_zpowers _) r
  have hin : tau ^ j ∈ Subgroup.zpowers (tau ^ m) := hintersection ▸ ⟨hker', hjM⟩
  exact cyclic_involution_intersection_residues tau m hm horder j hj hin

theorem original_cyclic_intersection_residues [Finite H]
    {Q : Type u} [Group Q] (chi : H →* Q)
    (L : Subgroup Q) (hL : L.index = 2)
    (M : Subgroup H) (hM : M.map chi ≤ L)
    (i : SpecialLinearGroup (Fin 2) F →* H) (hi : i.range = M)
    (tau : H) (m : ℕ) (hm : 0 < m) (horder : orderOf tau = 2 * m)
    (houtside : chi tau ∉ L) (hker : chi.ker = Subgroup.zpowers (tau ^ 2))
    (hintersection : chi.ker ⊓ M = Subgroup.zpowers (tau ^ m))
    (j : ℕ) (hj : j < 2 * m) (hji : tau ^ j ∈ i.range) : j = 0 ∨ j = m :=
  cyclic_intersection_of_original_projective chi L hL M hM tau m hm horder houtside
    hker hintersection j hj (hi ▸ hji)

theorem factorization_of_index_two (Q : Subgroup H) (hQ : Q.index = 2)
    (tau : H) (htau : tau ∉ Q) (h : H) :
    h ∈ Q ∨ h * tau⁻¹ ∈ Q := by
  by_cases hh : h ∈ Q
  · exact Or.inl hh
  · right
    rw [Q.mul_mem_iff_of_index_two hQ]
    simp only [hh, Q.inv_mem_iff, htau]

theorem cyclic_kernel_le_pair_range (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹) :
    Subgroup.zpowers (tau ^ 2) ≤ (pairToCover F b m hm i tau htau hbeta).range := by
  apply Subgroup.zpowers_le.mpr
  refine ⟨pair F b m hm 1 (2 : ZMod (2 * m)), ?_⟩
  rw [pairToCover_pair, map_one, one_mul]
  have hperiod := cyclicPower_natCast tau m hm htau 2
  exact hperiod

theorem matrix_layer_le_pair_range (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹) :
    i.range ≤ (pairToCover F b m hm i tau htau hbeta).range := by
  rintro h ⟨X, rfl⟩
  exact ⟨pair F b m hm X 0, by rw [pairToCover_pair]; simp⟩

theorem quotientToCover_surjective (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (hs : Function.Surjective (pairToCover F b m hm i tau htau hbeta)) :
    Function.Surjective (quotientToCover F b m hm heven i tau htau hbeta hminus) := by
  intro h
  obtain ⟨v, hv⟩ := hs h
  exact ⟨QuotientGroup.mk' (diagonalKernel F b m hm heven) v, hv⟩

end CyclicIntersection


theorem pairToCover_surjective_of_original_projective
    {Q : Type u} [Group Q] (chi : H →* Q)
    (L : Subgroup Q) (hL : L.index = 2)
    (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H)
    (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (beta F b X) = tau * i X * tau⁻¹)
    (hiL : i.range.map chi = L)
    (houtside : chi tau ∉ L)
    (hker : chi.ker = Subgroup.zpowers (tau ^ 2)) :
    Function.Surjective (pairToCover F b m hm i tau htau hbeta) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  let f := pairToCover F b m hm i tau htau hbeta
  have hkernel : chi.ker ≤ f.range := by
    rw [hker]
    exact cyclic_kernel_le_pair_range F b m hm i tau htau hbeta
  have hmatrix : i.range ≤ f.range := matrix_layer_le_pair_range F b m hm i tau htau hbeta
  have hpre : L.comap chi ≤ f.range := by
    rw [← hiL, Subgroup.comap_map_eq]
    exact sup_le hmatrix hkernel
  have ht : tau ∈ f.range := by
    refine ⟨pair F b m hm 1 (1 : ZMod (2 * m)), ?_⟩
    change i 1 * tau ^ (1 : ZMod (2 * m)).val = tau
    rw [map_one, one_mul]
    have hval : (1 : ZMod (2 * m)).val = 1 := by
      simpa only [Nat.cast_one] using
        (ZMod.val_natCast_of_lt (show 1 < 2 * m by omega))
    rw [hval, pow_one]
  intro h
  change h ∈ f.range
  rcases factorization_of_index_two L hL (chi tau) houtside (chi h) with hh | hh
  · exact hpre hh
  · have hp : h * tau⁻¹ ∈ L.comap chi := by
      change chi (h * tau⁻¹) ∈ L
      rwa [map_mul, map_inv]
    have hf := f.range.mul_mem (hpre hp) ht
    simpa only [inv_mul_cancel_right] using hf


section OriginalSquareRoot

open CFSG.Wreathed.WreathCentralSquare
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.OddFieldLift
open CFSG.Wreathed.CentralTwoPowerFieldLift
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem two_element_mem_of_odd_index {Q : Type u} [Group Q]
    (N : Subgroup Q) [N.Normal] (hodd : Odd N.index)
    (g : Q) (hg : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ∈ N := by
  obtain ⟨k, hk⟩ := hg
  let P := Subgroup.zpowers g
  have hP : IsPGroup 2 P := IsPGroup.of_card_dvd_pow (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk)
  let t := (hP.powEquiv ((Nat.coprime_two_left).mpr hodd)).symm
    (⟨g, Subgroup.mem_zpowers g⟩ : P)
  have ht : (t : Q) ^ N.index = g := congrArg Subtype.val
    ((hP.powEquiv ((Nat.coprime_two_left).mpr hodd)).apply_symm_apply
      (⟨g, Subgroup.mem_zpowers g⟩ : P))
  rw [← ht]
  exact N.pow_index_mem t

theorem original_two_element_linear [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (g : Gamma F Sigma) (hg : ∃ k : ℕ, g ^ 2 ^ k = 1) :
    g ∈ gammaLinear F Sigma := by
  apply two_element_mem_of_odd_index (gammaLinear F Sigma) _ g hg
  rwa [CFSG.Wreathed.CentralTwoPowerFieldLift.gammaLinear_index]

theorem original_kernel_card (n : ℕ) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    {Q : Type u} [Group Q] (pi : H →* Q) (hker : pi.ker = modelCenter S e) :
    Nat.card pi.ker = 2 ^ n := by
  rw [hker, modelCenter, Original.Z, MonoidHom.map_zpowers, Nat.card_zpowers,
    orderOf_injective _ (wreathModelHom_injective S e), Original.orderOf_a]

theorem original_root_projective_outer [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    (pi : H →* Gamma F Sigma) (hker : pi.ker = modelCenter S e)
    (M : Subgroup H) [M.Normal]
    (hSM : (S : Subgroup H) ⊓ M = modelY S e)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v) :
    pi (actualRoot S e) ∈ gammaLinear F Sigma ∧
      coordinateProjection F Sigma pi (actualRoot S e) ∉ coordinateG F ∧
      orderOf (coordinateProjection F Sigma pi (actualRoot S e)) = 2 := by
  let chi := coordinateProjection F Sigma pi
  have hout : chi (actualRoot S e) ∉ coordinateG F := by
    intro hx
    have hpre := compatible_special_preimage F M eta chi heta
    have hmem : actualRoot S e ∈ chi.ker ⊔ M := by
      rw [← hpre]
      exact hx
    have hchiker : chi.ker = pi.ker := by
      change ((coordinateE F).subtype.comp ((Gamma F Sigma).subtype.comp pi)).ker = pi.ker
      rw [MonoidHom.ker_comp_of_injective _ _ (coordinateE F).subtype_injective,
        MonoidHom.ker_comp_of_injective _ _ (Gamma F Sigma).subtype_injective]
    rw [hchiker, hker] at hmem
    exact actualRoot_not_mem_center_sup_normal n hn S e M hSM hmem
  have hsq : chi (actualRoot S e) ^ 2 = 1 := by
    rw [← map_pow, actualRoot_sq]
    have hle : pi.ker ≤ chi.ker := by
      intro x hx
      change ((coordinateE F).subtype.comp ((Gamma F Sigma).subtype.comp pi)) x = 1
      have heq : pi x = 1 := hx
      change ((coordinateE F).subtype.comp (Gamma F Sigma).subtype) (pi x) = 1
      rw [heq, map_one]
    apply hle
    rw [hker]
    exact ⟨Original.a (2 ^ n), Subgroup.mem_zpowers _, rfl⟩
  have hne : chi (actualRoot S e) ≠ 1 := fun h => hout (h ▸ (coordinateG F).one_mem)
  have hg : ∃ k : ℕ, (pi (actualRoot S e)) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨actualRoot S e, actualRoot_mem_sylow S e⟩
    refine ⟨k, ?_⟩
    rw [← map_pow, show actualRoot S e ^ 2 ^ k = 1 from congrArg Subtype.val hk, map_one]
  exact ⟨original_two_element_linear F Sigma hd _ hg, hout, orderOf_eq_prime hsq hne⟩

end OriginalSquareRoot


open CFSG.Wreathed.WreathCentralSquare
open CFSG.Semidihedral.OddFieldLift
open CFSG.Wreathed.CentralTwoPowerFieldLift
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.MatrixCover
open CFSG.Semidihedral.MatrixCoverData

theorem fixed_projective_lift_centralizes_original_E [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (b : (FixedField F Sigma)ˣ) (t : H)
    (ht : coordinateProjection F Sigma pi t =
      (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F))) :
    t ∈ Subgroup.centralizer
      (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral : Set H) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro e he
  let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral
  let ee : E0 := ⟨e, he⟩
  let sigma := CFSG.Wreathed.CentralTwoPowerFieldLift.EEquivField F Sigma pi hpi hcentral hK hd ee
  have heimage : coordinateProjection F Sigma pi e = fieldExtension F sigma := by
    have h := CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective
      F Sigma pi hpi hcentral hK hd sigma
    change coordinateProjection F Sigma pi
      ((CFSG.Wreathed.CentralTwoPowerFieldLift.EEquivField F Sigma pi hpi hcentral hK hd).symm sigma) = _ at h
    rw [MulEquiv.symm_apply_apply] at h
    exact h
  have hc : Commute (pi t) (pi e) := by
    change pi t * pi e = pi e * pi t
    apply quotient_coordinates_injective F Sigma
    change coordinateProjection F Sigma pi t * coordinateProjection F Sigma pi e =
      coordinateProjection F Sigma pi e * coordinateProjection F Sigma pi t
    rw [ht, heimage]
    exact (fixed_jProjective_commute F Sigma b sigma).symm.eq
  have hed : e ^ Nat.card Sigma = 1 :=
    (CFSG.Wreathed.CentralTwoPowerFieldLift.mem_E F Sigma pi hcentral e).mp he |>.2
  exact (commute_of_quotient_commute_of_odd_power pi hcentral hK (Nat.card Sigma)
    hd t e hed hc).symm.eq

theorem exists_original_conjugator_to_fixed_j [Finite F]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (r : H) (hrD : coordinateProjection F Sigma pi r ∈ coordinateD F)
    (hrout : coordinateProjection F Sigma pi r ∉ coordinateG F)
    (hrorder : orderOf (coordinateProjection F Sigma pi r) = 2)
    (b : Fˣ) (hb : ¬IsSquare b) :
    ∃ h : H, coordinateProjection F Sigma pi (h * r * h⁻¹) =
      (jProjective F b : Equiv.Perm (Omega F)) := by
  let v : coordinateD F := ⟨coordinateProjection F Sigma pi r, hrD⟩
  have hv : (v : Equiv.Perm (Omega F)) = coordinateProjection F Sigma pi r := rfl
  have hvo : orderOf v = 2 := by
    rw [← orderOf_injective _ (coordinateD F).subtype_injective]
    change orderOf (v : Equiv.Perm (Omega F)) = 2
    rw [hv]
    exact hrorder
  obtain ⟨d, hdconj⟩ :=
    CFSG.Semidihedral.ProjectiveNonsquareInvolutions.projective_nonsquare_involutions_are_conjugate
      F hF b hb v (by rw [hv]; exact hrout) hvo
  let de : coordinateE F := ⟨d.val, coordinateD_le_E F d.property⟩
  have hdlinear : de ∈ linearLayer F := d.property
  let dg : Gamma F Sigma :=
    ⟨de, (show linearLayer F ≤ Gamma F Sigma from le_sup_left) hdlinear⟩
  obtain ⟨h, hh⟩ := hpi dg
  refine ⟨h, ?_⟩
  rw [map_mul, map_mul, map_inv]
  have hdh : coordinateProjection F Sigma pi h = (d : Equiv.Perm (Omega F)) :=
    congrArg (fun g : Gamma F Sigma => ((g : coordinateE F) : Equiv.Perm (Omega F))) hh
  rw [hdh]
  have heq := congrArg Subtype.val hdconj
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hv] using heq

theorem exists_original_fixed_j_square_root [Finite F] [Finite H]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hker : pi.ker = modelCenter S e)
    (hcentral : pi.ker ≤ Subgroup.center H)
    (M : Subgroup H) [M.Normal]
    (hSM : (S : Subgroup H) ⊓ M = modelY S e)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (b : (FixedField F Sigma)ˣ) (hb : ¬IsSquare b) :
    ¬IsSquare (fixedUnit F Sigma b) ∧
      ∃ t : H,
        t ∈ Subgroup.centralizer
          (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral : Set H) ∧
        t ^ 2 = wreathModelHom S e (Original.a (2 ^ n)) ∧
        t ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)) ∧
        orderOf t = 2 * 2 ^ n ∧
        coordinateProjection F Sigma pi t =
          (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)) := by
  have hbF := fixed_nonsquare_retained F Sigma hd b hb
  have hr := original_root_projective_outer F Sigma hd n hn S e pi hker M hSM eta heta
  have hD : coordinateProjection F Sigma pi (actualRoot S e) ∈ coordinateD F := by
    have h := (gammaLinearEquiv F Sigma ⟨pi (actualRoot S e), hr.1⟩).property
    rw [gammaLinearEquiv_coe] at h
    exact h
  obtain ⟨h, hh⟩ := exists_original_conjugator_to_fixed_j F hF Sigma pi hpi
    (actualRoot S e) hD hr.2.1 hr.2.2 (fixedUnit F Sigma b) hbF
  let t := conjugateRoot S e h
  have htimage : coordinateProjection F Sigma pi t =
      (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)) := hh
  have hAcentral : modelCenter S e ≤ Subgroup.center H := by
    rw [← hker]
    exact hcentral
  have hK : IsPGroup 2 pi.ker := kernel_isPGroup_of_card pi ⟨n, original_kernel_card n S e pi hker⟩
  exact ⟨hbF, t,
    fixed_projective_lift_centralizes_original_E F Sigma hd pi hpi hcentral hK b t htimage,
    conjugateRoot_sq S e h hAcentral,
    conjugateRoot_pow_modulus n (by omega) S e h hAcentral,
    conjugateRoot_orderOf n hn S e h, htimage⟩

section FullSemilinearMaps

theorem pairToCover_range_of_original_projective
    {Q : Type u} [Group Q] (chi : H →* Q)
    (L K : Subgroup Q) (hLK : L ≤ K) (hL : L.relIndex K = 2)
    (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (i : SpecialLinearGroup (Fin 2) F →* H)
    (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (CFSG.Wreathed.CyclicCentralSL2Extension.beta F b X) = tau * i X * tau⁻¹)
    (hiL : i.range.map chi = L)
    (houtside : chi tau ∉ L) (htK : chi tau ∈ K)
    (hker : chi.ker = Subgroup.zpowers (tau ^ 2)) :
    (pairToCover F b m hm i tau htau hbeta).range = K.comap chi := by
  let f := pairToCover F b m hm i tau htau hbeta
  have hkernel : chi.ker ≤ f.range := by
    rw [hker]
    exact cyclic_kernel_le_pair_range F b m hm i tau htau hbeta
  have hmatrix : i.range ≤ f.range :=
    matrix_layer_le_pair_range F b m hm i tau htau hbeta
  have hpre : L.comap chi ≤ f.range := by
    rw [← hiL, Subgroup.comap_map_eq]
    exact sup_le hmatrix hkernel
  have ht : tau ∈ f.range := by
    refine ⟨pair F b m hm 1 (1 : ZMod (2 * m)), ?_⟩
    change i 1 * tau ^ (1 : ZMod (2 * m)).val = tau
    rw [map_one, one_mul]
    have hval : (1 : ZMod (2 * m)).val = 1 := by
      simpa only [Nat.cast_one] using
        ZMod.val_natCast_of_lt (show 1 < 2 * m by omega)
    rw [hval, pow_one]
  have hiK : ∀ X, chi (i X) ∈ K := by
    intro X
    apply hLK
    rw [← hiL]
    exact Subgroup.mem_map_of_mem chi ⟨X, rfl⟩
  apply le_antisymm
  · rintro h ⟨v, rfl⟩
    change chi (i v.left * tau ^ v.right.toAdd.val) ∈ K
    rw [map_mul, map_pow]
    exact K.mul_mem (hiK _) (K.pow_mem htK _)
  · intro h hh
    let tK : K := ⟨chi tau, htK⟩
    have hindex : (L.subgroupOf K).index = 2 := hL
    have htout : tK ∉ L.subgroupOf K := houtside
    rcases factorization_of_index_two (L.subgroupOf K) hindex tK htout
      (⟨chi h, hh⟩ : K) with hin | hin
    · exact hpre hin
    · have hin' : h * tau⁻¹ ∈ L.comap chi := by
        change chi (h * tau⁻¹) ∈ L
        rw [map_mul, map_inv]
        exact hin
      simpa only [inv_mul_cancel_right] using f.range.mul_mem (hpre hin') ht

theorem quotientToCover_range (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (CFSG.Wreathed.CyclicCentralSL2Extension.beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m) :
    (quotientToCover F b m hm heven i tau htau hbeta hminus).range =
      (pairToCover F b m hm i tau htau hbeta).range := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H v => exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨QuotientGroup.mk' (diagonalKernel F b m hm heven) v, rfl⟩

theorem quotientToCover_injective (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (hi : Function.Injective i)
    (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (CFSG.Wreathed.CyclicCentralSL2Extension.beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (hintersection : ∀ j : ℕ, j < 2 * m → tau ^ j ∈ i.range → j = 0 ∨ j = m) :
    Function.Injective (quotientToCover F b m hm heven i tau htau hbeta hminus) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (pairToCover_ker F b m hm heven i hi tau htau hbeta hminus hintersection).symm

theorem semilinearToCover_bijective_of_complement
    (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (i : SpecialLinearGroup (Fin 2) F →* H) (tau : H) (htau : tau ^ (2 * m) = 1)
    (hbeta : ∀ X, i (CFSG.Wreathed.CyclicCentralSL2Extension.beta F b X) = tau * i X * tau⁻¹)
    (hminus : i (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = tau ^ m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (e : Sigma →* H)
    (hfield : ∀ (sigma : Sigma) X, i (fieldSL F sigma X) = e sigma * i X * (e sigma)⁻¹)
    (hfix : ∀ sigma : Sigma, Commute (e sigma) tau)
    (hf : Function.Injective (quotientToCover F b m hm heven i tau htau hbeta hminus))
    (he : Function.Injective e)
    (hcomp : (quotientToCover F b m hm heven i tau htau hbeta hminus).range.IsComplement'
      e.range) :
    Function.Bijective (semilinearToCover F b m hm heven i tau htau hbeta hminus
      Sigma hSigma e hfield hfix) := by
  let f := quotientToCover F b m hm heven i tau htau hbeta hminus
  have hbij : Function.Bijective (fun p : f.range × e.range => (p.1 : H) * p.2) := hcomp
  constructor
  · intro x y hxy
    have hxy' : f x.left * e x.right = f y.left * e y.right := hxy
    have hh := hbij.1 (a₁ := (⟨f x.left, ⟨x.left, rfl⟩⟩, ⟨e x.right, ⟨x.right, rfl⟩⟩))
      (a₂ := (⟨f y.left, ⟨y.left, rfl⟩⟩, ⟨e y.right, ⟨y.right, rfl⟩⟩)) hxy'
    apply SemidirectProduct.ext
    · apply hf
      exact congrArg (fun p : f.range × e.range => (p.1 : H)) hh
    · apply he
      exact congrArg (fun p : f.range × e.range => (p.2 : H)) hh
  · intro h
    obtain ⟨p, hp⟩ := hbij.2 h
    obtain ⟨q, hq⟩ := p.1.property
    obtain ⟨sigma, hsigma⟩ := p.2.property
    refine ⟨⟨q, sigma⟩, ?_⟩
    change f q * e sigma = h
    rw [hq, hsigma]
    exact hp

end FullSemilinearMaps

section OriginalCoverAssembly

theorem layerLift_range (M : Subgroup H)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F) :
    (CFSG.Semidihedral.MatrixCover.layerLift F M eta).range = M := by
  rw [CFSG.Semidihedral.MatrixCover.layerLift, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr eta.symm.surjective, Subgroup.map_top, Subgroup.range_subtype]

theorem coordinate_special_relIndex_linear [Finite F]
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F)) :
    (coordinateG F).relIndex (coordinateD F) = 2 := by
  have h := Subgroup.index_map_equiv
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range (pglEquivCoordinateD F)
  change ((ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.map
    (pglEquivCoordinateD F).toMonoidHom).index = _ at h
  rw [pglPSLRange_map_coordinateD] at h
  exact h.trans (CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF)

theorem original_linear_preimage_eq [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma) :
    (coordinateD F).comap (coordinateProjection F Sigma pi) = H1 F Sigma pi := by
  ext h
  rfl

theorem original_layerLift_beta [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = chi v)
    (b : Fˣ) (t : H)
    (ht : chi t = (jProjective F b : Equiv.Perm (Omega F)))
    (X : SpecialLinearGroup (Fin 2) F) :
    CFSG.Semidihedral.MatrixCover.layerLift F M eta
        (CFSG.Wreathed.CyclicCentralSL2Extension.beta F b X) =
      t * CFSG.Semidihedral.MatrixCover.layerLift F M eta X * t⁻¹ := by
  have hproj : chi t = coordinatePGLAction F (ProjGenLinGroup.mk (nonsquareMatrix F b)) := ht
  have h := compatible_conjugation_matrix F p hpodd M eta chi heta t
    (nonsquareMatrix F b) hproj (eta.symm X)
  rw [eta.apply_symm_apply] at h
  have heq : eta.symm (CFSG.Wreathed.CyclicCentralSL2Extension.beta F b X) =
      conjugateIn M t (eta.symm X) := by
    apply eta.injective
    rw [eta.apply_symm_apply]
    exact h.symm
  change (eta.symm (CFSG.Wreathed.CyclicCentralSL2Extension.beta F b X) : H) = _
  rw [heq, conjugateIn_coe]
  rfl

@[expose] def originalFieldLift [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma)) : Sigma →* H :=
  (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral).subtype.comp
    (CFSG.Wreathed.CentralTwoPowerFieldLift.EEquivField F Sigma pi hpi hcentral hK hd).symm.toMonoidHom

theorem originalFieldLift_apply [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma)) (sigma : Sigma) :
    originalFieldLift F Sigma pi hpi hcentral hK hd sigma =
      CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma F Sigma pi hpi hcentral hK hd sigma := rfl

theorem originalFieldLift_injective [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma)) :
    Function.Injective (originalFieldLift F Sigma pi hpi hcentral hK hd) :=
  Subtype.val_injective.comp
    (CFSG.Wreathed.CentralTwoPowerFieldLift.EEquivField F Sigma pi hpi hcentral hK hd).symm.injective

theorem originalFieldLift_range [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma)) :
    (originalFieldLift F Sigma pi hpi hcentral hK hd).range =
      CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral := by
  rw [originalFieldLift, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr
      (CFSG.Wreathed.CentralTwoPowerFieldLift.EEquivField F Sigma pi hpi hcentral hK hd).symm.surjective,
    Subgroup.map_top, Subgroup.range_subtype]

theorem original_layerLift_field [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (sigma : Sigma) (X : SpecialLinearGroup (Fin 2) F) :
    CFSG.Semidihedral.MatrixCover.layerLift F M eta (fieldSL F sigma X) =
      originalFieldLift F Sigma pi hpi hcentral hK hd sigma *
        CFSG.Semidihedral.MatrixCover.layerLift F M eta X *
          (originalFieldLift F Sigma pi hpi hcentral hK hd sigma)⁻¹ :=
  CFSG.Semidihedral.MatrixCover.layerLift_field_conjugation F p hpodd M eta
    (coordinateProjection F Sigma pi) heta _ sigma
    (CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective F Sigma pi hpi hcentral hK hd sigma) X

end OriginalCoverAssembly

theorem cyclic_intersection_of_original_relative_projective [Finite H]
    {Q : Type u} [Group Q] (chi : H →* Q)
    (L K : Subgroup Q) (hL : L.relIndex K = 2)
    (M : Subgroup H) (hM : M.map chi ≤ L)
    (tau : H) (htK : chi tau ∈ K)
    (m : ℕ) (hm : 0 < m) (horder : orderOf tau = 2 * m)
    (houtside : chi tau ∉ L) (hker : chi.ker = Subgroup.zpowers (tau ^ 2))
    (hintersection : chi.ker ⊓ M = Subgroup.zpowers (tau ^ m))
    (j : ℕ) (hj : j < 2 * m) (hjM : tau ^ j ∈ M) : j = 0 ∨ j = m := by
  let tK : K := ⟨chi tau, htK⟩
  have hmem : tK ^ j ∈ L.subgroupOf K := by
    change (chi tau) ^ j ∈ L
    rw [← map_pow]
    exact hM ⟨tau ^ j, hjM, rfl⟩
  have heven := (pow_mem_index_two_iff_even (L.subgroupOf K) hL tK houtside j).mp hmem
  obtain ⟨r, hr⟩ := heven
  have hker' : tau ^ j ∈ chi.ker := by
    rw [hker, hr, ← two_mul, pow_mul]
    exact (Subgroup.zpowers (tau ^ 2)).pow_mem (Subgroup.mem_zpowers _) r
  have hin : tau ^ j ∈ Subgroup.zpowers (tau ^ m) := hintersection ▸ ⟨hker', hjM⟩
  exact cyclic_involution_intersection_residues tau m hm horder j hj hin

theorem original_x_mem_layer (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (M : Subgroup H)
    (hSM : (S : Subgroup H) ⊓ M = modelY S e) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ M := by
  have hx : wreathModelHom S e (Original.x (2 ^ n)) ∈ modelY S e :=
    ⟨Original.x (2 ^ n), original_x_mem_Y n hn, rfl⟩
  exact (hSM.symm ▸ hx).2

@[expose] def originalLayerX (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (M : Subgroup H)
    (hSM : (S : Subgroup H) ⊓ M = modelY S e) : M :=
  ⟨wreathModelHom S e (Original.x (2 ^ n)), original_x_mem_layer n hn S e M hSM⟩

theorem original_layerLift_minus (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (M : Subgroup H)
    (hSM : (S : Subgroup H) ⊓ M = modelY S e)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (hminus : eta (originalLayerX n hn S e M hSM) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    CFSG.Semidihedral.MatrixCover.layerLift F M eta
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
        wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [CFSG.Semidihedral.MatrixCover.layerLift_apply, ← hminus, eta.symm_apply_apply]
  rfl

section OriginalSemilinearConstruction

theorem original_fixed_parameter [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (b : (FixedField F Sigma)ˣ) :
    ∀ sigma ∈ Sigma, sigma (fixedUnit F Sigma b : F) = (fixedUnit F Sigma b : F) := by
  intro sigma hsigma
  rw [fixedUnit_coe]
  exact (b : FixedField F Sigma).property ⟨sigma, hsigma⟩

theorem original_kernel_isPGroup [Finite H] (n : ℕ) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    {Q : Type u} [Group Q] (pi : H →* Q) (hker : pi.ker = modelCenter S e) :
    IsPGroup 2 pi.ker :=
  kernel_isPGroup_of_card pi ⟨n, original_kernel_card n S e pi hker⟩

theorem original_semilinear_map_bijective [Finite F] [Finite H]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hker : pi.ker = modelCenter S e) (hcentral : pi.ker ≤ Subgroup.center H)
    (M : Subgroup H) [M.Normal] (hSM : (S : Subgroup H) ⊓ M = modelY S e)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (hminus : eta (originalLayerX n hn S e M hSM) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F)
    (b : (FixedField F Sigma)ˣ) (hb : ¬IsSquare (fixedUnit F Sigma b))
    (tau : H)
    (hsquare : tau ^ 2 = wreathModelHom S e (Original.a (2 ^ n)))
    (hpower : tau ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)))
    (horder : orderOf tau = 2 * 2 ^ n)
    (himage : coordinateProjection F Sigma pi tau =
      (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F))) :
    let m := 2 ^ n
    let hm : 0 < m := by positivity
    let heven : Even m := even_two.pow_of_ne_zero (by omega)
    let hK := original_kernel_isPGroup n S e pi hker
    let i := CFSG.Semidihedral.MatrixCover.layerLift F M eta
    let ht : tau ^ (2 * m) = 1 := horder ▸ pow_orderOf_eq_one tau
    let hbeta := original_layerLift_beta F p hpodd M eta
      (coordinateProjection F Sigma pi) heta (fixedUnit F Sigma b) tau himage
    let hiMinus := (original_layerLift_minus F n hn S e M hSM eta hminus).trans hpower.symm
    let eField := originalFieldLift F Sigma pi hpi hcentral hK hd
    let hfield := original_layerLift_field F p hpodd M eta Sigma pi hpi hcentral hK hd heta
    let hfix : ∀ sigma : Sigma, Commute (eField sigma) tau := by
      intro sigma
      exact Subgroup.mem_centralizer_iff.mp
        (fixed_projective_lift_centralizes_original_E F Sigma hd pi hpi hcentral hK b tau himage)
        (eField sigma) (originalFieldLift_range F Sigma pi hpi hcentral hK hd ▸
          (show eField sigma ∈ eField.range from ⟨sigma, rfl⟩))
    Function.Bijective (semilinearToCover F (fixedUnit F Sigma b) m hm heven i tau ht
      hbeta hiMinus Sigma (original_fixed_parameter F Sigma b) eField hfield hfix) := by
  dsimp only
  let m := 2 ^ n
  have hm : 0 < m := by positivity
  have heven : Even m := even_two.pow_of_ne_zero (by omega)
  let hK := original_kernel_isPGroup n S e pi hker
  let i := CFSG.Semidihedral.MatrixCover.layerLift F M eta
  let chi := coordinateProjection F Sigma pi
  have ht : tau ^ (2 * m) = 1 := horder ▸ pow_orderOf_eq_one tau
  have hbeta := original_layerLift_beta F p hpodd M eta chi heta (fixedUnit F Sigma b) tau himage
  have hiMinus := (original_layerLift_minus F n hn S e M hSM eta hminus).trans hpower.symm
  let eField := originalFieldLift F Sigma pi hpi hcentral hK hd
  have hfield := original_layerLift_field F p hpodd M eta Sigma pi hpi hcentral hK hd heta
  have hfix : ∀ sigma : Sigma, Commute (eField sigma) tau := by
    intro sigma
    exact Subgroup.mem_centralizer_iff.mp
      (fixed_projective_lift_centralizes_original_E F Sigma hd pi hpi hcentral hK b tau himage)
      (eField sigma) (originalFieldLift_range F Sigma pi hpi hcentral hK hd ▸
        (show eField sigma ∈ eField.range from ⟨sigma, rfl⟩))
  have hiRange : i.range = M := layerLift_range F M eta
  have hiImage : i.range.map chi = coordinateG F := by
    rw [hiRange]
    exact compatible_layer_image F M eta chi heta
  have hchiKer : chi.ker = Subgroup.zpowers (tau ^ 2) := by
    rw [CFSG.Semidihedral.MatrixCover.coordinateProjection_ker, hker, hsquare,
      modelCenter, Original.Z, MonoidHom.map_zpowers]
  have htOut : chi tau ∉ coordinateG F := by
    rw [himage]
    exact (CFSG.Semidihedral.ProjectiveNonsquareInvolutions.jProjective_outer_involution
      F (fixedUnit F Sigma b) hb).1
  have htD : chi tau ∈ coordinateD F := by
    rw [himage]
    exact (jProjective F (fixedUnit F Sigma b)).property
  have hkerInf : chi.ker ⊓ M = Subgroup.zpowers (tau ^ m) := by
    rw [hpower]
    exact compatible_kernel_inf_layer F M eta chi heta _
      (original_x_mem_layer n hn S e M hSM) hminus
  have hintersection : ∀ j : ℕ, j < 2 * m → tau ^ j ∈ i.range → j = 0 ∨ j = m := by
    intro j hj hjMem
    apply cyclic_intersection_of_original_relative_projective chi (coordinateG F)
      (coordinateD F) (coordinate_special_relIndex_linear F hF) M
      (by rw [compatible_layer_image F M eta chi heta]) tau htD m hm horder
      htOut hchiKer hkerInf j hj
    rwa [hiRange] at hjMem
  have hquotRange : (quotientToCover F (fixedUnit F Sigma b) m hm heven i tau ht
      hbeta hiMinus).range = H1 F Sigma pi := by
    rw [quotientToCover_range]
    rw [pairToCover_range_of_original_projective F chi (coordinateG F) (coordinateD F)
      (coordinateG_le_D F) (coordinate_special_relIndex_linear F hF)
      (fixedUnit F Sigma b) m hm i tau ht hbeta hiImage htOut htD hchiKer]
    exact original_linear_preimage_eq F Sigma pi
  apply semilinearToCover_bijective_of_complement F (fixedUnit F Sigma b) m hm heven
    i tau ht hbeta hiMinus Sigma (original_fixed_parameter F Sigma b) eField hfield hfix
    (quotientToCover_injective F (fixedUnit F Sigma b) m hm heven i
      (CFSG.Semidihedral.MatrixCover.layerLift_injective F M eta) tau ht hbeta hiMinus hintersection)
    (originalFieldLift_injective F Sigma pi hpi hcentral hK hd)
  rw [hquotRange, originalFieldLift_range]
  exact H_isComplement F Sigma pi hpi hcentral hK hd

end OriginalSemilinearConstruction

section OriginalFixedMatrices

theorem original_eta_field_conjugation [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (sigma : Sigma) (v : M) :
    eta (conjugateIn M (originalFieldLift F Sigma pi hpi hcentral hK hd sigma) v) =
      fieldSL F sigma (eta v) := by
  have h := original_layerLift_field F p hpodd M eta Sigma pi hpi hcentral hK hd heta
    sigma (eta v)
  change (eta.symm (fieldSL F sigma (eta v)) : H) = _ at h
  rw [CFSG.Semidihedral.MatrixCover.layerLift_apply, eta.symm_apply_apply] at h
  have hv : eta.symm (fieldSL F sigma (eta v)) =
      conjugateIn M (originalFieldLift F Sigma pi hpi hcentral hK hd sigma) v :=
    Subtype.ext h
  rw [← hv, eta.apply_symm_apply]

theorem original_layer_centralizer_iff_fixed_entries [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (v : M) :
    v ∈ (Subgroup.centralizer
      (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral : Set H)).subgroupOf M ↔
      eta v ∈ fixedEntrySL2 F Sigma := by
  rw [mem_fixedEntrySL2]
  constructor
  · intro hv sigma
    have hcomm : originalFieldLift F Sigma pi hpi hcentral hK hd sigma * (v : H) =
        (v : H) * originalFieldLift F Sigma pi hpi hcentral hK hd sigma :=
      Subgroup.mem_centralizer_iff.mp hv _
        (originalFieldLift_range F Sigma pi hpi hcentral hK hd ▸
          (show originalFieldLift F Sigma pi hpi hcentral hK hd sigma ∈
            (originalFieldLift F Sigma pi hpi hcentral hK hd).range from ⟨sigma, rfl⟩))
    have hconj : conjugateIn M (originalFieldLift F Sigma pi hpi hcentral hK hd sigma) v = v := by
      apply Subtype.ext
      rw [conjugateIn_coe, hcomm]
      group
    have h := original_eta_field_conjugation F p hpodd M eta Sigma pi hpi hcentral hK hd
      heta sigma v
    rw [hconj] at h
    exact h.symm
  · intro hv
    apply Subgroup.mem_centralizer_iff.mpr
    intro e he
    have heRange : e ∈ (originalFieldLift F Sigma pi hpi hcentral hK hd).range :=
      originalFieldLift_range F Sigma pi hpi hcentral hK hd ▸ he
    obtain ⟨sigma, rfl⟩ := heRange
    have hconj : conjugateIn M (originalFieldLift F Sigma pi hpi hcentral hK hd sigma) v = v := by
      apply eta.injective
      rw [original_eta_field_conjugation F p hpodd M eta Sigma pi hpi hcentral hK hd heta]
      exact hv sigma
    have h := congrArg Subtype.val hconj
    change originalFieldLift F Sigma pi hpi hcentral hK hd sigma * (v : H) *
      (originalFieldLift F Sigma pi hpi hcentral hK hd sigma)⁻¹ = (v : H) at h
    exact (mul_inv_eq_iff_eq_mul.mp h)

theorem original_eta_centralizer_image [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v) :
    ((Subgroup.centralizer
      (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral : Set H)).subgroupOf M).map
      eta.toMonoidHom = fixedEntrySL2 F Sigma := by
  ext X
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (original_layer_centralizer_iff_fixed_entries F p hpodd M eta Sigma pi hpi hcentral
      hK hd heta v).mp hv
  · intro hX
    refine ⟨eta.symm X, ?_, eta.apply_symm_apply X⟩
    apply (original_layer_centralizer_iff_fixed_entries F p hpodd M eta Sigma pi hpi hcentral
      hK hd heta _).mpr
    rwa [eta.apply_symm_apply]

end OriginalFixedMatrices

section TransportedQuotient

theorem matrixLayer_image_of_values
    (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (Phi : SemilinearExtension F b m hm heven Sigma hSigma ≃* H)
    (i : SpecialLinearGroup (Fin 2) F →* H)
    (hvalues : ∀ X, Phi (CFSG.Wreathed.CentralSL2Abelianization.matrixInclusion
      F b m hm heven Sigma hSigma X) = i X) :
    (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F b m hm heven Sigma hSigma).map
      Phi.toMonoidHom = i.range := by
  rw [CFSG.Wreathed.CentralSL2Abelianization.matrixLayer, ← MonoidHom.range_comp]
  congr 1
  exact MonoidHom.ext hvalues

@[expose] def originalMatrixQuotientEquiv
    (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (Phi : SemilinearExtension F b m hm heven Sigma hSigma ≃* H)
    (M : Subgroup H) [M.Normal]
    (hM : (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F b m hm heven Sigma hSigma).map
      Phi.toMonoidHom = M) :
    (H ⧸ M) ≃* Multiplicative (ZMod m) × Sigma :=
  (QuotientGroup.congr _ _ Phi hM).symm.trans
    (CFSG.Wreathed.CentralSL2Abelianization.matrixQuotientEquiv F b m hm heven Sigma hSigma)

theorem originalMatrixQuotientEquiv_mk
    (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (Phi : SemilinearExtension F b m hm heven Sigma hSigma ≃* H)
    (M : Subgroup H) [M.Normal]
    (hM : (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F b m hm heven Sigma hSigma).map
      Phi.toMonoidHom = M)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (sigma : Sigma) :
    originalMatrixQuotientEquiv F b m hm heven Sigma hSigma Phi M hM
      (QuotientGroup.mk (Phi ⟨quotientClass F b m hm heven X j, sigma⟩)) =
      (Multiplicative.ofAdd (ZMod.castHom (dvd_mul_left m 2) (ZMod m) j), sigma) := by
  change CFSG.Wreathed.CentralSL2Abelianization.matrixQuotientEquiv F b m hm heven Sigma hSigma
    ((QuotientGroup.congr _ _ Phi hM).symm
      (QuotientGroup.mk (Phi ⟨quotientClass F b m hm heven X j, sigma⟩))) = _
  have heq := QuotientGroup.congr_mk
    (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F b m hm heven Sigma hSigma)
    M Phi hM (⟨quotientClass F b m hm heven X j, sigma⟩)
  rw [← heq, MulEquiv.symm_apply_apply]
  rfl

theorem original_matrix_quotient_card
    (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (Phi : SemilinearExtension F b m hm heven Sigma hSigma ≃* H)
    (M : Subgroup H) [M.Normal]
    (hM : (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F b m hm heven Sigma hSigma).map
      Phi.toMonoidHom = M) : Nat.card (H ⧸ M) = m * Nat.card Sigma := by
  let : NeZero m := ⟨by omega⟩
  rw [Nat.card_congr (originalMatrixQuotientEquiv F b m hm heven Sigma hSigma Phi M hM).toEquiv,
    Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod m) ≃ ZMod m),
    Nat.card_eq_fintype_card, ZMod.card]

theorem original_matrix_quotient_isCyclic [Finite F]
    (b : Fˣ) (n : ℕ) (hm : 0 < 2 ^ n) (heven : Even (2 ^ n))
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (hd : Odd (Nat.card Sigma))
    (Phi : SemilinearExtension F b (2 ^ n) hm heven Sigma hSigma ≃* H)
    (M : Subgroup H) [M.Normal]
    (hM : (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer
      F b (2 ^ n) hm heven Sigma hSigma).map Phi.toMonoidHom = M) : IsCyclic (H ⧸ M) := by
  let : NeZero (2 ^ n) := ⟨by positivity⟩
  let : IsCyclic Sigma := CFSG.Wreathed.CentralSL2Abelianization.fieldSubgroup_isCyclic F Sigma
  apply (originalMatrixQuotientEquiv F b (2 ^ n) hm heven Sigma hSigma Phi M hM).isCyclic.mpr
  apply Group.isCyclic_prod_iff.mpr
  refine ⟨inferInstance, inferInstance, ?_⟩
  simpa only [Nat.card_congr
    (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ n)) ≃ ZMod (2 ^ n)),
    Nat.card_eq_fintype_card, ZMod.card] using hd.coprime_two_left.pow_left n

end TransportedQuotient

section LiteralCoverEquivalence

variable [Finite F] [Finite H]
variable (p : ℕ) [CharP F p] (hpodd : Odd p)
variable (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
variable (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
variable (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
variable (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
variable (hker : pi.ker = modelCenter S e) (hcentral : pi.ker ≤ Subgroup.center H)
variable (M : Subgroup H) [M.Normal] (hSM : (S : Subgroup H) ⊓ M = modelY S e)
variable (eta : M ≃* SpecialLinearGroup (Fin 2) F)
variable (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
variable (hminus : eta (originalLayerX n hn S e M hSM) =
  CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F)
variable (b : (FixedField F Sigma)ˣ) (hb : ¬IsSquare (fixedUnit F Sigma b))
variable (tau : H)
variable (hsquare : tau ^ 2 = wreathModelHom S e (Original.a (2 ^ n)))
variable (hpower : tau ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)))
variable (horder : orderOf tau = 2 * 2 ^ n)
variable (himage : coordinateProjection F Sigma pi tau =
  (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)))

@[expose] def originalCoverEquiv :
    SemilinearExtension F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
      (even_two.pow_of_ne_zero (by omega)) Sigma (original_fixed_parameter F Sigma b) ≃* H :=
  MulEquiv.ofBijective _ (original_semilinear_map_bijective F p hpodd hF Sigma hd n hn S e
    pi hpi hker hcentral M hSM eta heta hminus b hb tau hsquare hpower horder himage)

theorem originalCoverEquiv_formula
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (sigma : Sigma) :
    originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
      hminus b hb tau hsquare hpower horder himage
      ⟨quotientClass F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
        (even_two.pow_of_ne_zero (by omega)) X j, sigma⟩ =
      (eta.symm X : H) * tau ^ j.val *
        originalFieldLift F Sigma pi hpi hcentral (original_kernel_isPGroup n S e pi hker) hd sigma :=
  rfl

theorem originalCoverEquiv_special
    (X : SpecialLinearGroup (Fin 2) F) :
    originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
      hminus b hb tau hsquare hpower horder himage
      ⟨specialInclusion F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
        (even_two.pow_of_ne_zero (by omega)) X, 1⟩ = (eta.symm X : H) := by
  rw [specialInclusion_apply, originalCoverEquiv_formula]
  simp only [ZMod.val_zero, pow_zero, mul_one, map_one]

theorem originalCoverEquiv_generator :
    originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
      hminus b hb tau hsquare hpower horder himage
      ⟨cyclicGenerator F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
        (even_two.pow_of_ne_zero (by omega)), 1⟩ = tau := by
  rw [cyclicGenerator, originalCoverEquiv_formula]
  have hval : (1 : ZMod (2 * 2 ^ n)).val = 1 := by
    simpa only [Nat.cast_one] using
      ZMod.val_natCast_of_lt (show 1 < 2 * 2 ^ n by
        have hm : 0 < 2 ^ n := by positivity
        omega)
  simp only [map_one, Subgroup.coe_one, one_mul, hval, pow_one, mul_one]

theorem originalCoverEquiv_generator_square :
    originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
      hminus b hb tau hsquare hpower horder himage
      (⟨cyclicGenerator F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
        (even_two.pow_of_ne_zero (by omega)), 1⟩ ^ 2) =
        wreathModelHom S e (Original.a (2 ^ n)) := by
  rw [map_pow, originalCoverEquiv_generator]
  exact hsquare

theorem originalCoverEquiv_field (sigma : Sigma) :
    originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
      hminus b hb tau hsquare hpower horder himage ⟨1, sigma⟩ =
      originalFieldLift F Sigma pi hpi hcentral (original_kernel_isPGroup n S e pi hker) hd sigma := by
  have hq : (1 : CentralExtension F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
      (even_two.pow_of_ne_zero (by omega))) =
      quotientClass F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
        (even_two.pow_of_ne_zero (by omega)) 1 0 := by
    rw [← specialInclusion_apply]
    exact (map_one (specialInclusion F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
      (even_two.pow_of_ne_zero (by omega)))).symm
  rw [hq, originalCoverEquiv_formula]
  simp only [map_one, Subgroup.coe_one, one_mul, ZMod.val_zero, pow_zero, mul_one]

theorem originalCoverEquiv_projective
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (sigma : Sigma) :
    coordinateProjection F Sigma pi
      (originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
        hminus b hb tau hsquare hpower horder himage
        ⟨quotientClass F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
          (even_two.pow_of_ne_zero (by omega)) X j, sigma⟩) =
      coordinatePGLAction F
        (ProjGenLinGroup.mk (SpecialLinearGroup.toGL X *
          nonsquareMatrix F (fixedUnit F Sigma b) ^ j.val)) * fieldExtension F sigma := by
  rw [originalCoverEquiv_formula, map_mul, map_mul, map_pow, himage,
    ← heta (eta.symm X), eta.apply_symm_apply,
    originalFieldLift_apply, CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective]
  have hsl : slCoordinateAction F X =
      coordinatePGLAction F (ProjGenLinGroup.mk (SpecialLinearGroup.toGL X)) := by
    rw [← ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL]
    rfl
  rw [hsl, map_mul, map_mul, map_pow, map_pow]
  rfl

theorem originalCoverEquiv_matrixLayer :
    (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F (fixedUnit F Sigma b) (2 ^ n)
      (by positivity) (even_two.pow_of_ne_zero (by omega)) Sigma
      (original_fixed_parameter F Sigma b)).map
      (originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
        hminus b hb tau hsquare hpower horder himage).toMonoidHom = M := by
  rw [matrixLayer_image_of_values F (fixedUnit F Sigma b) (2 ^ n) (by positivity)
    (even_two.pow_of_ne_zero (by omega)) Sigma (original_fixed_parameter F Sigma b)
    (originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta
      hminus b hb tau hsquare hpower horder himage)
    (CFSG.Semidihedral.MatrixCover.layerLift F M eta)
    (fun X => originalCoverEquiv_special F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
      M hSM eta heta hminus b hb tau hsquare hpower horder himage X)]
  exact layerLift_range F M eta

end LiteralCoverEquivalence

section OriginalFixedEquivalence

@[expose] def originalFixedCentralizerEquiv [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v) :
    (Subgroup.centralizer
      (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral : Set H)).subgroupOf M ≃*
      SpecialLinearGroup (Fin 2) (FixedPoints.subfield Sigma F) :=
  (eta.subgroupMap _).trans
    ((subgroupEquivOfEq (original_eta_centralizer_image F p hpodd M eta Sigma pi hpi hcentral
      hK hd heta)).trans (fixedSL2EquivRange F Sigma).symm)

theorem originalFixedCentralizerEquiv_inclusion [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (M : Subgroup H) [M.Normal] (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma))
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (v : (Subgroup.centralizer
      (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral : Set H)).subgroupOf M) :
    fixedSL2Inclusion F Sigma
      (originalFixedCentralizerEquiv F p hpodd M eta Sigma pi hpi hcentral hK hd heta v) =
        eta v := by
  have h := (fixedSL2EquivRange F Sigma).apply_symm_apply
    ((subgroupEquivOfEq (original_eta_centralizer_image F p hpodd M eta Sigma pi hpi hcentral
      hK hd heta)) (eta.subgroupMap _ v))
  exact congrArg Subtype.val h

theorem original_central_cover_card [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (n : ℕ) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hker : pi.ker = modelCenter S e) :
    Nat.card H = (2 ^ n) * Nat.card Sigma * Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [H_card F Sigma pi hpi, original_kernel_card n S e pi hker]
  ac_rfl

end OriginalFixedEquivalence

section OriginalUniqueFieldLift

theorem original_eSigma_unique [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center H)
    (hK : IsPGroup 2 pi.ker) (hd : Odd (Nat.card Sigma)) (sigma : Sigma) :
    ∃! e : CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral,
      coordinateProjection F Sigma pi e = fieldExtension F sigma := by
  refine ⟨CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma F Sigma pi hpi hcentral hK hd sigma,
    CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective F Sigma pi hpi hcentral hK hd sigma, ?_⟩
  intro e he
  apply (CFSG.Wreathed.CentralTwoPowerFieldLift.piOnE F Sigma pi hpi hcentral hK hd).injective
  apply Subtype.ext
  apply CFSG.Semidihedral.MatrixCover.quotient_coordinates_injective F Sigma
  simpa only [CFSG.Wreathed.CentralTwoPowerFieldLift.piOnE_coe, coordinateProjection,
    MonoidHom.comp_apply, Subgroup.coe_subtype] using
    he.trans (CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective
      F Sigma pi hpi hcentral hK hd sigma).symm

end OriginalUniqueFieldLift

theorem exists_original_fixed_nonsquare_unit [Finite F]
    (p : ℕ) [CharP F p] (hpodd : Odd p)
    (Sigma : Subgroup (F ≃+* F)) : ∃ b : (FixedField F Sigma)ˣ, ¬IsSquare b := by
  have hpne : p ≠ 2 := by intro h; subst p; norm_num at hpodd
  have hchar : ringChar (FixedField F Sigma) ≠ 2 := by
    rwa [ringChar.eq (FixedField F Sigma) p]
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have hane : a ≠ 0 := by
    intro h
    exact ha (h ▸ ⟨0, by simp⟩)
  let b : (FixedField F Sigma)ˣ := Units.mk0 a hane
  refine ⟨b, ?_⟩
  rintro ⟨c, hc⟩
  exact ha ⟨c.val, congrArg Units.val hc⟩

theorem wreathed_central_cover_exact_matrix_field_model_of_finite [Finite F] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hker : pi.ker = modelCenter S e) (hcentral : pi.ker ≤ Subgroup.center H)
    (M : Subgroup H) [M.Normal] (hSM : (S : Subgroup H) ⊓ M = modelY S e)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (hminus : eta (originalLayerX n hn S e M hSM) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    let m := 2 ^ n
    let hm : 0 < m := by positivity
    let heven : Even m := even_two.pow_of_ne_zero (by omega)
    let hK := original_kernel_isPGroup n S e pi hker
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral
    let eField := originalFieldLift F Sigma pi hpi hcentral hK hd
    let fixParam := original_fixed_parameter F Sigma
    Nat.card Sigma ∣ f ∧
    Nat.card (FixedPoints.subfield Sigma F) = p ^ (f / Nat.card Sigma) ∧
    (∀ t : H, t ∈ E0 ↔ t ∈ B F Sigma pi ∧ t ^ Nat.card Sigma = 1) ∧
    (∀ sigma : Sigma, ∃! t : E0, coordinateProjection F Sigma pi t = fieldExtension F sigma) ∧
    (∀ b : (FixedField F Sigma)ˣ, ¬IsSquare b →
      ¬IsSquare (fixedUnit F Sigma b) ∧
      ∃ tau : H, tau ∈ Subgroup.centralizer (E0 : Set H) ∧
        tau ^ 2 = wreathModelHom S e (Original.a m) ∧
        tau ^ m = wreathModelHom S e (Original.x m) ∧
        orderOf tau = 2 * m ∧
        coordinateProjection F Sigma pi tau =
          (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)) ∧
        ∃ Phi : SemilinearExtension F (fixedUnit F Sigma b) m hm heven Sigma (fixParam b) ≃* H,
          (∀ X j sigma, Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩ =
            (eta.symm X : H) * tau ^ j.val * eField sigma) ∧
          (∀ X, Phi ⟨specialInclusion F (fixedUnit F Sigma b) m hm heven X, 1⟩ =
            (eta.symm X : H)) ∧
          Phi ⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ = tau ∧
          Phi (⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ ^ 2) =
            wreathModelHom S e (Original.a m) ∧
          (∀ sigma : Sigma, Phi ⟨1, sigma⟩ = eField sigma) ∧
          (∀ X j sigma, coordinateProjection F Sigma pi
            (Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩) =
              coordinatePGLAction F (ProjGenLinGroup.mk
                (SpecialLinearGroup.toGL X * nonsquareMatrix F (fixedUnit F Sigma b) ^ j.val)) *
                  fieldExtension F sigma) ∧
          (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F (fixedUnit F Sigma b) m hm heven
            Sigma (fixParam b)).map Phi.toMonoidHom = M) ∧
    Nat.card H = m * Nat.card Sigma * Nat.card F * (Nat.card F ^ 2 - 1) ∧
    IsCyclic (H ⧸ M) ∧ Nat.card (H ⧸ M) = m * Nat.card Sigma ∧
    (∀ sigma : Sigma, ∀ v : M, ∀ i j : Fin 2,
      eta (conjugateIn M (eField sigma) v) i j = (sigma : F ≃+* F) (eta v i j)) ∧
    ((Subgroup.centralizer (E0 : Set H)).subgroupOf M).map eta.toMonoidHom =
      (fixedSL2Inclusion F Sigma).range ∧
    (∃ eps : (Subgroup.centralizer (E0 : Set H)).subgroupOf M ≃*
      SpecialLinearGroup (Fin 2) (FixedPoints.subfield Sigma F),
      ∀ v, fixedSL2Inclusion F Sigma (eps v) = eta v) := by
  let : CharP F p := CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, hcard⟩
  dsimp only
  let m := 2 ^ n
  have hm : 0 < m := by positivity
  have heven : Even m := even_two.pow_of_ne_zero (by omega)
  let hK := original_kernel_isPGroup n S e pi hker
  let eField := originalFieldLift F Sigma pi hpi hcentral hK hd
  have hfixed := original_fixed_field_data p f hp hpodd hf F hcard Sigma hd
  have hmodels : ∀ b : (FixedField F Sigma)ˣ, ¬IsSquare b →
      ¬IsSquare (fixedUnit F Sigma b) ∧
      ∃ tau : H, tau ∈ Subgroup.centralizer
          (CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral : Set H) ∧
        tau ^ 2 = wreathModelHom S e (Original.a m) ∧
        tau ^ m = wreathModelHom S e (Original.x m) ∧
        orderOf tau = 2 * m ∧
        coordinateProjection F Sigma pi tau =
          (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)) ∧
        ∃ Phi : SemilinearExtension F (fixedUnit F Sigma b) m hm heven Sigma
            (original_fixed_parameter F Sigma b) ≃* H,
          (∀ X j sigma, Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩ =
            (eta.symm X : H) * tau ^ j.val * eField sigma) ∧
          (∀ X, Phi ⟨specialInclusion F (fixedUnit F Sigma b) m hm heven X, 1⟩ =
            (eta.symm X : H)) ∧
          Phi ⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ = tau ∧
          Phi (⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ ^ 2) =
            wreathModelHom S e (Original.a m) ∧
          (∀ sigma : Sigma, Phi ⟨1, sigma⟩ = eField sigma) ∧
          (∀ X j sigma, coordinateProjection F Sigma pi
            (Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩) =
              coordinatePGLAction F (ProjGenLinGroup.mk
                (SpecialLinearGroup.toGL X * nonsquareMatrix F (fixedUnit F Sigma b) ^ j.val)) *
                  fieldExtension F sigma) ∧
          (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F (fixedUnit F Sigma b) m hm heven
            Sigma (original_fixed_parameter F Sigma b)).map Phi.toMonoidHom = M := by
    intro b hb
    obtain ⟨hbF, tau, hc, hsquare, hpower, horder, himage⟩ :=
      exists_original_fixed_j_square_root F hF Sigma hd n hn S e pi hpi hker hcentral M hSM
        eta heta b hb
    let Phi := originalCoverEquiv F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral M hSM
      eta heta hminus b hbF tau hsquare hpower horder himage
    refine ⟨hbF, tau, hc, hsquare, hpower, horder, himage, Phi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact originalCoverEquiv_formula F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
        M hSM eta heta hminus b hbF tau hsquare hpower horder himage
    · exact originalCoverEquiv_special F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
        M hSM eta heta hminus b hbF tau hsquare hpower horder himage
    · exact originalCoverEquiv_generator F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
        M hSM eta heta hminus b hbF tau hsquare hpower horder himage
    · exact originalCoverEquiv_generator_square F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
        M hSM eta heta hminus b hbF tau hsquare hpower horder himage
    · exact originalCoverEquiv_field F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
        M hSM eta heta hminus b hbF tau hsquare hpower horder himage
    · exact originalCoverEquiv_projective F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
        M hSM eta heta hminus b hbF tau hsquare hpower horder himage
    · exact originalCoverEquiv_matrixLayer F p hpodd hF Sigma hd n hn S e pi hpi hker hcentral
        M hSM eta heta hminus b hbF tau hsquare hpower horder himage
  have hquot : IsCyclic (H ⧸ M) ∧ Nat.card (H ⧸ M) = m * Nat.card Sigma := by
    obtain ⟨b, hb⟩ := exists_original_fixed_nonsquare_unit F p hpodd Sigma
    obtain ⟨_, tau, _, _, _, _, _, Phi, _, _, _, _, _, _, hML⟩ := hmodels b hb
    exact ⟨original_matrix_quotient_isCyclic F (fixedUnit F Sigma b) n hm heven Sigma
      (original_fixed_parameter F Sigma b) hd Phi M hML,
      original_matrix_quotient_card F (fixedUnit F Sigma b) m hm heven Sigma
        (original_fixed_parameter F Sigma b) Phi M hML⟩
  refine ⟨hfixed.1, hfixed.2.1, fun t => mem_E F Sigma pi hcentral t,
    original_eSigma_unique F Sigma pi hpi hcentral hK hd, hmodels,
    original_central_cover_card F Sigma n S e pi hpi hker, hquot.1, hquot.2, ?_,
    original_eta_centralizer_image F p hpodd M eta Sigma pi hpi hcentral hK hd heta,
    originalFixedCentralizerEquiv F p hpodd M eta Sigma pi hpi hcentral hK hd heta,
    originalFixedCentralizerEquiv_inclusion F p hpodd M eta Sigma pi hpi hcentral hK hd heta⟩
  intro sigma v i j
  rw [original_eta_field_conjugation F p hpodd M eta Sigma pi hpi hcentral hK hd heta]
  rfl

@[expose] def OriginalCentralCoverModel [Finite F] [Finite H]
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f)
    (_hcard : Nat.card F = p ^ f)
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hker : pi.ker = modelCenter S e) (hcentral : pi.ker ≤ Subgroup.center H)
    (M : Subgroup H) [M.Normal] (hSM : (S : Subgroup H) ⊓ M = modelY S e)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (_heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (_hminus : eta (originalLayerX n hn S e M hSM) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) : Prop :=
    let m := 2 ^ n
    let hm : 0 < m := by positivity
    let heven : Even m := even_two.pow_of_ne_zero (by omega)
    let hK := original_kernel_isPGroup n S e pi hker
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma pi hcentral
    let eField := originalFieldLift F Sigma pi hpi hcentral hK hd
    let fixParam := original_fixed_parameter F Sigma
    Nat.card Sigma ∣ f ∧
    Nat.card (FixedPoints.subfield Sigma F) = p ^ (f / Nat.card Sigma) ∧
    (∀ t : H, t ∈ E0 ↔ t ∈ B F Sigma pi ∧ t ^ Nat.card Sigma = 1) ∧
    (∀ sigma : Sigma, ∃! t : E0, coordinateProjection F Sigma pi t = fieldExtension F sigma) ∧
    (∀ b : (FixedField F Sigma)ˣ, ¬IsSquare b →
      ¬IsSquare (fixedUnit F Sigma b) ∧
      ∃ tau : H, tau ∈ Subgroup.centralizer (E0 : Set H) ∧
        tau ^ 2 = wreathModelHom S e (Original.a m) ∧
        tau ^ m = wreathModelHom S e (Original.x m) ∧
        orderOf tau = 2 * m ∧
        coordinateProjection F Sigma pi tau =
          (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)) ∧
        ∃ Phi : SemilinearExtension F (fixedUnit F Sigma b) m hm heven Sigma (fixParam b) ≃* H,
          (∀ X j sigma, Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩ =
            (eta.symm X : H) * tau ^ j.val * eField sigma) ∧
          (∀ X, Phi ⟨specialInclusion F (fixedUnit F Sigma b) m hm heven X, 1⟩ =
            (eta.symm X : H)) ∧
          Phi ⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ = tau ∧
          Phi (⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ ^ 2) =
            wreathModelHom S e (Original.a m) ∧
          (∀ sigma : Sigma, Phi ⟨1, sigma⟩ = eField sigma) ∧
          (∀ X j sigma, coordinateProjection F Sigma pi
            (Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩) =
              coordinatePGLAction F (ProjGenLinGroup.mk
                (SpecialLinearGroup.toGL X * nonsquareMatrix F (fixedUnit F Sigma b) ^ j.val)) *
                  fieldExtension F sigma) ∧
          (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F (fixedUnit F Sigma b) m hm heven
            Sigma (fixParam b)).map Phi.toMonoidHom = M) ∧
    Nat.card H = m * Nat.card Sigma * Nat.card F * (Nat.card F ^ 2 - 1) ∧
    IsCyclic (H ⧸ M) ∧ Nat.card (H ⧸ M) = m * Nat.card Sigma ∧
    (∀ sigma : Sigma, ∀ v : M, ∀ i j : Fin 2,
      eta (conjugateIn M (eField sigma) v) i j = (sigma : F ≃+* F) (eta v i j)) ∧
    ((Subgroup.centralizer (E0 : Set H)).subgroupOf M).map eta.toMonoidHom =
      (fixedSL2Inclusion F Sigma).range ∧
    (∃ eps : (Subgroup.centralizer (E0 : Set H)).subgroupOf M ≃*
      SpecialLinearGroup (Fin 2) (FixedPoints.subfield Sigma F),
      ∀ v, fixedSL2Inclusion F Sigma (eps v) = eta v)


theorem wreathed_central_cover_exact_matrix_field_model
    (F : Type u) [Field F] (H : Type v) [Group H] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) :
    let : Finite F := Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero f hp.ne_zero))
    ∀ (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hker : pi.ker = modelCenter S e) (hcentral : pi.ker ≤ Subgroup.center H)
    (M : Subgroup H) [M.Normal] (hSM : (S : Subgroup H) ⊓ M = modelY S e)
    (eta : M ≃* SpecialLinearGroup (Fin 2) F)
    (heta : ∀ v : M, slCoordinateAction F (eta v) = coordinateProjection F Sigma pi v)
    (hminus : eta (originalLayerX n hn S e M hSM) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F),
    OriginalCentralCoverModel F p f hp hpodd hf hcard Sigma hd n hn S e pi hpi hker
      hcentral M hSM eta heta hminus := by
  dsimp only
  let : Finite F := Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero f hp.ne_zero))
  intro Sigma hd n hn S e pi hpi hker hcentral M hM hSM eta heta hminus
  exact wreathed_central_cover_exact_matrix_field_model_of_finite F p f hp hpodd hf hcard
    Sigma hd n hn S e pi hpi hker hcentral M hSM eta heta hminus


end CFSG.Wreathed.WreathedCentralCover
