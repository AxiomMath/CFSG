module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixLagrangianSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearSymplecticInvolution

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix Module CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} {n : ℕ}

@[expose] def basisGL {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι (ZMod 2) V) :
    LinearMap.GeneralLinearGroup (ZMod 2) V ≃* GL ι (ZMod 2) :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv e).toMulEquiv

theorem coe_basisGL {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι (ZMod 2) V)
    (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    ((basisGL e g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) =
      LinearMap.toMatrix e e (g : V →ₗ[ZMod 2] V) :=
  rfl

theorem mem_bilinIsometryGroup_iff {e : Basis (Fin n ⊕ Fin n) (ZMod 2) V}
    (he : IsSymplecticBasis b e) (g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    g ∈ bilinIsometryGroup b ↔ basisGL e g ∈ StatedSp n (ZMod 2) := by
  rw [mem_statedSp_iff, coe_basisGL, ← he, mem_bilinIsometryGroup,
    ← TauCeti.BilinForm.isIsometry_iff]
  exact TauCeti.BilinForm.isIsometry_iff_toMatrix e

@[expose] def spCoord {e : Basis (Fin n ⊕ Fin n) (ZMod 2) V} (he : IsSymplecticBasis b e) :
    bilinIsometryGroup b ≃* StatedSp n (ZMod 2) where
  toFun g := ⟨basisGL e g, (mem_bilinIsometryGroup_iff he g).1 g.2⟩
  invFun A := ⟨(basisGL e).symm A, (mem_bilinIsometryGroup_iff he _).2 (by
    rw [MulEquiv.apply_symm_apply]
    exact A.2)⟩
  left_inv g := Subtype.ext ((basisGL e).symm_apply_apply g.1)
  right_inv A := Subtype.ext ((basisGL e).apply_symm_apply A.1)
  map_mul' g h := Subtype.ext ((basisGL e).map_mul g.1 h.1)

variable {e : Basis (Fin n ⊕ Fin n) (ZMod 2) V} (he : IsSymplecticBasis b e)

theorem spMatrixOf_spCoord (g : bilinIsometryGroup b) :
    spMatrixOf (spCoord he g) =
      LinearMap.toMatrix e e ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) :=
  rfl

theorem spCoord_mulVec (g : bilinIsometryGroup b) (v : V) :
    spMatrixOf (spCoord he g) *ᵥ ⇑(e.repr v) =
      ⇑(e.repr (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v)) :=
  LinearMap.toMatrix_mulVec_repr e e _ v

variable (e) in
@[expose] def lagrangianOf : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range (e ∘ Sum.inl))

theorem mem_lagrangianOf {v : V} : v ∈ lagrangianOf e ↔ ⇑(e.repr v) ∈ lagrangianZero n := by
  rw [mem_lagrangianZero, lagrangianOf, Set.range_comp, Basis.mem_span_image]
  constructor
  · intro h j
    by_contra hj
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.2 hj)
    exact Sum.inl_ne_inr hi
  · intro h x hx
    rcases x with i | j
    · exact ⟨i, rfl⟩
    · exact absurd (h j) (Finsupp.mem_support_iff.1 hx)

theorem map_lagrangianOf : (lagrangianOf e).map e.equivFun.toLinearMap = lagrangianZero n := by
  ext u
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_lagrangianOf.1 hw
  · intro hu
    refine ⟨e.equivFun.symm u, mem_lagrangianOf.2 ?_, e.equivFun.apply_symm_apply u⟩
    have h : ⇑(e.repr (e.equivFun.symm u)) = u := e.equivFun.apply_symm_apply u
    rw [h]
    exact hu

omit [Module (ZMod 2) V] in
theorem exists_basis_lagrangianOf [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 2 * n) {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = n) :
    ∃ e : Basis (Fin n ⊕ Fin n) (ZMod 2) V, IsSymplecticBasis b e ∧ W = lagrangianOf e := by
  obtain ⟨e, he, hWe⟩ := exists_completeIsotropicFlag hb hnd hV hW
  refine ⟨e, he, ?_⟩
  rw [hWe, hd, lagrangianOf, Set.range_comp,
    show {j : Fin n | (j : ℕ) < n} = Set.univ from Set.eq_univ_of_forall fun j => j.2,
    Set.image_univ]

variable (b) in
@[expose] def subspaceStabilizer (W : Submodule (ZMod 2) V) : Subgroup (bilinIsometryGroup b) where
  carrier := {g | W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = W}
  one_mem' := Submodule.map_id W
  mul_mem' {g h} hg hh := by
    change W.map ((((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)).comp
      ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) = W
    rw [Submodule.map_comp, hh, hg]
  inv_mem' {g} hg := by
    have h1 : ((((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V)).comp ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) = LinearMap.id := by
      change ((((g⁻¹ * g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V)) = LinearMap.id
      rw [inv_mul_cancel]
      rfl
    change W.map _ = W
    conv_lhs => rw [← hg]
    rw [← Submodule.map_comp, h1, Submodule.map_id]

theorem mem_subspaceStabilizer {W : Submodule (ZMod 2) V} {g : bilinIsometryGroup b} :
    g ∈ subspaceStabilizer b W ↔
      W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = W :=
  Iff.rfl

theorem apply_mem_of_mem_subspaceStabilizer {W : Submodule (ZMod 2) V} {g : bilinIsometryGroup b}
    (hg : g ∈ subspaceStabilizer b W) {w : V} (hw : w ∈ W) :
    ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w ∈ W := by
  have h : ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w ∈
      W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) :=
    Submodule.mem_map_of_mem hw
  rwa [mem_subspaceStabilizer.1 hg] at h

theorem apply_inv_apply (g : bilinIsometryGroup b) (v : V) :
    ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) v) = v := by
  change ((((g * g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    V →ₗ[ZMod 2] V)) v = v
  rw [mul_inv_cancel]
  rfl

theorem inv_apply_apply (g : bilinIsometryGroup b) (v : V) :
    (((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) = v := by
  change ((((g⁻¹ * g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    V →ₗ[ZMod 2] V)) v = v
  rw [inv_mul_cancel]
  rfl

theorem pointwiseStabilizer_le_subspaceStabilizer (W : Submodule (ZMod 2) V) :
    pointwiseStabilizer b W ≤ subspaceStabilizer b W := by
  intro g hg
  rw [mem_subspaceStabilizer]
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [hg w hw]
    exact hw
  · intro hx
    exact ⟨x, hx, hg x hx⟩

variable (b) in
@[expose] def restrictSubspace (W : Submodule (ZMod 2) V) :
    subspaceStabilizer b W →* LinearMap.GeneralLinearGroup (ZMod 2) W where
  toFun g :=
    { val := (((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V).restrict fun _ hw => apply_mem_of_mem_subspaceStabilizer g.2 hw
      inv := ((((g⁻¹ : subspaceStabilizer b W) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V).restrict
          fun _ hw => apply_mem_of_mem_subspaceStabilizer (g⁻¹).2 hw
      val_inv := LinearMap.ext fun w =>
        Subtype.ext (apply_inv_apply (g : bilinIsometryGroup b) (w : V))
      inv_val := LinearMap.ext fun w =>
        Subtype.ext (inv_apply_apply (g : bilinIsometryGroup b) (w : V)) }
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem restrictSubspace_apply {W : Submodule (ZMod 2) V} (g : subspaceStabilizer b W) (w : W) :
    (((restrictSubspace b W g : LinearMap.GeneralLinearGroup (ZMod 2) W) :
      W →ₗ[ZMod 2] W) w : V) =
      (((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) w :=
  rfl

theorem ker_restrictSubspace (W : Submodule (ZMod 2) V) :
    (restrictSubspace b W).ker =
      (pointwiseStabilizer b W).subgroupOf (subspaceStabilizer b W) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_pointwiseStabilizer]
  constructor
  · intro h w hw
    exact congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) W =>
      ((u : W →ₗ[ZMod 2] W) ⟨w, hw⟩ : V)) h
  · intro h
    exact Units.ext (LinearMap.ext fun w => Subtype.ext (h w w.2))

instance normal_pointwiseStabilizer_subgroupOf (W : Submodule (ZMod 2) V) :
    ((pointwiseStabilizer b W).subgroupOf (subspaceStabilizer b W)).Normal := by
  rw [← ker_restrictSubspace]
  exact MonoidHom.normal_ker _

include he in
theorem mem_pointwiseStabilizer_iff_spCoord (g : bilinIsometryGroup b) :
    g ∈ pointwiseStabilizer b (lagrangianOf e) ↔ spCoord he g ∈ (tauSym n).range := by
  rw [mem_range_tauSym_iff, mem_pointwiseStabilizer]
  constructor
  · intro h u hu
    have hwu : ⇑(e.repr (e.equivFun.symm u)) = u := e.equivFun.apply_symm_apply u
    have hmem : e.equivFun.symm u ∈ lagrangianOf e := mem_lagrangianOf.2 (by rw [hwu]; exact hu)
    rw [← hwu, spCoord_mulVec, h _ hmem]
  · intro h w hw
    have := h _ (mem_lagrangianOf.1 hw)
    rw [spCoord_mulVec] at this
    exact e.repr.injective (DFunLike.coe_injective this)

include he in
theorem mem_pointwiseStabilizer_iff_toMatrix (g : bilinIsometryGroup b) :
    g ∈ pointwiseStabilizer b (lagrangianOf e) ↔ ∃ B : Matrix (Fin n) (Fin n) (ZMod 2), Bᵀ = B ∧
      LinearMap.toMatrix e e ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) =
        fromBlocks 1 B 0 1 := by
  rw [mem_pointwiseStabilizer_iff_spCoord he, ← spMatrixOf_spCoord he]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B.toAdd, binarySym_transpose _, by rw [← hB, spMatrixOf_tauSym]⟩
  · rintro ⟨B, hBt, hB⟩
    exact ⟨Multiplicative.ofAdd ⟨B, mem_binarySymMatrices.2 hBt⟩, statedSp_ext (by
      change spMatrixOf (tauSym n _) = spMatrixOf (spCoord he g)
      rw [hB, spMatrixOf_tauSym, toAdd_ofAdd])⟩

theorem equivFun_comp_spCoord (g : bilinIsometryGroup b) :
    e.equivFun.toLinearMap.comp ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) = (mulVecLin (spMatrixOf (spCoord he g))).comp e.equivFun.toLinearMap :=
  LinearMap.ext fun v => (spCoord_mulVec he g v).symm

theorem mem_subspaceStabilizer_iff_spCoord (g : bilinIsometryGroup b) :
    g ∈ subspaceStabilizer b (lagrangianOf e) ↔
      spCoord he g ∈ stabilizer n (ZMod 2) (lagrangianZero n) := by
  rw [mem_stabilizer, mem_subspaceStabilizer]
  rw [← map_lagrangianOf (e := e), ← Submodule.map_comp, ← equivFun_comp_spCoord he g,
    Submodule.map_comp]
  exact (Submodule.map_injective_of_injective e.equivFun.injective).eq_iff.symm

variable (e) in
@[expose] def lagrangianBasis : Basis (Fin n) (ZMod 2) (lagrangianOf e) :=
  Basis.span (e.linearIndependent.comp Sum.inl Sum.inl_injective)

theorem coe_lagrangianBasis (j : Fin n) : (lagrangianBasis e j : V) = e (Sum.inl j) :=
  Basis.coe_span_apply _ j

theorem lagrangianBasis_repr (w : lagrangianOf e) (i : Fin n) :
    (lagrangianBasis e).repr w i = e.repr (w : V) (Sum.inl i) := by
  have key : (Finsupp.lapply i).comp (lagrangianBasis e).repr.toLinearMap =
      (Finsupp.lapply (Sum.inl i)).comp (e.repr.toLinearMap.comp (lagrangianOf e).subtype) := by
    refine (lagrangianBasis e).ext fun j => ?_
    simp [coe_lagrangianBasis, Finsupp.single_apply]
  exact LinearMap.congr_fun key w

theorem toMatrix_restrictSubspace (g : subspaceStabilizer b (lagrangianOf e)) :
    LinearMap.toMatrix (lagrangianBasis e) (lagrangianBasis e)
        ((restrictSubspace b (lagrangianOf e) g :
          LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
            lagrangianOf e →ₗ[ZMod 2] lagrangianOf e) =
      (spMatrixOf (spCoord he (g : bilinIsometryGroup b))).toBlocks₁₁ := by
  ext i j
  rw [LinearMap.toMatrix_apply, lagrangianBasis_repr, restrictSubspace_apply, coe_lagrangianBasis,
    toBlocks₁₁, of_apply, spMatrixOf_spCoord, LinearMap.toMatrix_apply]

theorem basisGL_restrictSubspace (g : subspaceStabilizer b (lagrangianOf e)) :
    basisGL (lagrangianBasis e) (restrictSubspace b (lagrangianOf e) g) =
      lagrangianLevi n ⟨spCoord he (g : bilinIsometryGroup b),
        (mem_subspaceStabilizer_iff_spCoord he (g : bilinIsometryGroup b)).1 g.2⟩ :=
  Units.ext (toMatrix_restrictSubspace he g)

include he in
theorem restrictSubspace_surjective :
    Function.Surjective (restrictSubspace b (lagrangianOf e)) := by
  intro A
  obtain ⟨s, hs⟩ := lagrangianLevi_surjective (basisGL (lagrangianBasis e) A)
  have hg : (spCoord he).symm (s : StatedSp n (ZMod 2)) ∈
      subspaceStabilizer b (lagrangianOf e) := by
    rw [mem_subspaceStabilizer_iff_spCoord he, MulEquiv.apply_symm_apply]
    exact s.2
  refine ⟨⟨_, hg⟩, (basisGL (lagrangianBasis e)).injective ?_⟩
  rw [basisGL_restrictSubspace he, ← hs]
  congr 1
  exact Subtype.ext (MulEquiv.apply_symm_apply _ _)

theorem spMatrixOf_spCoord_conj (g : subspaceStabilizer b (lagrangianOf e))
    {r : bilinIsometryGroup b} {B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hr : spMatrixOf (spCoord he r) = fromBlocks 1 B 0 1) (hB : Bᵀ = B) :
    spMatrixOf (spCoord he ((g : bilinIsometryGroup b) * r * (g : bilinIsometryGroup b)⁻¹)) =
      fromBlocks 1 (LinearMap.toMatrix (lagrangianBasis e) (lagrangianBasis e)
          ((restrictSubspace b (lagrangianOf e) g :
            LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
              lagrangianOf e →ₗ[ZMod 2] lagrangianOf e) * B *
        (LinearMap.toMatrix (lagrangianBasis e) (lagrangianBasis e)
          ((restrictSubspace b (lagrangianOf e) g :
            LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
              lagrangianOf e →ₗ[ZMod 2] lagrangianOf e))ᵀ) 0 1 := by
  have hg := (mem_subspaceStabilizer_iff_spCoord he (g : bilinIsometryGroup b)).1 g.2
  have hr' : spCoord he r = tauSym n (Multiplicative.ofAdd ⟨B, mem_binarySymMatrices.2 hB⟩) :=
    statedSp_ext (by
      change spMatrixOf (spCoord he r) = spMatrixOf (tauSym n _)
      rw [hr, spMatrixOf_tauSym, toAdd_ofAdd])
  rw [map_mul, map_mul, map_inv, hr', conj_tauSym_of_mem_stabilizer hg, spMatrixOf_tauSym,
    toAdd_ofAdd, toMatrix_restrictSubspace he g]
  rfl

omit he in
theorem lagrangianOf_eq_span_image :
    lagrangianOf e = Submodule.span (ZMod 2) (e '' (Sum.inl '' {j : Fin n | (j : ℕ) < n})) := by
  rw [lagrangianOf, Set.range_comp,
    show {j : Fin n | (j : ℕ) < n} = Set.univ from Set.eq_univ_of_forall fun j => j.2,
    Set.image_univ]

omit he in
theorem finrank_lagrangianOf : finrank (ZMod 2) (lagrangianOf e) = n := by
  rw [lagrangianOf_eq_span_image]
  exact finrank_span_inl_image e le_rfl

include he in
theorem isTotallyIsotropic_lagrangianOf : IsTotallyIsotropic b (lagrangianOf e) := by
  rw [lagrangianOf, Set.range_comp, ← Set.image_univ]
  exact he.isTotallyIsotropic Set.univ

theorem map_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (A : Subgroup G) :
    (Subgroup.centralizer (A : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((A.map φ.toMonoidHom : Subgroup H) : Set H) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    apply φ.symm.injective
    rw [map_mul, map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact h a ha
  · intro h a ha
    have h1 := h (φ a) ⟨a, ha, rfl⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1

theorem map_spCoord_pointwiseStabilizer :
    (pointwiseStabilizer b (lagrangianOf e)).map (spCoord he).toMonoidHom = (tauSym n).range := by
  ext s
  rw [Subgroup.mem_map_equiv, mem_pointwiseStabilizer_iff_spCoord he, MulEquiv.apply_symm_apply]

theorem map_spCoord_subspaceStabilizer :
    (subspaceStabilizer b (lagrangianOf e)).map (spCoord he).toMonoidHom =
      stabilizer n (ZMod 2) (lagrangianZero n) := by
  ext s
  rw [Subgroup.mem_map_equiv, mem_subspaceStabilizer_iff_spCoord he, MulEquiv.apply_symm_apply]

include he in
theorem card_pointwiseStabilizer_lagrangianOf :
    Nat.card (pointwiseStabilizer b (lagrangianOf e)) = 2 ^ (n * (n + 1) / 2) := by
  rw [← card_range_tauSym n, ← map_spCoord_pointwiseStabilizer he,
    Subgroup.card_map_of_injective (spCoord he).injective]

include he in
theorem mul_comm_of_mem_pointwiseStabilizer_lagrangianOf {g h : bilinIsometryGroup b}
    (hg : g ∈ pointwiseStabilizer b (lagrangianOf e))
    (hh : h ∈ pointwiseStabilizer b (lagrangianOf e)) : g * h = h * g := by
  obtain ⟨B, hB⟩ := (mem_pointwiseStabilizer_iff_spCoord he g).1 hg
  obtain ⟨C, hC⟩ := (mem_pointwiseStabilizer_iff_spCoord he h).1 hh
  apply (spCoord he).injective
  rw [map_mul, map_mul, ← hB, ← hC, ← map_mul, ← map_mul, mul_comm]

theorem zmod_two_add_self_eq_zero (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

include he in
theorem mul_self_of_mem_pointwiseStabilizer_lagrangianOf {g : bilinIsometryGroup b}
    (hg : g ∈ pointwiseStabilizer b (lagrangianOf e)) : g * g = 1 := by
  obtain ⟨B, hB⟩ := (mem_pointwiseStabilizer_iff_spCoord he g).1 hg
  have hBB : B * B = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    refine Subtype.ext ?_
    ext i j
    exact zmod_two_add_self_eq_zero
      (((Multiplicative.toAdd B : binarySymMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2)) i j)
  apply (spCoord he).injective
  rw [map_mul, ← hB, ← map_mul, hBB, map_one, map_one]

include he in
theorem isElementaryAbelian_pointwiseStabilizer_lagrangianOf :
    IsElementaryAbelian 2 (pointwiseStabilizer b (lagrangianOf e)) :=
  { toIsMulCommutative := ⟨⟨fun g h =>
      Subtype.ext (mul_comm_of_mem_pointwiseStabilizer_lagrangianOf he g.2 h.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, sq, mul_self_of_mem_pointwiseStabilizer_lagrangianOf he g.2,
          Subgroup.coe_one]) }

include he in
theorem centralizer_pointwiseStabilizer_lagrangianOf :
    Subgroup.centralizer (pointwiseStabilizer b (lagrangianOf e) : Set (bilinIsometryGroup b)) =
      pointwiseStabilizer b (lagrangianOf e) := by
  apply Subgroup.map_injective (f := (spCoord he).toMonoidHom) (spCoord he).injective
  rw [map_centralizer_mulEquiv, map_spCoord_pointwiseStabilizer he, centralizer_range_tauSym]

include he in
theorem normalizer_pointwiseStabilizer_lagrangianOf :
    Subgroup.normalizer (pointwiseStabilizer b (lagrangianOf e) : Set (bilinIsometryGroup b)) =
      subspaceStabilizer b (lagrangianOf e) := by
  apply Subgroup.map_injective (f := (spCoord he).toMonoidHom) (spCoord he).injective
  rw [Subgroup.map_equiv_normalizer_eq, map_spCoord_pointwiseStabilizer he, normalizer_range_tauSym,
    map_spCoord_subspaceStabilizer he]

theorem map_conj_pointwiseStabilizer (g : bilinIsometryGroup b) (W : Submodule (ZMod 2) V) :
    (pointwiseStabilizer b W).map (MulAut.conj g).toMonoidHom =
      pointwiseStabilizer b (W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V)) := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_pointwiseStabilizer,
    mem_pointwiseStabilizer]
  constructor
  · rintro h _ ⟨w, hw, rfl⟩
    have h1 : (((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) ((((x : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w)) =
        w := h w hw
    calc (((x : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) =
        ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
            V →ₗ[ZMod 2] V) ((((x : bilinIsometryGroup b) :
              LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
                (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w))) :=
          (apply_inv_apply g _).symm
      _ = ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w := by rw [h1]
  · intro h w hw
    have h1 := h _ ⟨w, hw, rfl⟩
    change (((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) ((((x : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w)) = w
    rw [h1, inv_apply_apply]

theorem isTotallyIsotropic_map (g : bilinIsometryGroup b) {W : Submodule (ZMod 2) V}
    (hW : IsTotallyIsotropic b W) :
    IsTotallyIsotropic b (W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [g.2 x y]
  exact hW x hx y hy

theorem finrank_map_eq (g : bilinIsometryGroup b) (W : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) = finrank (ZMod 2) W :=
  LinearEquiv.finrank_map_eq
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (g : LinearMap.GeneralLinearGroup
      (ZMod 2) V)) W

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
