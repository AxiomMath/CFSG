module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherCommonBasis
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherInvariant

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl

variable {r : ℕ} {K : Type} [Field K]

theorem flag_eq_span (i : ℕ) :
    flag r K i = span K ((fun x => (Pi.single x (1 : K) : Fin r ⊕ Fin r → K)) ''
      {x | (flagOrder r x : ℕ) < i}) := by
  apply le_antisymm
  · intro v hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun x _ => ?_
    by_cases hx : (flagOrder r x : ℕ) < i
    · have : (Pi.single x (v x) : Fin r ⊕ Fin r → K) = v x • Pi.single x 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact smul_mem _ _ (subset_span ⟨x, hx, rfl⟩)
    · rw [mem_flag_iff.mp hv x (not_lt.mp hx), Pi.single_zero]
      exact zero_mem _
  · rw [span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine mem_flag_iff.mpr fun y hy => ?_
    have hxy : y ≠ x := fun h => by rw [h] at hy; exact absurd hx (not_lt.mpr hy)
    simp [hxy]

theorem pairedSympForm_single_apply (x : Fin r ⊕ Fin r) (v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (Pi.single x 1) v = lineSign K x * v x.swap := by
  rcases x with i | i
  · rw [pairedSympForm_single_inl]
    simp [lineSign]
  · rw [pairedSympForm_apply]
    simp [dotProduct, Pi.single_apply, lineSign]

theorem flagOrder_swap' (x : Fin r ⊕ Fin r) :
    (flagOrder r x.swap : ℕ) = 2 * r - 1 - flagOrder r x := by
  rcases x with i | i <;> simp only [Sum.swap_inl, Sum.swap_inr, flagOrder_inl, flagOrder_inr] <;>
    have := i.2 <;> omega

theorem finrank_flag {i : ℕ} (hi : i ≤ 2 * r) : finrank K (flag r K i) = i := by
  set u : Fin (2 * r) → Fin r ⊕ Fin r → K :=
    ⇑(Pi.basisFun K (Fin r ⊕ Fin r)) ∘ (flagOrder r).symm
  have hu : LinearIndependent K u :=
    (Pi.basisFun K (Fin r ⊕ Fin r)).linearIndependent.comp _ (flagOrder r).symm.injective
  have himage : u '' {a : Fin (2 * r) | (a : ℕ) < i} =
      (fun x => (Pi.single x (1 : K) : Fin r ⊕ Fin r → K)) '' {x | (flagOrder r x : ℕ) < i} := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨(flagOrder r).symm a, by simpa using ha, ?_⟩
      simp only [u, Function.comp_apply, Pi.basisFun_apply]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨flagOrder r x, hx, ?_⟩
      simp only [u, Function.comp_apply, Equiv.symm_apply_apply, Pi.basisFun_apply]
  rw [flag_eq_span, ← himage, finrank_span_image_lt hu hi]

theorem isSelfDualFlag_flag : IsSelfDualFlag (pairedSympForm K r) r (flag r K) := by
  refine ⟨fun i hi => finrank_flag hi, fun i _ => flag_mono (Nat.le_succ i), fun i hi => ?_⟩
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_flag_iff]
  constructor
  · intro h y hy
    have h1 := h (Pi.single y.swap 1) (by
      rw [flag_eq_span]
      refine subset_span ⟨y.swap, ?_, rfl⟩
      change (flagOrder r y.swap : ℕ) < i
      rw [flagOrder_swap']
      have := (flagOrder r y).2
      omega)
    rw [pairedSympForm_single_apply, Sum.swap_swap] at h1
    exact (mul_eq_zero.mp h1).resolve_left (lineSign_ne_zero _)
  · intro h u hu
    rw [flag_eq_span] at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [pairedSympForm_single_apply, h x.swap (by
        rw [flagOrder_swap']
        change (flagOrder r x : ℕ) < i at hx
        have := (flagOrder r x).2
        omega), mul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem pairedSympForm_mulVec (g : StatedSp r K) (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r
      (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u)
      (((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) =
      pairedSympForm K r u v := by
  have hg := mem_statedSp_iff.mp g.2
  set M := ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  simp only [pairedSympForm, toBilin'_apply']
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, hg,
    ← dotProduct_mulVec]

theorem isSelfDualFlag_map (g : StatedSp r K) :
    IsSelfDualFlag (pairedSympForm K r) r fun i => (flag r K i).map
      (mulVecLin ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
  set M := ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  set Mi := (((g⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have hMi : ∀ v, M *ᵥ (Mi *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one, one_mulVec]
  have hinj : Function.Injective (mulVecLin M) := fun u v h => by
    have := congrArg (mulVecLin Mi) h
    simp only [mulVecLin_apply, mulVec_mulVec] at this
    rwa [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
      one_mulVec, one_mulVec] at this
  have hF := isSelfDualFlag_flag (r := r) (K := K)
  refine ⟨fun i hi => ?_, fun i hi => map_mono (hF.2.1 i hi), fun i hi => ?_⟩
  · rw [← (Submodule.equivMapOfInjective _ hinj (flag r K i)).finrank_eq, hF.1 i hi]
  · ext v
    change v ∈ (pairedSympForm K r).orthogonal ((flag r K i).map (mulVecLin M)) ↔
      v ∈ (flag r K (2 * r - i)).map (mulVecLin M)
    rw [LinearMap.BilinForm.mem_orthogonal_iff, ← hF.2.2 i hi]
    constructor
    · intro h
      refine ⟨Mi *ᵥ v, LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_, hMi v⟩
      have := h (M *ᵥ u) ⟨u, hu, rfl⟩
      rwa [← hMi v, pairedSympForm_mulVec] at this
    · rintro ⟨w, hw, rfl⟩ _ ⟨u, hu, rfl⟩
      rw [mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
      exact hw u hu

variable (K) in
@[expose] def spBruhatCell (w : signedPermGroup r) : Set (StatedSp r K) :=
  {g | ∃ b₁ ∈ borelSubgroup r K, ∃ b₂ ∈ borelSubgroup r K, g = b₁ * dotW K w * b₂}

abbrev spAct (g : StatedSp r K) : (Fin r ⊕ Fin r → K) →ₗ[K] Fin r ⊕ Fin r → K :=
  mulVecLin ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

theorem map_spAct_mul (g h : StatedSp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    W.map (spAct (g * h)) = (W.map (spAct h)).map (spAct g) := by
  rw [spAct, spAct, spAct, Subgroup.coe_mul, Units.val_mul, mulVecLin_mul, Submodule.map_comp]

theorem map_spAct_one (W : Submodule K (Fin r ⊕ Fin r → K)) :
    W.map (spAct (1 : StatedSp r K)) = W := by
  rw [spAct, Subgroup.coe_one, Units.val_one, mulVecLin_one, Submodule.map_id]

theorem map_spAct_inv (g : StatedSp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (W.map (spAct g)).map (spAct g⁻¹) = W := by
  rw [← map_spAct_mul, inv_mul_cancel, map_spAct_one]

theorem flag_eq_span_basisFun (i : ℕ) :
    flag r K i = span K (⇑(Pi.basisFun K (Fin r ⊕ Fin r)) '' {x | (flagOrder r x : ℕ) < i}) := by
  rw [flag_eq_span]
  congr 2
  funext x
  exact (Pi.basisFun_apply K (Fin r ⊕ Fin r) x).symm

theorem exists_inl_of_flagOrder_lt {i : ℕ} (hi : i ≤ r) {x : Fin r ⊕ Fin r}
    (hx : (flagOrder r x : ℕ) < i) : ∃ j : Fin r, x = Sum.inl j ∧ (j : ℕ) < i := by
  rcases x with j | j
  · exact ⟨j, rfl, by rwa [flagOrder_inl] at hx⟩
  · rw [flagOrder_inr] at hx
    omega

theorem exists_mem_spBruhatCell (g : StatedSp r K) :
    ∃ w : signedPermGroup r, g ∈ spBruhatCell K w := by
  classical
  have hF := isSelfDualFlag_flag (r := r) (K := K)
  have hG := isSelfDualFlag_map g
  obtain ⟨b, hb, hbF, hbG⟩ := common_symplectic_flag_basis pairedSympForm_isAlt
    pairedSympForm_nondegenerate finrank_standard hF hG
  have hstd : IsSymplecticBasis (pairedSympForm K r) (Pi.basisFun K (Fin r ⊕ Fin r)) :=
    toMatrix_pairedSympForm
  obtain ⟨β, hβ⟩ := exists_statedSp_mulVec_basis hstd hb
  set e := Pi.basisFun K (Fin r ⊕ Fin r)
  have hβF : ∀ i ≤ 2 * r, (flag r K i).map (spAct β) = flag r K i := by
    intro i hi
    conv_lhs => rw [flag_eq_span_basisFun]
    rw [map_span_basis hβ, ← hbF i hi]
  have hβB : β ∈ borelSubgroup r K :=
    mem_borelSubgroup.mpr fun i _ hi => mem_stabilizer.mpr (hβF i (by omega))
  have hβinv : ∀ x, (((β⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ b x = e x := by
    intro x
    rw [← hβ x, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, one_mulVec]
  set C : ℕ → Set (Fin r ⊕ Fin r) := fun i => {x | b x ∈ (flag r K i).map (spAct g)}
  have hh : ∀ i ≤ 2 * r, (flag r K i).map (spAct (β⁻¹ * g)) = span K (e '' C i) := by
    intro i hi
    rw [map_spAct_mul, hbG i hi]
    exact map_span_basis hβinv _
  have hfin : ∀ i ≤ 2 * r, finrank K (span K (e '' C i)) = i := by
    intro i hi
    rw [← hh i hi]
    exact (isSelfDualFlag_map (β⁻¹ * g)).1 i hi
  have hmemC : ∀ i ≤ 2 * r, ∀ x, x ∈ C i ↔ e x ∈ span K (e '' C i) := fun i _ x =>
    (Basis.self_mem_span_image e).symm
  have hCmono : ∀ {i i' : ℕ}, i ≤ i' → i' ≤ 2 * r → C i ⊆ C i' := by
    intro i i' hii' hi' x hx
    exact map_mono (flag_mono hii') hx
  have hiso : ∀ x ∈ C r, x.swap ∉ C r := by
    intro x hx hx'
    have hGr : (pairedSympForm K r).orthogonal ((flag r K r).map (spAct g)) =
        (flag r K r).map (spAct g) := by
      have := hG.2.2 r (by omega)
      rwa [show 2 * r - r = r by omega] at this
    have h0 : pairedSympForm K r (b x) (b x.swap) = 0 := by
      have : b x.swap ∈ (pairedSympForm K r).orthogonal ((flag r K r).map (spAct g)) := by
        rw [hGr]
        exact hx'
      exact this (b x) hx
    have h1 := congrFun₂ hb x x.swap
    rw [LinearMap.BilinForm.toMatrix_apply, h0, J_apply, ite_eq_left rfl] at h1
    exact lineSign_ne_zero x h1.symm
  have hnew : ∀ j : Fin r, ∃ x, x ∈ C (j + 1) ∧ x ∉ C j := by
    intro j
    by_contra! hsub
    have hle : span K (e '' C (j + 1)) ≤ span K (e '' C j) :=
      span_mono (Set.image_mono fun x hx => hsub x hx)
    have := Submodule.finrank_mono hle
    rw [hfin (j + 1) (by omega), hfin j (by omega)] at this
    omega
  choose y hy using hnew
  have hyC : ∀ j : Fin r, y j ∈ C r := fun j =>
    hCmono (i := j + 1) (i' := r) (by have := j.2; omega) (by omega) (hy j).1
  have hyinj : Function.Injective y := by
    intro j j' hjj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h' := Fin.lt_def.mp h
      exact (hy j').2 (hjj' ▸ hCmono (i := j + 1) (i' := j') (by omega)
        (by have := j'.2; omega) (hy j).1)
    · have h' := Fin.lt_def.mp h
      exact (hy j).2 (hjj' ▸ hCmono (i := j' + 1) (i' := j) (by omega)
        (by have := j.2; omega) (hy j').1)
  set f : Fin r ⊕ Fin r → Fin r ⊕ Fin r := Sum.elim y fun j => (y j).swap with hf
  have hfinj : Function.Injective f := by
    rintro (j | j) (j' | j') h <;> simp only [hf, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (hyinj h)
    · exact absurd (h ▸ hyC j) (hiso _ (hyC j'))
    · exact absurd (h.symm ▸ hyC j') (hiso _ (hyC j))
    · exact congrArg Sum.inr (hyinj (swap_injective' h))
  set w : Equiv.Perm (Fin r ⊕ Fin r) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hw : w ∈ signedPermGroup r := by
    rintro (j | j)
    · rfl
    · exact (Sum.swap_swap _).symm
  set w' : signedPermGroup r := ⟨w, hw⟩
  have hwF : ∀ i ≤ r, (flag r K i).map (spAct (dotW K w')) = span K (e '' C i) := by
    intro i hi
    refine eq_of_le_of_finrank_eq ?_ ?_
    · rw [flag_eq_span_basisFun, map_span, span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨j, rfl, hj⟩ := exists_inl_of_flagOrder_lt hi hx
      change (((dotW K w' : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ e (Sum.inl j) ∈ _
      rw [Pi.basisFun_apply, dotW_mulVec_single]
      refine smul_mem _ _ ?_
      rw [← Pi.basisFun_apply K]
      exact (Basis.self_mem_span_image e).mpr (hCmono (by omega) (by omega) (hy j).1)
    · rw [hfin i (by omega)]
      exact (isSelfDualFlag_map (dotW K w')).1 i (by omega)
  have hrest : (dotW K w')⁻¹ * (β⁻¹ * g) ∈ borelSubgroup r K := by
    refine mem_borelSubgroup.mpr fun i _ hi => mem_stabilizer.mpr ?_
    rw [map_spAct_mul, hh i (by omega), ← hwF i hi, map_spAct_inv]
  refine ⟨w', β, hβB, _, hrest, ?_⟩
  group

@[expose] def flagPerm (w : Equiv.Perm (Fin r ⊕ Fin r)) : Equiv.Perm (Fin (2 * r)) :=
  (flagOrder r).symm.trans (w.trans (flagOrder r))

theorem flagPerm_injective : Function.Injective (flagPerm (r := r)) := by
  intro w w' h
  ext x
  have := congrArg (fun σ : Equiv.Perm (Fin (2 * r)) => σ (flagOrder r x)) h
  simpa [flagPerm] using this

theorem reindex_dotW (w : signedPermGroup r) :
    reindex (flagOrder r) (flagOrder r) (((dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      LinearFlag.permMatrix (2 * r) K (flagPerm (w : Equiv.Perm (Fin r ⊕ Fin r))) *
        diagonal fun a =>
          dotSign (K := K) (w : Equiv.Perm (Fin r ⊕ Fin r)) ((flagOrder r).symm a) := by
  ext a c
  rw [reindex_apply, submatrix_apply, coe_dotW,
    CFSG.LieType.Universal.SpecialLinear.signedPerm_apply, mul_diagonal,
    LinearFlag.permMatrix_apply]
  have hiff : (flagOrder r).symm a = (w : Equiv.Perm (Fin r ⊕ Fin r)) ((flagOrder r).symm c) ↔
      a = flagPerm (w : Equiv.Perm (Fin r ⊕ Fin r)) c := by
    simp only [flagPerm, Equiv.trans_apply]
    constructor
    · intro h
      rw [← h, Equiv.apply_symm_apply]
    · rintro rfl
      rw [Equiv.symm_apply_apply]
  by_cases h : a = flagPerm (w : Equiv.Perm (Fin r ⊕ Fin r)) c
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h, one_mul]
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h, zero_mul]

theorem dotSign_ne_zero (w : Equiv.Perm (Fin r ⊕ Fin r)) (x : Fin r ⊕ Fin r) :
    dotSign (K := K) w x ≠ 0 := fun h => by
  have := dotSign_mul_self (K := K) w x
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem cornerRank_dotW (w : signedPermGroup r) (i j : ℕ) :
    LinearFlag.cornerRank (reindex (flagOrder r) (flagOrder r) (((dotW K w : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) i j =
      LinearFlag.cornerCount (flagPerm (w : Equiv.Perm (Fin r ⊕ Fin r))) i j := by
  rw [reindex_dotW, LinearFlag.cornerRank_mul_right, LinearFlag.cornerRank_permMatrix]
  · exact fun a c hac => diagonal_apply_ne _ (ne_of_gt hac)
  · intro a
    rw [diagonal_apply_eq]
    exact dotSign_ne_zero _ _

theorem reindex_of_mem_borelSubgroup {b : StatedSp r K} (hb : b ∈ borelSubgroup r K) :
    (reindex (flagOrder r) (flagOrder r) ((b : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).IsUpperTriangular ∧
    ∀ a, reindex (flagOrder r) (flagOrder r) ((b : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a a ≠ 0 := by
  have htri := mem_borelSubgroup_iff_reindex.mp hb
  refine ⟨htri, fun a => ?_⟩
  have hdet : (reindex (flagOrder r) (flagOrder r) ((b : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).det ≠ 0 := by
    rw [det_reindex_self]
    exact ((b : GL (Fin r ⊕ Fin r) K).isUnit.map Matrix.detMonoidHom).ne_zero
  rw [det_of_isUpperTriangular htri] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet a (Finset.mem_univ a)

theorem reindex_mul_reindex {n : Type*} [Fintype n] [DecidableEq n] (e : Fin r ⊕ Fin r ≃ n)
    (M N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    reindex e e (M * N) = reindex e e M * reindex e e N := by
  rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

theorem cornerRank_of_mem_spBruhatCell {g : StatedSp r K} {w : signedPermGroup r}
    (hg : g ∈ spBruhatCell K w) (i j : ℕ) :
    LinearFlag.cornerRank (reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) i j =
      LinearFlag.cornerCount (flagPerm (w : Equiv.Perm (Fin r ⊕ Fin r))) i j := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  obtain ⟨h1, h1'⟩ := reindex_of_mem_borelSubgroup hb₁
  obtain ⟨h2, h2'⟩ := reindex_of_mem_borelSubgroup hb₂
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [reindex_mul_reindex, reindex_mul_reindex, LinearFlag.cornerRank_mul_right h2 h2',
    LinearFlag.cornerRank_mul_left h1 h1', cornerRank_dotW]

theorem symplectic_bruhat :
    (∀ g : StatedSp r K, ∃ w : signedPermGroup r, g ∈ spBruhatCell K w) ∧
    (∀ (g : StatedSp r K) (w w' : signedPermGroup r),
      g ∈ spBruhatCell K w → g ∈ spBruhatCell K w' → w = w') ∧
    (∀ (g : StatedSp r K) (w : signedPermGroup r), g ∈ spBruhatCell K w ↔
      ∀ i j : ℕ, 1 ≤ i → i ≤ 2 * r → 1 ≤ j → j ≤ 2 * r →
        LinearFlag.cornerRank (reindex (flagOrder r) (flagOrder r) ((g : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) i j =
          LinearFlag.cornerCount (flagPerm (w : Equiv.Perm (Fin r ⊕ Fin r))) i j) := by
  have huniq : ∀ (g : StatedSp r K) (w w' : signedPermGroup r),
      g ∈ spBruhatCell K w → g ∈ spBruhatCell K w' → w = w' := by
    intro g w w' hw hw'
    apply Subtype.ext
    apply flagPerm_injective
    exact LinearFlag.eq_of_cornerCount_eq fun i j _ _ _ _ =>
      (cornerRank_of_mem_spBruhatCell hw i j).symm.trans (cornerRank_of_mem_spBruhatCell hw' i j)
  refine ⟨exists_mem_spBruhatCell, huniq, fun g w => ⟨fun hg i j _ _ _ _ =>
    cornerRank_of_mem_spBruhatCell hg i j, fun h => ?_⟩⟩
  obtain ⟨w', hw'⟩ := exists_mem_spBruhatCell g
  have : w = w' := by
    apply Subtype.ext
    apply flagPerm_injective
    exact LinearFlag.eq_of_cornerCount_eq fun i j hi hin hj hjn =>
      (h i j hi hin hj hjn).symm.trans (cornerRank_of_mem_spBruhatCell hw' i j)
  rwa [this]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
