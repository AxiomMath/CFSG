module

public import CFSG.LieType.SteinbergBRBlockParabolic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type*} [Field F] {n d e : ℕ}

@[expose] def sumEquiv (h : d + e = n) : Fin d ⊕ Fin e ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

theorem sumEquiv_inl (h : d + e = n) (i : Fin d) : (sumEquiv h (Sum.inl i) : ℕ) = i := by
  simp [sumEquiv]

theorem sumEquiv_inr (h : d + e = n) (j : Fin e) : (sumEquiv h (Sum.inr j) : ℕ) = d + j := by
  simp [sumEquiv]

variable (F) in
@[expose] noncomputable def reindexSL (h : d + e = n) :
    SpecialLinearGroup (Fin d ⊕ Fin e) F ≃* SpecialLinearGroup (Fin n) F where
  toFun M := ⟨reindex (sumEquiv h) (sumEquiv h) M.val, by rw [det_reindex_self, M.prop]⟩
  invFun M := ⟨reindex (sumEquiv h).symm (sumEquiv h).symm M.val, by rw [det_reindex_self, M.prop]⟩
  left_inv M := Subtype.ext (by simp)
  right_inv M := Subtype.ext (by simp)
  map_mul' M N := Subtype.ext ((reindexAlgEquiv F F (sumEquiv h)).map_mul M.val N.val)

theorem reindexSL_val (h : d + e = n) (M : SpecialLinearGroup (Fin d ⊕ Fin e) F) :
    (reindexSL F h M).val = reindex (sumEquiv h) (sumEquiv h) M.val :=
  rfl

theorem single_mem_flagSpace' {i : Fin n} (hi : (i : ℕ) < d) :
    (Pi.single i (1 : F) : Fin n → F) ∈ flagSpace n F d :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem map_le_flagSpace_iff (g : Matrix (Fin n) (Fin n) F) :
    (flagSpace n F d).map (mulVecLin g) ≤ flagSpace n F d ↔
      ∀ i j : Fin n, d ≤ (i : ℕ) → (j : ℕ) < d → g i j = 0 := by
  constructor
  · intro h i j hi hj
    have hmem : g *ᵥ (Pi.single j 1) ∈ flagSpace n F d := h ⟨_, single_mem_flagSpace' hj, rfl⟩
    have := (mem_flagSpace.1 hmem) i hi
    rwa [mulVec_single_one, col_apply] at this
  · rintro h _ ⟨v, hv, rfl⟩
    rw [mem_flagSpace]
    intro i hi
    rw [mulVecLin_apply, mulVec, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < d
    · rw [h i k hi hk, zero_mul]
    · rw [(mem_flagSpace.1 hv) k (not_lt.1 hk), mul_zero]

theorem mem_stabilizer_iff_map_le {W : Submodule F (Fin n → F)}
    {g : SpecialLinearGroup (Fin n) F} :
    g ∈ stabilizer W ↔ W.map (mulVecLin g.val) ≤ W := by
  refine ⟨fun hg => le_of_eq hg, fun hle => ?_⟩
  have hinv : Invertible g.val :=
    Matrix.invertibleOfIsUnitDet g.val (by rw [g.prop]; exact isUnit_one)
  have hfin : finrank F (W.map (mulVecLin g.val)) = finrank F W := by
    have := LinearEquiv.finrank_map_eq (g.val.toLinearEquiv' hinv) W
    exact this
  exact Submodule.eq_of_le_of_finrank_eq hle hfin

theorem mem_stabilizer_flagSpace_iff {g : SpecialLinearGroup (Fin n) F} :
    g ∈ stabilizer (flagSpace n F d) ↔
      ∀ i j : Fin n, d ≤ (i : ℕ) → (j : ℕ) < d → g.val i j = 0 := by
  rw [mem_stabilizer_iff_map_le, map_le_flagSpace_iff]

theorem mem_parQ_iff_reindex (h : d + e = n) (M : SpecialLinearGroup (Fin d ⊕ Fin e) F) :
    M ∈ parQ ↔ reindexSL F h M ∈ stabilizer (flagSpace n F d) := by
  rw [mem_stabilizer_flagSpace_iff, mem_parQ]
  constructor
  · intro hM i j hi hj
    rw [reindexSL_val, reindex_apply, submatrix_apply]
    obtain ⟨x, rfl⟩ := (sumEquiv h).surjective i
    obtain ⟨y, rfl⟩ := (sumEquiv h).surjective j
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases x with x | x
    · rw [sumEquiv_inl] at hi
      exact absurd hi (not_le.2 x.2)
    rcases y with y | y
    · exact congrFun₂ hM x y
    · rw [sumEquiv_inr] at hj
      omega
  · intro hM
    ext x y
    have := hM (sumEquiv h (Sum.inr x)) (sumEquiv h (Sum.inl y))
      (by rw [sumEquiv_inr]; omega) (by rw [sumEquiv_inl]; exact y.2)
    rwa [reindexSL_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] at this

theorem inv_val_mulVec_val_mulVec (g : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    (g⁻¹).val *ᵥ (g.val *ᵥ v) = v := by
  rw [mulVec_mulVec, inv_val_mul_val, one_mulVec]

theorem val_mulVec_inv_val_mulVec (g : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    g.val *ᵥ ((g⁻¹).val *ᵥ v) = v := by
  rw [mulVec_mulVec, val_mul_inv_val, one_mulVec]

variable (F) in
@[expose] def radU (W : Submodule F (Fin n → F)) : Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | (∀ v, g.val *ᵥ v - v ∈ W) ∧ ∀ w ∈ W, g.val *ᵥ w = w}
  one_mem' := ⟨fun v => by simp, fun w _ => by simp⟩
  mul_mem' {g h} hg hh := by
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have e : (g * h).val *ᵥ v - v = (g.val *ᵥ (h.val *ᵥ v) - h.val *ᵥ v) + (h.val *ᵥ v - v) := by
        rw [show (g * h).val = g.val * h.val from rfl, ← mulVec_mulVec]
        abel
      rw [e]
      exact W.add_mem (hg.1 _) (hh.1 v)
    · rw [show (g * h).val = g.val * h.val from rfl, ← mulVec_mulVec, hh.2 w hw, hg.2 w hw]
  inv_mem' {g} hg := by
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have h1 := hg.1 ((g⁻¹).val *ᵥ v)
      rw [val_mulVec_inv_val_mulVec] at h1
      have h2 := W.neg_mem h1
      rwa [neg_sub] at h2
    · have e := inv_val_mulVec_val_mulVec g w
      rwa [hg.2 w hw] at e

theorem mem_radU {W : Submodule F (Fin n → F)} {g : SpecialLinearGroup (Fin n) F} :
    g ∈ radU F W ↔ (∀ v, g.val *ᵥ v - v ∈ W) ∧ ∀ w ∈ W, g.val *ᵥ w = w :=
  Iff.rfl

theorem mem_map_iff_inv {s : SpecialLinearGroup (Fin n) F} {X : Submodule F (Fin n → F)}
    {x : Fin n → F} : x ∈ X.map (mulVecLin s.val) ↔ (s⁻¹).val *ᵥ x ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, inv_val_mulVec_val_mulVec]
    exact hy
  · intro hx
    exact ⟨_, hx, by rw [mulVecLin_apply, val_mulVec_inv_val_mulVec]⟩

theorem conj_mulVec (s g : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    (s⁻¹ * g * s).val *ᵥ v = (s⁻¹).val *ᵥ (g.val *ᵥ (s.val *ᵥ v)) := by
  rw [show (s⁻¹ * g * s).val = (s⁻¹).val * g.val * s.val from rfl, ← mulVec_mulVec,
    ← mulVec_mulVec]

theorem mem_stabilizer_iff_conj {s : SpecialLinearGroup (Fin n) F} {W : Submodule F (Fin n → F)}
    (hs : (flagSpace n F d).map (mulVecLin s.val) = W) (g : SpecialLinearGroup (Fin n) F) :
    g ∈ stabilizer W ↔ s⁻¹ * g * s ∈ stabilizer (flagSpace n F d) := by
  rw [mem_stabilizer_iff_map_le, mem_stabilizer_iff_map_le]
  constructor
  · rintro h _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply, conj_mulVec]
    have h1 : s.val *ᵥ v ∈ W := hs ▸ ⟨v, hv, rfl⟩
    have h2 : g.val *ᵥ (s.val *ᵥ v) ∈ W := h ⟨_, h1, rfl⟩
    rw [← hs] at h2
    exact mem_map_iff_inv.1 h2
  · rintro h _ ⟨w, hw, rfl⟩
    have hw1 : w ∈ (flagSpace n F d).map (mulVecLin s.val) := by rw [hs]; exact hw
    have hw2 : (s⁻¹).val *ᵥ w ∈ flagSpace n F d := mem_map_iff_inv.1 hw1
    have h1 := h ⟨_, hw2, rfl⟩
    rw [mulVecLin_apply, conj_mulVec, val_mulVec_inv_val_mulVec] at h1
    rw [← hs]
    exact mem_map_iff_inv.2 h1

theorem mem_radU_iff_conj {s : SpecialLinearGroup (Fin n) F} {W : Submodule F (Fin n → F)}
    (hs : (flagSpace n F d).map (mulVecLin s.val) = W) (g : SpecialLinearGroup (Fin n) F) :
    g ∈ radU F W ↔ s⁻¹ * g * s ∈ radU F (flagSpace n F d) := by
  rw [mem_radU, mem_radU]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have := h1 (s.val *ᵥ v)
      rw [← hs, mem_map_iff_inv, mulVec_sub, inv_val_mulVec_val_mulVec] at this
      rw [conj_mulVec]
      exact this
    · have hw' : s.val *ᵥ w ∈ W := hs ▸ ⟨w, hw, rfl⟩
      rw [conj_mulVec, h2 _ hw', inv_val_mulVec_val_mulVec]
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have := h1 ((s⁻¹).val *ᵥ v)
      rw [conj_mulVec, val_mulVec_inv_val_mulVec] at this
      rw [← hs, mem_map_iff_inv, mulVec_sub]
      exact this
    · rw [← hs, mem_map_iff_inv] at hw
      have := h2 _ hw
      rw [conj_mulVec, val_mulVec_inv_val_mulVec] at this
      calc g.val *ᵥ w = s.val *ᵥ ((s⁻¹).val *ᵥ (g.val *ᵥ w)) := (val_mulVec_inv_val_mulVec s _).symm
        _ = s.val *ᵥ ((s⁻¹).val *ᵥ w) := by rw [this]
        _ = w := val_mulVec_inv_val_mulVec s w

theorem forall_sub_mem_flagSpace_iff (g : Matrix (Fin n) (Fin n) F) :
    (∀ v, g *ᵥ v - v ∈ flagSpace n F d) ↔
      ∀ i j : Fin n, d ≤ (i : ℕ) → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · intro h i j hi
    have := (mem_flagSpace.1 (h (Pi.single j 1))) i hi
    rw [Pi.sub_apply, mulVec_single_one, col_apply, sub_eq_zero] at this
    rw [this, one_apply, Pi.single_apply]
  · intro h v
    rw [mem_flagSpace]
    intro i hi
    have e : g *ᵥ v - v = (g - 1) *ᵥ v := by rw [sub_mulVec, one_mulVec]
    rw [e, mulVec, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.sub_apply, h i k hi, sub_self, zero_mul]

theorem forall_mulVec_eq_iff (g : Matrix (Fin n) (Fin n) F) :
    (∀ w ∈ flagSpace n F d, g *ᵥ w = w) ↔
      ∀ i j : Fin n, (j : ℕ) < d → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · intro h i j hj
    have := congrFun (h _ (single_mem_flagSpace' hj)) i
    rw [mulVec_single_one, col_apply] at this
    rw [this, one_apply, Pi.single_apply]
  · intro h w hw
    have e : g *ᵥ w = (g - 1) *ᵥ w + w := by rw [sub_mulVec, one_mulVec, sub_add_cancel]
    rw [e, add_eq_right]
    funext i
    rw [mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < d
    · rw [Matrix.sub_apply, h i k hk, sub_self, zero_mul]
    · rw [(mem_flagSpace.1 hw) k (not_lt.1 hk), mul_zero]

theorem mem_radU_flagSpace_iff (h : d + e = n) (M : SpecialLinearGroup (Fin d ⊕ Fin e) F) :
    reindexSL F h M ∈ radU F (flagSpace n F d) ↔ M ∈ (uniHom F (Fin d) (Fin e)).range := by
  rw [mem_radU, reindexSL_val, forall_sub_mem_flagSpace_iff, forall_mulVec_eq_iff]
  have key : ∀ x y : Fin d ⊕ Fin e, (reindex (sumEquiv h) (sumEquiv h) M.val)
      (sumEquiv h x) (sumEquiv h y) = M.val x y := fun x y => by
    rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have key1 : ∀ x y : Fin d ⊕ Fin e, (1 : Matrix (Fin n) (Fin n) F) (sumEquiv h x)
      (sumEquiv h y) = (1 : Matrix (Fin d ⊕ Fin e) (Fin d ⊕ Fin e) F) x y := fun x y => by
    by_cases hxy : x = y
    · subst hxy
      rw [one_apply_eq, one_apply_eq]
    · rw [one_apply_ne ((sumEquiv h).injective.ne hxy), one_apply_ne hxy]
  constructor
  · rintro ⟨h1, h2⟩
    have hM : M.val = fromBlocks 1 M.val.toBlocks₁₂ 0 1 := by
      conv_lhs => rw [← fromBlocks_toBlocks M.val]
      congr 1
      · ext i j
        have := h2 (sumEquiv h (Sum.inl i)) (sumEquiv h (Sum.inl j))
          (by rw [sumEquiv_inl]; exact j.2)
        rw [key, key1] at this
        simpa [toBlocks₁₁, one_apply] using this
      · ext i j
        have := h1 (sumEquiv h (Sum.inr i)) (sumEquiv h (Sum.inl j)) (by rw [sumEquiv_inr]; omega)
        rw [key, key1] at this
        simpa [toBlocks₂₁, one_apply] using this
      · ext i j
        have := h1 (sumEquiv h (Sum.inr i)) (sumEquiv h (Sum.inr j)) (by rw [sumEquiv_inr]; omega)
        rw [key, key1] at this
        simpa [toBlocks₂₂, one_apply] using this
    exact ⟨Multiplicative.ofAdd M.val.toBlocks₁₂, Subtype.ext hM.symm⟩
  · rintro ⟨x, rfl⟩
    have hval := uniHom_val (F := F) (a := Fin d) (b := Fin e) (Multiplicative.toAdd x)
    refine ⟨fun i j hi => ?_, fun i j hj => ?_⟩
    · obtain ⟨u, rfl⟩ := (sumEquiv h).surjective i
      obtain ⟨w, rfl⟩ := (sumEquiv h).surjective j
      rw [key, key1]
      change (uniHom F (Fin d) (Fin e) (Multiplicative.ofAdd (Multiplicative.toAdd x))).val u w = _
      rw [hval]
      rcases u with u | u
      · rw [sumEquiv_inl] at hi
        exact absurd hi (not_le.2 u.2)
      rcases w with w | w <;> simp [fromBlocks, one_apply]
    · obtain ⟨u, rfl⟩ := (sumEquiv h).surjective i
      obtain ⟨w, rfl⟩ := (sumEquiv h).surjective j
      rw [key, key1]
      change (uniHom F (Fin d) (Fin e) (Multiplicative.ofAdd (Multiplicative.toAdd x))).val u w = _
      rw [hval]
      rcases w with w | w
      · rcases u with u | u <;> simp [fromBlocks, one_apply]
      · rw [sumEquiv_inr] at hj
        omega

variable (F) in
@[expose] noncomputable def transportSL (h : d + e = n) (s : SpecialLinearGroup (Fin n) F) :
    SpecialLinearGroup (Fin d ⊕ Fin e) F ≃* SpecialLinearGroup (Fin n) F :=
  (reindexSL F h).trans (MulAut.conj s)

theorem transportSL_apply (h : d + e = n) (s : SpecialLinearGroup (Fin n) F)
    (M : SpecialLinearGroup (Fin d ⊕ Fin e) F) :
    transportSL F h s M = s * reindexSL F h M * s⁻¹ :=
  rfl

theorem conj_transportSL (h : d + e = n) (s : SpecialLinearGroup (Fin n) F)
    (M : SpecialLinearGroup (Fin d ⊕ Fin e) F) :
    s⁻¹ * transportSL F h s M * s = reindexSL F h M := by
  rw [transportSL_apply]
  group

theorem mem_parQ_iff_transport (h : d + e = n) {s : SpecialLinearGroup (Fin n) F}
    {W : Submodule F (Fin n → F)} (hs : (flagSpace n F d).map (mulVecLin s.val) = W)
    (M : SpecialLinearGroup (Fin d ⊕ Fin e) F) :
    M ∈ parQ ↔ transportSL F h s M ∈ stabilizer W := by
  rw [mem_stabilizer_iff_conj hs, conj_transportSL, ← mem_parQ_iff_reindex]

theorem mem_radU_iff_transport (h : d + e = n) {s : SpecialLinearGroup (Fin n) F}
    {W : Submodule F (Fin n → F)} (hs : (flagSpace n F d).map (mulVecLin s.val) = W)
    (M : SpecialLinearGroup (Fin d ⊕ Fin e) F) :
    M ∈ (uniHom F (Fin d) (Fin e)).range ↔ transportSL F h s M ∈ radU F W := by
  rw [mem_radU_iff_conj hs, conj_transportSL, mem_radU_flagSpace_iff]

theorem map_parQ_transport (h : d + e = n) {s : SpecialLinearGroup (Fin n) F}
    {W : Submodule F (Fin n → F)} (hs : (flagSpace n F d).map (mulVecLin s.val) = W) :
    (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)).map
      (transportSL F h s).toMonoidHom = stabilizer W := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_parQ_iff_transport h hs, MulEquiv.apply_symm_apply]

theorem map_uniHom_range_transport (h : d + e = n) {s : SpecialLinearGroup (Fin n) F}
    {W : Submodule F (Fin n → F)} (hs : (flagSpace n F d).map (mulVecLin s.val) = W) :
    (uniHom F (Fin d) (Fin e)).range.map (transportSL F h s).toMonoidHom = radU F W := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_radU_iff_transport h hs, MulEquiv.apply_symm_apply]

theorem transportSL_symm_scalar (h : d + e = n) (s : SpecialLinearGroup (Fin n) F)
    {g : SpecialLinearGroup (Fin n) F} {c : F} (hg : g.val = scalar (Fin n) c) :
    ((transportSL F h s).symm g).val = scalar (Fin d ⊕ Fin e) c := by
  have hcen : s⁻¹ * g * s = g := by
    apply Subtype.ext
    change (s⁻¹).val * g.val * s.val = g.val
    rw [hg, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      inv_val_mul_val]
  have e : (transportSL F h s).symm g = (reindexSL F h).symm g := by
    rw [MulEquiv.symm_apply_eq, transportSL_apply, MulEquiv.apply_symm_apply]
    calc g = s * (s⁻¹ * g * s) * s⁻¹ := by group
      _ = s * g * s⁻¹ := by rw [hcen]
  rw [e]
  change reindex (sumEquiv h).symm (sumEquiv h).symm g.val = _
  rw [hg, scalar_apply, scalar_apply, reindex_apply, submatrix_diagonal_equiv]
  rfl

end CFSG.LieType.SteinbergBR.BlockPar
