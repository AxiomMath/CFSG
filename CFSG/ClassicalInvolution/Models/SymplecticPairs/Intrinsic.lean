module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section Orth

theorem form_add_right (v a b : Fin n ⊕ Fin n → K) : form v (a + b) = form v a + form v b := by
  simp [form, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (v a : Fin n ⊕ Fin n → K) (c : K) : form v (c • a) = c * form v a := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

theorem form_add_left (a b v : Fin n ⊕ Fin n → K) : form (a + b) v = form a v + form b v := by
  simp [form, add_dotProduct]

theorem form_smul_left (a v : Fin n ⊕ Fin n → K) (c : K) : form (c • a) v = c * form a v := by
  simp [form, smul_dotProduct]

theorem form_zero_left (v : Fin n ⊕ Fin n → K) : form 0 v = 0 := by
  simp [form]

theorem form_mulVec_inv_left (g : StatedSp n K) (w u : Fin n ⊕ Fin n → K) :
    form (mat n K g⁻¹ *ᵥ w) u = form w (mat n K g *ᵥ u) :=
  calc form (mat n K g⁻¹ *ᵥ w) u
      = form (mat n K g *ᵥ (mat n K g⁻¹ *ᵥ w)) (mat n K g *ᵥ u) := (form_mulVec g _ _).symm
    _ = form w (mat n K g *ᵥ u) := by rw [mulVec_mulVec_inv]

@[expose] def orthSet (P : Set (Fin n ⊕ Fin n → K)) : Set (Fin n ⊕ Fin n → K) :=
  {v | ∀ u ∈ P, form v u = 0}

theorem form_zero_right (v : Fin n ⊕ Fin n → K) : form v 0 = 0 := by
  simp [form]

theorem mem_orthSet_span {S : Set (Fin n ⊕ Fin n → K)} {v : Fin n ⊕ Fin n → K} :
    v ∈ orthSet (Submodule.span K S : Set (Fin n ⊕ Fin n → K)) ↔ ∀ u ∈ S, form v u = 0 := by
  constructor
  · intro h u hu
    exact h u (Submodule.subset_span hu)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem u hu => exact h u hu
    | zero => exact form_zero_right v
    | add a b _ _ ha hb => rw [form_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [form_smul_right, ha, mul_zero]

theorem mem_orthSet_span_pair {u w v : Fin n ⊕ Fin n → K} :
    v ∈ orthSet (Submodule.span K {u, w} : Set (Fin n ⊕ Fin n → K)) ↔
      form v u = 0 ∧ form v w = 0 := by
  constructor
  · intro h
    exact ⟨h u (Submodule.subset_span (by simp)), h w (Submodule.subset_span (by simp))⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    rw [form_add_right, form_smul_right, form_smul_right, h1, h2]
    ring

@[expose] def IsHyperbolicPlane (P : Submodule K (Fin n ⊕ Fin n → K)) : Prop :=
  ∃ u w : Fin n ⊕ Fin n → K, form u w = 1 ∧ P = Submodule.span K {u, w}

@[expose] def planeGroup (P : Submodule K (Fin n ⊕ Fin n → K)) : Subgroup (StatedSp n K) :=
  fixing (orthSet (P : Set (Fin n ⊕ Fin n → K)))

theorem mem_span_pair_conj (g : StatedSp n K) (u w v : Fin n ⊕ Fin n → K) :
    v ∈ Submodule.span K {mat n K g *ᵥ u, mat n K g *ᵥ w} ↔
      mat n K g⁻¹ *ᵥ v ∈ Submodule.span K {u, w} := by
  rw [Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_inv_mulVec,
      mulVec_inv_mulVec]
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, ?_⟩
    have := congrArg (fun x => mat n K g *ᵥ x) h
    simp only [mulVec_mulVec_inv, Matrix.mulVec_add, Matrix.mulVec_smul] at this
    exact this

theorem planeGroup_map_conj (g : StatedSp n K) (P : Submodule K (Fin n ⊕ Fin n → K)) :
    planeGroup (P.map (Matrix.mulVecLin (mat n K g))) =
      (planeGroup P).map (MulAut.conj g).toMonoidHom := by
  refine fixing_eq_map_conj g fun v => ?_
  constructor
  · intro h u hu
    rw [form_mulVec_inv_left]
    exact h _ (Submodule.mem_map_of_mem hu)
  · intro h y hy
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
    have : form v (mat n K g *ᵥ u) = 0 := by
      rw [← form_mulVec_inv_left]
      exact h u hu
    exact this

theorem planeGroup_span_conj (g : StatedSp n K) (u w : Fin n ⊕ Fin n → K) :
    planeGroup (Submodule.span K {mat n K g *ᵥ u, mat n K g *ᵥ w}) =
      (planeGroup (Submodule.span K {u, w})).map (MulAut.conj g).toMonoidHom := by
  refine fixing_eq_map_conj g fun v => ?_
  rw [mem_orthSet_span_pair, mem_orthSet_span_pair, ← form_mulVec_inv_left g v u,
    ← form_mulVec_inv_left g v w]

end Orth

section Standard

@[expose] def stdPlane (K : Type) [Field K] (n : ℕ) (k : Fin n) :
    Submodule K (Fin n ⊕ Fin n → K) :=
  Submodule.span K {Pi.single (Sum.inl k) 1, Pi.single (Sum.inr k) 1}

theorem form_single_inl_inr (k : Fin n) :
    form (Pi.single (Sum.inl k) (1 : K) : Fin n ⊕ Fin n → K) (Pi.single (Sum.inr k) 1) = 1 := by
  rw [form_single_right]
  simp

theorem isHyperbolicPlane_stdPlane (k : Fin n) : IsHyperbolicPlane (stdPlane K n k) :=
  ⟨_, _, form_single_inl_inr k, rfl⟩

theorem mem_stdPlane_iff (k : Fin n) {v : Fin n ⊕ Fin n → K} :
    v ∈ stdPlane K n k ↔ ∀ t ∉ coords k, v t = 0 := by
  rw [stdPlane, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩ t ht
    have h1 : t ≠ Sum.inl k := fun e => ht (e ▸ inl_mem_coords k)
    have h2 : t ≠ Sum.inr k := fun e => ht (e ▸ inr_mem_coords k)
    simp [h1, h2]
  · intro h
    refine ⟨v (Sum.inl k), v (Sum.inr k), ?_⟩
    funext t
    by_cases h1 : t = Sum.inl k
    · subst h1
      simp
    · by_cases h2 : t = Sum.inr k
      · subst h2
        simp
      · have ht : t ∉ coords k := fun ht => by rcases mem_coords.1 ht with e | e <;> contradiction
        simp [h1, h2, h t ht]

theorem minusSpace_longInv_eq (h2 : (2 : K) ≠ 0) (k : Fin n) :
    minusSpace (longInv K n k) = stdPlane K n k := by
  ext v
  rw [mem_minusSpace_longInv h2, mem_stdPlane_iff]

theorem orthSet_stdPlane (k : Fin n) :
    orthSet (stdPlane K n k : Set (Fin n ⊕ Fin n → K)) = {v | ∀ t ∈ coords k, v t = 0} := by
  ext v
  rw [stdPlane, mem_orthSet_span_pair, form_single_right, form_single_right]
  simp only [par_inl, par_inr, sgn_inl, sgn_inr, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩ t ht
    rcases mem_coords.1 ht with rfl | rfl
    · simpa using h2
    · simpa using h1
  · intro h
    exact ⟨by simp [h _ (inr_mem_coords k)], by simp [h _ (inl_mem_coords k)]⟩

theorem planeGroup_stdPlane (k : Fin n) : planeGroup (stdPlane K n k) = longRootSp2 K n k := by
  rw [planeGroup, orthSet_stdPlane, fixing_supported_eq (parClosed_coords k),
    longRootSp2_eq_suppGroup]

end Standard

section Nondegenerate

theorem linearIndependent_pair_of_form_eq_one {u w : Fin n ⊕ Fin n → K} (h : form u w = 1) :
    LinearIndependent K ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hwu : form w u = -1 := by rw [form_antisymm u w, h]
  have h1 := congrArg (fun x => form x w) hst
  have h2 := congrArg (fun x => form x u) hst
  simp only [form_add_left, form_smul_left, h, hwu, form_self, form_zero_left] at h1 h2
  exact ⟨by linear_combination h1, by linear_combination -h2⟩

theorem finrank_span_pair {u w : Fin n ⊕ Fin n → K} (h : form u w = 1) :
    Module.finrank K (Submodule.span K {u, w}) = 2 := by
  rw [← Matrix.range_cons_cons_empty u w ![],
    finrank_span_eq_card (linearIndependent_pair_of_form_eq_one h), Fintype.card_fin]

theorem isHyperbolicPlane_iff {P : Submodule K (Fin n ⊕ Fin n → K)} :
    IsHyperbolicPlane P ↔
      Module.finrank K P = 2 ∧ ∀ v ∈ P, (∀ u ∈ P, form v u = 0) → v = 0 := by
  constructor
  · rintro ⟨u, w, h, rfl⟩
    refine ⟨finrank_span_pair h, fun v hv hv0 => ?_⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
    have hwu : form w u = -1 := by rw [form_antisymm u w, h]
    have h1 := hv0 u (Submodule.subset_span (by simp))
    have h2 := hv0 w (Submodule.subset_span (by simp))
    simp only [form_add_left, form_smul_left, h, hwu, form_self] at h1 h2
    have ha : a = 0 := by linear_combination h2
    have hb : b = 0 := by linear_combination -h1
    simp [ha, hb]
  · rintro ⟨hdim, hnd⟩
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by rw [hdim]; norm_num)
    have hx0 : (x : Fin n ⊕ Fin n → K) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨w', hw', hw'0⟩ : ∃ w' ∈ P, form (x : Fin n ⊕ Fin n → K) w' ≠ 0 := by
      by_contra hcon
      exact hx0 (hnd _ x.2 fun u hu => by
        by_contra hne
        exact hcon ⟨u, hu, hne⟩)
    set w := (form (x : Fin n ⊕ Fin n → K) w')⁻¹ • w' with hw
    have hwP : w ∈ P := P.smul_mem _ hw'
    have huw : form (x : Fin n ⊕ Fin n → K) w = 1 := by
      rw [hw, form_smul_right, inv_mul_cancel₀ hw'0]
    refine ⟨x, w, huw, ?_⟩
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact x.2
      · exact hwP
    · rw [finrank_span_pair huw, hdim]

end Nondegenerate

section Planes

variable {L : Subgroup (StatedSp n K)} {i : StatedSp n K}

theorem minusSpace_conj_eq (h2 : (2 : K) ≠ 0) (g : StatedSp n K) (k : Fin n) :
    minusSpace (g * longInv K n k * g⁻¹) =
      Submodule.span K {mat n K g *ᵥ (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → K),
        mat n K g *ᵥ (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → K)} := by
  ext v
  rw [mem_minusSpace_conj, mem_span_pair_conj, ← stdPlane, minusSpace_longInv_eq h2]

theorem IsLongRootSp2.isHyperbolicPlane (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) :
    IsHyperbolicPlane (minusSpace i) := by
  obtain ⟨k, g, rfl, rfl⟩ := h
  refine ⟨_, _, ?_, minusSpace_conj_eq h2 g k⟩
  rw [form_mulVec]
  exact form_single_inl_inr k

theorem IsLongRootSp2.fixSpace_eq_orthSet (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) :
    (fixSpace i : Set (Fin n ⊕ Fin n → K)) = orthSet (minusSpace i : Set (Fin n ⊕ Fin n → K)) := by
  ext v
  exact h.mem_fixSpace_iff h2

theorem IsLongRootSp2.eq_planeGroup (h2 : (2 : K) ≠ 0) (h : IsLongRootSp2 L i) :
    L = planeGroup (minusSpace i) := by
  rw [h.eq_longRootGroup h2, longRootGroup, planeGroup, h.fixSpace_eq_orthSet h2]

theorem exists_isLongRootSp2_of_isHyperbolicPlane (h2 : (2 : K) ≠ 0)
    {P : Submodule K (Fin n ⊕ Fin n → K)} (hP : IsHyperbolicPlane P) :
    ∃ i, IsLongRootSp2 (planeGroup P) i ∧ minusSpace i = P := by
  obtain ⟨u, w, huw, rfl⟩ := hP
  rcases n with _ | m
  · exfalso
    rw [form_apply] at huw
    simp at huw
  · obtain ⟨g, hu, hw⟩ := exists_sp_apply_eq u w huw
    refine ⟨g * longInv K (m + 1) 0 * g⁻¹, ⟨0, g, ?_, rfl⟩, ?_⟩
    · rw [← hu, ← hw, planeGroup_span_conj]
      exact congrArg _ (planeGroup_stdPlane 0)
    · rw [minusSpace_conj_eq h2, hu, hw]

theorem exists_isLongRootSp2_iff (h2 : (2 : K) ≠ 0) (L : Subgroup (StatedSp n K)) :
    (∃ i, IsLongRootSp2 L i) ↔ ∃ P, IsHyperbolicPlane P ∧ L = planeGroup P := by
  constructor
  · rintro ⟨i, h⟩
    exact ⟨_, h.isHyperbolicPlane h2, h.eq_planeGroup h2⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨i, hi, -⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hP
    exact ⟨i, hi⟩

end Planes

end CFSG.ClassicalInvolution.Models.SymplecticPairs
