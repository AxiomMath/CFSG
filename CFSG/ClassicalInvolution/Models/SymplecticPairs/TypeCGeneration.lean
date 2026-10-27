module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n m : ℕ}

section Normal

theorem commutator_mul_central {G : Type*} [Group G] {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ ∧ ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.1 hz
  constructor
  · rw [commutatorElement_def, commutatorElement_def]
    calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [← h b]; group
  · rw [commutatorElement_def, commutatorElement_def]
    calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [← h a⁻¹]; group

theorem scalars_le_center : (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) ≤
    Subgroup.center (StatedSp n K) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  simp only [Subgroup.coe_mul, ← hc]
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem eq_top_of_normal_of_not_le_center [Finite K] (hn : 1 ≤ n) (h4 : 4 ≤ Nat.card K)
    {N : Subgroup (StatedSp n K)} (hN : N.Normal) (hnc : ¬ N ≤ Subgroup.center (StatedSp n K)) :
    N = ⊤ := by
  have hsimple := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K n hn
    (Or.inl (Or.inr h4))
  have hperf : Group.IsPerfect (StatedSp n K) := by
    refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n K (Or.inl ?_)
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  set Z := (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) with hZdef
  have hZ : Z ≤ Subgroup.center (StatedSp n K) := scalars_le_center
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal := hN.map _ (QuotientGroup.mk'_surjective Z)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
  · exfalso
    apply hnc
    intro x hx
    have hx' : QuotientGroup.mk' Z x ∈ N.map (QuotientGroup.mk' Z) := ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact hZ ((QuotientGroup.eq_one_iff x).1 (by simpa using hx'))
  · have hsup : ∀ g : StatedSp n K, ∃ a ∈ N, ∃ z ∈ Z, g = a * z := by
      intro g
      have : QuotientGroup.mk' Z g ∈ N.map (QuotientGroup.mk' Z) := by rw [h]; trivial
      obtain ⟨a, ha, hag⟩ := this
      refine ⟨a, ha, a⁻¹ * g, QuotientGroup.eq.1 hag, by group⟩
    have hcomm : ∀ a b : StatedSp n K, ⁅a, b⁆ ∈ N := by
      intro a b
      obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hsup a
      obtain ⟨b₁, hb₁, z₂, hz₂, rfl⟩ := hsup b
      rw [(commutator_mul_central (hZ hz₁)).1, (commutator_mul_central (hZ hz₂)).2]
      have : ⁅a₁, b₁⁆ = a₁ * (b₁ * a₁⁻¹ * b₁⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem ha₁ (hN.conj_mem _ (inv_mem ha₁) _)
    have hcom : commutator (StatedSp n K) = ⊤ := Group.isPerfect_def.1 hperf
    have hle : ⁅(⊤ : Subgroup (StatedSp n K)), ⊤⁆ ≤ N :=
      Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
    rw [← commutator_def, hcom] at hle
    exact eq_top_iff.2 hle

end Normal

section Orth

@[expose] def orthPlanes (K : Type) [Field K] (n : ℕ) (k : Fin n) :
    Set (Submodule K (Fin n ⊕ Fin n → K)) :=
  {P | IsHyperbolicPlane P ∧ ∀ u ∈ P, ∀ v ∈ stdPlane K n k, form u v = 0}

theorem stdPlane_le_orthSet {P : Submodule K (Fin n ⊕ Fin n → K)} {k : Fin n}
    (hP : P ∈ orthPlanes K n k) :
    (stdPlane K n k : Set (Fin n ⊕ Fin n → K)) ⊆ orthSet (P : Set _) := by
  intro v hv u hu
  rw [form_antisymm, hP.2 u hu v hv, neg_zero]

theorem planeGroup_le_suppGroup_compl (h2 : (2 : K) ≠ 0) {P : Submodule K (Fin n ⊕ Fin n → K)}
    {k : Fin n} (hP : P ∈ orthPlanes K n k) : planeGroup P ≤ suppGroup (coords k)ᶜ := by
  rw [← complGroup_longInv h2, complGroup, minusSpace_longInv_eq h2]
  exact fixing_anti (stdPlane_le_orthSet hP)

theorem fix_stdPlane_of_mem_compl (h2 : (2 : K) ≠ 0) {k : Fin n} {c : StatedSp n K}
    (hc : c ∈ suppGroup (coords k)ᶜ) {v : Fin n ⊕ Fin n → K} (hv : v ∈ stdPlane K n k) :
    mat n K c *ᵥ v = v := by
  rw [← complGroup_longInv h2, complGroup, minusSpace_longInv_eq h2] at hc
  exact hc v hv

theorem map_mem_orthPlanes (h2 : (2 : K) ≠ 0) {P : Submodule K (Fin n ⊕ Fin n → K)} {k : Fin n}
    (hP : P ∈ orthPlanes K n k) {c : StatedSp n K} (hc : c ∈ suppGroup (coords k)ᶜ) :
    P.map (Matrix.mulVecLin (mat n K c)) ∈ orthPlanes K n k := by
  obtain ⟨⟨u, w, huw, rfl⟩, horth⟩ := hP
  refine ⟨⟨mat n K c *ᵥ u, mat n K c *ᵥ w, ?_, ?_⟩, ?_⟩
  · rw [form_mulVec]; exact huw
  · rw [Submodule.map_span]
    simp [Set.image_insert_eq]
  · intro u' hu' v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hu'
    rw [Matrix.mulVecLin_apply, ← fix_stdPlane_of_mem_compl h2 hc hv, form_mulVec]
    exact horth x hx v hv

theorem stdPlane_mem_orthPlanes {k l : Fin n} (hlk : l ≠ k) :
    stdPlane K n l ∈ orthPlanes K n k := by
  refine ⟨isHyperbolicPlane_stdPlane l, fun u hu v hv => ?_⟩
  refine form_eq_zero_of_supp (parClosed_coords k) (fun a ha => ?_) (fun a ha => ?_)
  · refine (mem_stdPlane_iff l).1 hu a ?_
    intro hal
    rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 hal with h | h <;>
      first | exact hlk (Sum.inl_injective h).symm | exact hlk (Sum.inr_injective h).symm |
        cases h
  · exact (mem_stdPlane_iff k).1 hv a ha

variable (K n) in
@[expose] noncomputable def orthPlaneSubgroup (k : Fin n) : Subgroup (StatedSp n K) :=
  ⨆ P : orthPlanes K n k, planeGroup (P : Submodule K (Fin n ⊕ Fin n → K))

theorem orthPlaneSubgroup_le (h2 : (2 : K) ≠ 0) (k : Fin n) :
    orthPlaneSubgroup K n k ≤ suppGroup (coords k)ᶜ :=
  iSup_le fun P => planeGroup_le_suppGroup_compl h2 P.2

theorem conj_orthPlaneSubgroup_le (h2 : (2 : K) ≠ 0) {k : Fin n} {c : StatedSp n K}
    (hc : c ∈ suppGroup (coords k)ᶜ) :
    (orthPlaneSubgroup K n k).map (MulAut.conj c).toMonoidHom ≤ orthPlaneSubgroup K n k := by
  rw [orthPlaneSubgroup, Subgroup.map_iSup]
  refine iSup_le fun P => ?_
  rw [← planeGroup_map_conj]
  exact le_iSup (fun Q : orthPlanes K n k => planeGroup (Q : Submodule K (Fin n ⊕ Fin n → K)))
    ⟨_, map_mem_orthPlanes h2 P.2 hc⟩

theorem noncomm_longBlock_transv (l : Fin n) :
    longBlock K n l (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])) *
        longBlock K n l (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])) ≠
      longBlock K n l (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])) *
        longBlock K n l (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])) := by
  intro h
  rw [← map_mul, ← map_mul] at h
  have h' := longBlock_injective l h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h'
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
  simp [mkSL, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem longBlock_mem_orthPlaneSubgroup {k l : Fin n} (hl : l ≠ k) (A : SL(2, K)) :
    longBlock K n l A ∈ orthPlaneSubgroup K n k := by
  have : planeGroup (stdPlane K n l) ≤ orthPlaneSubgroup K n k :=
    le_iSup (fun Q : orthPlanes K n k => planeGroup (Q : Submodule K (Fin n ⊕ Fin n → K)))
      ⟨_, stdPlane_mem_orthPlanes hl⟩
  rw [planeGroup_stdPlane] at this
  exact this ⟨A, rfl⟩

theorem longBlock_mem_compl (h2 : (2 : K) ≠ 0) {k l : Fin n} (hl : l ≠ k) (A : SL(2, K)) :
    longBlock K n l A ∈ suppGroup (coords k)ᶜ :=
  orthPlaneSubgroup_le h2 k (longBlock_mem_orthPlaneSubgroup hl A)

theorem exists_ne_of_one_le {m : ℕ} (hm : 1 ≤ m) (k : Fin (m + 1)) : ∃ l : Fin (m + 1), l ≠ k := by
  by_cases hk : k.val = 0
  · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
  · exact ⟨⟨0, by omega⟩, fun h => hk (by rw [← h])⟩

theorem orthPlaneSubgroup_eq [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) (hm : 1 ≤ m)
    (k : Fin (m + 1)) : orthPlaneSubgroup K (m + 1) k = suppGroup (coords k)ᶜ := by
  refine le_antisymm (orthPlaneSubgroup_le h2 k) ?_
  obtain ⟨e⟩ := IsLongRootSp2.nonempty_mulEquiv_complGroup h2
    (isLongRootSp2_standard (K := K) (n := m + 1) k)
  have hC : complGroup (longInv K (m + 1) k) = suppGroup (coords k)ᶜ := complGroup_longInv h2 k
  have hnorm : ((orthPlaneSubgroup K (m + 1) k).subgroupOf
      (complGroup (longInv K (m + 1) k))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (g : StatedSp (m + 1) K) ∈ suppGroup (coords k)ᶜ := by rw [← hC]; exact g.2
    exact conj_orthPlaneSubgroup_le h2 hg ⟨_, hx, rfl⟩
  have hS'norm : (((orthPlaneSubgroup K (m + 1) k).subgroupOf
      (complGroup (longInv K (m + 1) k))).comap e.toMonoidHom).Normal := hnorm.comap _
  obtain ⟨l, hl⟩ := exists_ne_of_one_le hm k
  have hlC : ∀ A : SL(2, K), longBlock K (m + 1) l A ∈ complGroup (longInv K (m + 1) k) :=
    fun A => by
    rw [hC]; exact longBlock_mem_compl h2 hl A
  have hnc : ¬ ((orthPlaneSubgroup K (m + 1) k).subgroupOf
      (complGroup (longInv K (m + 1) k))).comap e.toMonoidHom ≤ Subgroup.center (StatedSp m K) := by
    intro hle
    have hx' : e.symm ⟨longBlock K (m + 1) l (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])),
        hlC _⟩ ∈ ((orthPlaneSubgroup K (m + 1) k).subgroupOf
          (complGroup (longInv K (m + 1) k))).comap e.toMonoidHom := by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact longBlock_mem_orthPlaneSubgroup hl _
    have hcen := Subgroup.mem_center_iff.1 (hle hx')
      (e.symm ⟨longBlock K (m + 1) l (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])), hlC _⟩)
    have := congrArg (fun z => (e z : StatedSp (m + 1) K)) hcen
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at this
    exact noncomm_longBlock_transv (K := K) (n := m + 1) l this.symm
  have htop := eq_top_of_normal_of_not_le_center hm h4 hS'norm hnc
  intro g hg
  rw [← hC] at hg
  have hg' : e.symm ⟨g, hg⟩ ∈ ((orthPlaneSubgroup K (m + 1) k).subgroupOf
      (complGroup (longInv K (m + 1) k))).comap e.toMonoidHom := by rw [htop]; trivial
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hg'
  simpa using hg'

theorem exists_sp_apply_eq_two_at {k l : Fin n} (hkl : k ≠ l)
    (u₁ w₁ u₂ w₂ : Fin n ⊕ Fin n → K) (h₁ : form u₁ w₁ = 1) (h₂ : form u₂ w₂ = 1)
    (o₁ : form u₁ u₂ = 0) (o₂ : form u₁ w₂ = 0) (o₃ : form w₁ u₂ = 0) (o₄ : form w₁ w₂ = 0) :
    ∃ g : StatedSp n K, mat n K g *ᵥ Pi.single (Sum.inl k) 1 = u₁ ∧
      mat n K g *ᵥ Pi.single (Sum.inr k) 1 = w₁ ∧ mat n K g *ᵥ Pi.single (Sum.inl l) 1 = u₂ ∧
      mat n K g *ᵥ Pi.single (Sum.inr l) 1 = w₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by have := k.2; have := l.2; omega⟩
  obtain ⟨g₁, a1, a2, a3, a4⟩ := exists_sp_apply_eq_two u₁ w₁ u₂ w₂ h₁ h₂ o₁ o₂ o₃ o₄
  have hkl' : l ≠ k := hkl.symm
  obtain ⟨g₂, b1, b2, b3, b4⟩ := exists_sp_apply_eq_two
    (Pi.single (Sum.inl k) (1 : K) : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K)
    (Pi.single (Sum.inr k) 1) (Pi.single (Sum.inl l) 1) (Pi.single (Sum.inr l) 1)
    (form_single_inl_inr k)
    (form_single_inl_inr l) (by rw [form_single_right]; simp)
    (by rw [form_single_right]; simp [hkl'])
    (by rw [form_single_right]; simp [hkl'])
    (by rw [form_single_right]; simp)
  refine ⟨g₁ * g₂⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b1, a1]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b2, a2]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b3, a3]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 b4, a4]

theorem exists_compl_map_eq (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) {k : Fin n}
    {P P' : Submodule K (Fin n ⊕ Fin n → K)} (hP : P ∈ orthPlanes K n k)
    (hP' : P' ∈ orthPlanes K n k) :
    ∃ c ∈ suppGroup (coords k)ᶜ, P.map (Matrix.mulVecLin (mat n K c)) = P' := by
  obtain ⟨⟨u, w, huw, rfl⟩, horth⟩ := hP
  obtain ⟨⟨u', w', huw', rfl⟩, horth'⟩ := hP'
  obtain ⟨l, hl⟩ : ∃ l : Fin n, l ≠ k := by
    by_cases hk : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
    · exact ⟨⟨0, by omega⟩, fun h => hk (by rw [← h])⟩
  have hek : ∀ x ∈ Submodule.span K {u, w}, form x (Pi.single (Sum.inl k) (1 : K)) = 0 ∧
      form x (Pi.single (Sum.inr k) (1 : K)) = 0 := fun x hx =>
    ⟨horth x hx _ (Submodule.subset_span (by simp)),
      horth x hx _ (Submodule.subset_span (by simp))⟩
  have hek' : ∀ x ∈ Submodule.span K {u', w'}, form x (Pi.single (Sum.inl k) (1 : K)) = 0 ∧
      form x (Pi.single (Sum.inr k) (1 : K)) = 0 := fun x hx =>
    ⟨horth' x hx _ (Submodule.subset_span (by simp)),
      horth' x hx _ (Submodule.subset_span (by simp))⟩
  have hu := hek u (Submodule.subset_span (by simp))
  have hw := hek w (Submodule.subset_span (by simp))
  have hu' := hek' u' (Submodule.subset_span (by simp))
  have hw' := hek' w' (Submodule.subset_span (by simp))
  have hflip : ∀ x : Fin n ⊕ Fin n → K, ∀ y, form x y = 0 → form y x = 0 := fun x y h => by
    rw [form_antisymm, h, neg_zero]
  obtain ⟨ga, a1, a2, a3, a4⟩ := exists_sp_apply_eq_two_at hl.symm (Pi.single (Sum.inl k) 1)
    (Pi.single (Sum.inr k) 1) u w (form_single_inl_inr k) huw (hflip _ _ hu.1) (hflip _ _ hw.1)
    (hflip _ _ hu.2) (hflip _ _ hw.2)
  obtain ⟨gb, b1, b2, b3, b4⟩ := exists_sp_apply_eq_two_at hl.symm (Pi.single (Sum.inl k) 1)
    (Pi.single (Sum.inr k) 1) u' w' (form_single_inl_inr k) huw' (hflip _ _ hu'.1)
    (hflip _ _ hw'.1) (hflip _ _ hu'.2) (hflip _ _ hw'.2)
  refine ⟨gb * ga⁻¹, ?_, ?_⟩
  · rw [← complGroup_longInv h2, complGroup, minusSpace_longInv_eq h2]
    intro v hv
    obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.1 hv
    have e1 : mat n K (gb * ga⁻¹) *ᵥ Pi.single (Sum.inl k) 1 = Pi.single (Sum.inl k) 1 := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff ga _ _).1 a1, b1]
    have e2 : mat n K (gb * ga⁻¹) *ᵥ Pi.single (Sum.inr k) 1 = Pi.single (Sum.inr k) 1 := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff ga _ _).1 a2, b2]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, e2]
  · rw [Submodule.map_span]
    have e3 : mat n K (gb * ga⁻¹) *ᵥ u = u' := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff ga _ _).1 a3, b3]
    have e4 : mat n K (gb * ga⁻¹) *ᵥ w = w' := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff ga _ _).1 a4, b4]
    simp only [Set.image_insert_eq, Set.image_singleton, Matrix.mulVecLin_apply, e3, e4]

theorem exists_conj_planeGroup_of_orth (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) {k : Fin n}
    {P P' : Submodule K (Fin n ⊕ Fin n → K)} (hP : P ∈ orthPlanes K n k)
    (hP' : P' ∈ orthPlanes K n k) :
    ∃ c ∈ suppGroup (coords k)ᶜ,
      planeGroup P' = (planeGroup P).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c, hc, h⟩ := exists_compl_map_eq h2 hn hP hP'
  exact ⟨c, hc, by rw [← h, planeGroup_map_conj]⟩

end Orth

end CFSG.ClassicalInvolution.Models.SymplecticPairs
