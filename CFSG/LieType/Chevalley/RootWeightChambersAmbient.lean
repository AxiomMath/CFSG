module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.RootWeightFiltrationSpace
public import CFSG.LieType.Chevalley.WeylExchange

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Matrix
open scoped RealInnerProductSpace

namespace RootWeightSpace

variable {τ : Tag}

theorem toPi_sum
    {ι : Type*} (s : Finset ι) (f : ι → RootWeightSpace τ) :
    (∑ k ∈ s, f k).toPi = ∑ k ∈ s, (f k).toPi :=
  map_sum (linearEquivPi τ) f s

theorem sum_apply
    {ι : Type*} (s : Finset ι) (f : ι → RootWeightSpace τ) (j : Fin τ.rank) :
    (∑ k ∈ s, f k) j = ∑ k ∈ s, f k j := by
  rw [toPi_sum, Finset.sum_apply]

theorem inner_single_left
    (i : Fin τ.rank) (x : RootWeightSpace τ) :
    ⟪ofLattice (Pi.single i 1), x⟫ = ∑ j, (τ.symmetrizedCartan i j : ℝ) * x j := by
  rw [inner_eq_sum, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem inner_single_left_eq
    (i : Fin τ.rank) (x : RootWeightSpace τ) :
    ⟪ofLattice (Pi.single i 1), x⟫ =
      (τ.symmetrizer i i : ℝ) * ∑ j, (τ.cartan i j : ℝ) * x j := by
  rw [inner_single_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_apply]
  push_cast
  ring

theorem inner_ofLattice_left
    (v : Fin τ.rank → ℤ) (x : RootWeightSpace τ) :
    ⟪ofLattice v, x⟫ = ∑ j, (v j : ℝ) * ⟪ofLattice (Pi.single j 1), x⟫ := by
  rw [inner_eq_sum]
  simp only [ofLattice_apply, inner_single_left, Finset.mul_sum, mul_assoc]

theorem inner_single_self
    (i : Fin τ.rank) :
    ⟪ofLattice (Pi.single i 1), ofLattice (Pi.single i 1)⟫ = 2 * (τ.symmetrizer i i : ℝ) := by
  rw [inner_single_left_eq, Finset.sum_eq_single i]
  · simp [Tag.cartan_self]
    ring
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ofLattice_injective
    : Function.Injective (ofLattice : (Fin τ.rank → ℤ) → _) :=
  fun u v h => funext fun j => by
    have := congrArg (fun x : RootWeightSpace τ => x j) h
    simpa using this

theorem ofLattice_single_ne_zero
    (i : Fin τ.rank) :
    ofLattice (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
  have := congrArg (fun x : RootWeightSpace τ => x i) h
  simp at this

theorem symmetrizer_real_pos
    (i : Fin τ.rank) : (0 : ℝ) < τ.symmetrizer i i := by
  have h := real_inner_self_pos.2 (ofLattice_single_ne_zero (τ := τ) i)
  rw [inner_single_self] at h
  linarith

theorem inner_ofLattice_nonneg_of_single
    {v : Fin τ.rank → ℤ} (hv : ∀ j, 0 ≤ v j)
    {x : RootWeightSpace τ} (hx : ∀ j, 0 ≤ ⟪ofLattice (Pi.single j 1), x⟫) :
    0 ≤ ⟪ofLattice v, x⟫ := by
  rw [inner_ofLattice_left]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (by exact_mod_cast hv j) (hx j)

theorem inner_ofLattice_nonpos_of_single
    {v : Fin τ.rank → ℤ} (hv : ∀ j, v j ≤ 0)
    {x : RootWeightSpace τ} (hx : ∀ j, 0 ≤ ⟪ofLattice (Pi.single j 1), x⟫) :
    ⟪ofLattice v, x⟫ ≤ 0 := by
  rw [inner_ofLattice_left]
  exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hv j) (hx j)

theorem inner_ofLattice_pos_of_single
    {v : Fin τ.rank → ℤ} (hv : ∀ j, 0 ≤ v j) (hne : v ≠ 0)
    {x : RootWeightSpace τ} (hx : ∀ j, 0 < ⟪ofLattice (Pi.single j 1), x⟫) :
    0 < ⟪ofLattice v, x⟫ := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  rw [inner_ofLattice_left]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (by exact_mod_cast hv j) (hx j).le)
    ⟨k, Finset.mem_univ k, mul_pos (by exact_mod_cast lt_of_le_of_ne (hv k) (Ne.symm hk)) (hx k)⟩

theorem inner_single_self_pos
    (i : Fin τ.rank) :
    0 < ⟪ofLattice (Pi.single i 1), ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)⟫ :=
  real_inner_self_pos.2 (ofLattice_single_ne_zero i)

theorem sum_smul_single_apply
    (c : Fin τ.rank → ℝ) (j : Fin τ.rank) :
    (∑ i, c i • ofLattice (Pi.single i 1 : Fin τ.rank → ℤ)) j = c j := by
  rw [sum_apply, Finset.sum_eq_single j]
  · change c j * (((Pi.single j 1 : Fin τ.rank → ℤ) j : ℤ) : ℝ) = c j
    simp
  · intro i _ hij
    change c i * (((Pi.single i 1 : Fin τ.rank → ℤ) j : ℤ) : ℝ) = 0
    simp [Ne.symm hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem linearIndependent_single_top :
    LinearIndependent ℝ fun i : Fin τ.rank =>
      (⟨ofLattice (Pi.single i 1), Submodule.mem_top⟩ : (⊤ : Submodule ℝ (RootWeightSpace τ))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hc' : ∑ i, c i • ofLattice (Pi.single i 1 : Fin τ.rank → ℤ) = 0 := by
    have := congrArg Subtype.val hc
    simpa using this
  have := congrArg (fun x : RootWeightSpace τ => x j) hc'
  simp only [sum_smul_single_apply] at this
  simpa using this

theorem span_single_top :
    Submodule.span ℝ (Set.range fun i : Fin τ.rank =>
      (⟨ofLattice (Pi.single i 1), Submodule.mem_top⟩ : (⊤ : Submodule ℝ (RootWeightSpace τ)))) =
      ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = ∑ i, (x : RootWeightSpace τ) i •
      (⟨ofLattice (Pi.single i 1), Submodule.mem_top⟩ : (⊤ : Submodule ℝ (RootWeightSpace τ))) := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    ext j
    rw [sum_smul_single_apply]
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable (τ) in
@[expose] def simpleBasis
    : Module.Basis (Fin τ.rank) ℝ (RootWeightSpace τ) :=
  (Pi.basisFun ℝ (Fin τ.rank)).map (linearEquivPi τ).symm

theorem simpleBasis_apply
    (i : Fin τ.rank) : simpleBasis τ i = ofLattice (Pi.single i 1) := by
  ext j
  simp [simpleBasis, linearEquivPi, Pi.single_apply]

theorem eq_of_forall_inner_single_eq
    {x y : RootWeightSpace τ}
    (h : ∀ i, ⟪ofLattice (Pi.single i 1), x⟫ = ⟪ofLattice (Pi.single i 1), y⟫) : x = y :=
  InnerProductSpace.ext_inner_left_basis (simpleBasis τ) fun i => by
    rw [simpleBasis_apply]
    exact h i

variable (τ) in
@[expose] def heightVec
    : RootWeightSpace τ :=
  ofPi ((realSymmetrizedCartan τ)⁻¹ *ᵥ 1)

theorem inner_single_heightVec
    (j : Fin τ.rank) :
    ⟪ofLattice (Pi.single j 1), heightVec τ⟫ = 1 := by
  have hdet : IsUnit (realSymmetrizedCartan τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (posDef_realSymmetrizedCartan τ).isUnit
  have h : realSymmetrizedCartan τ *ᵥ (heightVec τ).toPi = 1 := by
    rw [heightVec, toPi_ofPi, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hj := congrFun h j
  rw [inner_single_left]
  simpa [mulVec, dotProduct, realSymmetrizedCartan] using hj

theorem eq_heightVec_iff
    {x : RootWeightSpace τ} :
    (∀ j, ⟪ofLattice (Pi.single j 1), x⟫ = 1) ↔ x = heightVec τ := by
  refine ⟨fun h => eq_of_forall_inner_single_eq fun j => by rw [h, inner_single_heightVec],
    ?_⟩
  rintro rfl
  exact inner_single_heightVec

theorem inner_single_heightVec_pos
    (j : Fin τ.rank) :
    0 < ⟪ofLattice (Pi.single j 1), heightVec τ⟫ := by
  rw [inner_single_heightVec]
  exact one_pos

theorem inner_ofLattice_heightVec
    (v : Fin τ.rank → ℤ) :
    ⟪ofLattice v, heightVec τ⟫ = (height v : ℝ) := by
  rw [inner_ofLattice_left]
  simp only [inner_single_heightVec, mul_one, height]
  push_cast
  rfl

end RootWeightSpace

open RootWeightSpace

variable {τ : Tag}

theorem weylIsometry_simple
    (i : Fin τ.rank) (x : RootWeightSpace τ) :
    weylIsometry τ (simple τ i) x =
      x - (∑ j, (τ.cartan i j : ℝ) * x j) • ofLattice (Pi.single i 1) := by
  apply (toRootSpace τ).injective
  rw [toRootSpace_weylIsometry, weylAct_simple, map_sub, map_smul, toRootSpace_ofLattice]
  simp only [toRootSpace_apply]

theorem weylIsometry_simple_eq_reflection
    (i : Fin τ.rank) (x : RootWeightSpace τ) :
    weylIsometry τ (simple τ i) x = x - (2 * ⟪ofLattice (Pi.single i 1), x⟫ /
      ⟪ofLattice (Pi.single i 1), ofLattice (Pi.single i 1)⟫) • ofLattice (Pi.single i 1) := by
  rw [weylIsometry_simple, inner_single_self, inner_single_left_eq]
  have hd := (symmetrizer_real_pos (τ := τ) i).ne'
  congr 2
  field_simp

theorem weylIsometry_injective
    : Function.Injective (weylIsometry τ) := by
  intro w w' h
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin τ.rank → ℤ) fun v => ?_
  have hv := congrArg (fun f => f (ofLattice v)) h
  simp only [weylIsometry_ofLattice] at hv
  exact ofLattice_injective hv

theorem exists_length_mul_simple_lt
    {w : WeylGroup τ} (h1 : w ≠ 1) :
    ∃ i, (coxeterSystem τ).length (w * simple τ i) < (coxeterSystem τ).length w ∧
      height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 := by
  obtain ⟨i, hi⟩ := (weyl_exchange_condition τ).2.2.2 w h1
  have hl := ((weyl_exchange_condition τ).2.1 w i).1.2 hi
  have hpos : 0 < (coxeterSystem τ).length w := by
    rw [Nat.pos_iff_ne_zero, Ne, CoxeterSystem.length_eq_zero_iff]
    exact h1
  exact ⟨i, by omega, hi.2⟩

theorem inner_weylIsometry_single_nonpos
    {w : WeylGroup τ} {i : Fin τ.rank}
    (hneg : height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0) {x : RootWeightSpace τ}
    (hx : ∀ j, 0 ≤ ⟪ofLattice (Pi.single j 1), x⟫) :
    ⟪weylIsometry τ w (ofLattice (Pi.single i 1)), x⟫ ≤ 0 := by
  rw [weylIsometry_ofLattice]
  exact inner_ofLattice_nonpos_of_single
    ((IsRoot.height_neg_iff (IsRoot.smul (isRoot_single τ i) w)).1 hneg) hx

section Abstract

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℝ M]

theorem coe_orthogonalProjectionOnto_apply_map (F : Submodule ℝ M) [F.HasOrthogonalProjection]
    (f : M ≃ₗᵢ[ℝ] M) (hf : ∀ x ∈ F, f x ∈ F) (hf' : ∀ x ∈ F, f.symm x ∈ F) (x : M) :
    (F.orthogonalProjectionOnto (f x) : M) = f (F.orthogonalProjectionOnto x) := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hf _ (Submodule.coe_mem _))
    fun y hy => ?_
  have h := Submodule.starProjection_inner_eq_zero x (f.symm y) (hf' y hy)
  rw [← f.inner_map_map, map_sub, LinearIsometryEquiv.apply_symm_apply] at h
  rwa [Submodule.coe_orthogonalProjectionOnto_apply]

variable {G : Type*} [Group G] (ρ : G →* (M ≃ₗᵢ[ℝ] M)) {ι : Type*}

theorem exists_forall_inner_nonneg (S : Subgroup G) [Finite S] (F : Submodule ℝ M)
    (hSF : ∀ w ∈ S, ∀ y ∈ F, ρ w y ∈ F) (a : ι → M) (t : ι → G) (ht : ∀ i, t i ∈ S)
    (hrefl : ∀ i, ∀ y ∈ F, ρ (t i) y = y - (2 * ⟪a i, y⟫ / ⟪a i, a i⟫) • a i)
    (ha : ∀ i, 0 < ⟪a i, a i⟫) {h : M} (hh : ∀ i, 0 < ⟪a i, h⟫) {x : M} (hx : x ∈ F) :
    ∃ u ∈ S, ∀ i, 0 ≤ ⟪a i, ρ u x⟫ := by
  obtain ⟨u, hu⟩ := Finite.exists_max fun u : S => ⟪ρ u x, h⟫
  refine ⟨u, u.2, fun i => ?_⟩
  by_contra hneg
  rw [not_le] at hneg
  have hmem : t i * u ∈ S := mul_mem (ht i) u.2
  have h1 := hu ⟨t i * u, hmem⟩
  simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply] at h1
  rw [hrefl i _ (hSF u u.2 x hx), inner_sub_left, real_inner_smul_left] at h1
  have h2 : 2 * ⟪a i, ρ u x⟫ / ⟪a i, a i⟫ < 0 :=
    div_neg_of_neg_of_pos (by linarith) (ha i)
  have h3 := mul_neg_of_neg_of_pos h2 (hh i)
  linarith

theorem fix_of_mem_closure {a : ι → M} {t : ι → G} {l : M}
    (hfix : ∀ i, ⟪a i, l⟫ = 0 → ρ (t i) l = l) {w : G}
    (hw : w ∈ Subgroup.closure (t '' {i | ⟪a i, l⟫ = 0})) : ρ w l = l := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact hfix i hi
  | one => simp
  | mul x y _ _ hx hy =>
    simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hy, hx]
  | inv x _ hx =>
    conv_lhs => rw [← hx]
    rw [map_inv, LinearIsometryEquiv.coe_inv, LinearIsometryEquiv.symm_apply_apply]

theorem mem_closure_of_fix (S : Subgroup G) {a : ι → M} {t : ι → G} (ht : ∀ i, t i ∈ S)
    {l : M} (hl : ∀ i, 0 ≤ ⟪a i, l⟫) (hfix : ∀ i, ⟪a i, l⟫ = 0 → ρ (t i) l = l) (len : G → ℕ)
    (hexch : ∀ w ∈ S, w ≠ 1 → ∃ i, len (w * t i) < len w ∧ ⟪ρ w (a i), l⟫ ≤ 0) :
    ∀ w ∈ S, ρ w l = l → w ∈ Subgroup.closure (t '' {i | ⟪a i, l⟫ = 0}) := by
  intro w
  induction hn : len w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro hw hwl
    by_cases h1 : w = 1
    · rw [h1]
      exact one_mem _
    obtain ⟨i, hlen, hneg⟩ := hexch w hw h1
    have hi : ⟪a i, l⟫ = 0 := by
      have e : ⟪ρ w (a i), l⟫ = ⟪a i, l⟫ := by
        conv_lhs => rw [← hwl]
        exact (ρ w).inner_map_map _ _
      linarith [hl i]
    have hmem : t i ∈ Subgroup.closure (t '' {i | ⟪a i, l⟫ = 0}) :=
      Subgroup.subset_closure ⟨i, hi, rfl⟩
    have hwt : ρ (w * t i) l = l := by
      simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hfix i hi, hwl]
    have h2 := ih _ (hn ▸ hlen) (w * t i) rfl (mul_mem hw (ht i)) hwt
    have e : w = w * t i * (t i)⁻¹ := by group
    rw [e]
    exact mul_mem h2 (inv_mem hmem)

theorem eq_zero_of_forall_inner_eq_zero {F : Submodule ℝ M} {a : ι → F}
    (hspan : Submodule.span ℝ (Set.range a) = ⊤) {l : F} (hl : ∀ i, ⟪a i, l⟫ = 0) : l = 0 := by
  have key : ∀ x ∈ Submodule.span ℝ (Set.range a), ⟪x, l⟫ = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hl i
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  exact inner_self_eq_zero.1 (key l (by rw [hspan]; exact Submodule.mem_top))

end Abstract

end CFSG.LieType.Chevalley
