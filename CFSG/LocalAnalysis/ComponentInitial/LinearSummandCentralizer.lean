module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

variable (k E : Type*) [Field k] [Field E] [Algebra k E] (W : Type*) [AddCommGroup W]
  [Module k W] (m : ℕ)

@[expose] noncomputable def summandSL :
    SpecialLinearGroup (Fin m) E →* LinearMap.GeneralLinearGroup k ((Fin m → E) × W) :=
  MonoidHom.toHomUnits
    { toFun := fun g =>
        ((mulVecLin (g : Matrix (Fin m) (Fin m) E)).restrictScalars k).prodMap LinearMap.id
      map_one' := by
        refine LinearMap.ext fun x => ?_
        simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp [mulVec_mulVec] }

@[simp] theorem summandSL_apply (g : SpecialLinearGroup (Fin m) E) (v : Fin m → E) (w : W) :
    (summandSL k E W m g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, w) =
      ((g : Matrix (Fin m) (Fin m) E) *ᵥ v, w) :=
  rfl

section

variable {k E W m}

theorem summandSL_apply_fst (g : SpecialLinearGroup (Fin m) E) (x : (Fin m → E) × W) :
    ((summandSL k E W m g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x).1 =
      (g : Matrix (Fin m) (Fin m) E) *ᵥ x.1 :=
  rfl

theorem summandSL_apply_snd (g : SpecialLinearGroup (Fin m) E) (x : (Fin m → E) × W) :
    ((summandSL k E W m g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x).2 = x.2 :=
  rfl

theorem transvection_mulVec_eq_add_single {ι F : Type*} [DecidableEq ι] [Fintype ι] [CommRing F]
    {i j : ι} (hij : i ≠ j) (t : F) (v : ι → F) :
    ((SpecialLinearGroup.transvection hij t : SpecialLinearGroup ι F) : Matrix ι ι F) *ᵥ v =
      v + Pi.single i (t * v j) := by
  rw [SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec, single_mulVec]
  rfl

theorem eq_zero_of_forall_transvection_mulVec_eq (hm : 2 ≤ m) {v : Fin m → E}
    (hv : ∀ (i j : Fin m) (hij : i ≠ j),
      ((SpecialLinearGroup.transvection hij (1 : E) : SpecialLinearGroup (Fin m) E) :
        Matrix (Fin m) (Fin m) E) *ᵥ v = v) :
    v = 0 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  funext j
  obtain ⟨i, hij⟩ := exists_ne j
  have h := hv i j hij
  rw [transvection_mulVec_eq_add_single, add_eq_left] at h
  simpa using congrFun h i

theorem exists_smul_prod_of_commute_summandSL (hm : 2 ≤ m)
    {L : (Fin m → E) × W →ₗ[k] (Fin m → E) × W}
    (hL : ∀ (g : SpecialLinearGroup (Fin m) E) (x : (Fin m → E) × W),
      (summandSL k E W m g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (L x) =
        L ((summandSL k E W m g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x)) :
    ∃ (c : E) (D : W →ₗ[k] W), ∀ (v : Fin m → E) (w : W), L (v, w) = (c • v, D w) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have h0 : ∀ w, (L (0, w)).1 = 0 := by
    intro w
    refine eq_zero_of_forall_transvection_mulVec_eq hm fun i j hij => ?_
    have h := congrArg Prod.fst (hL (SpecialLinearGroup.transvection hij 1) (0, w))
    rwa [summandSL_apply_fst, summandSL_apply, mulVec_zero] at h
  have h1 : ∀ v, (L (v, 0)).2 = 0 := by
    have : (LinearMap.snd k (Fin m → E) W) ∘ₗ L ∘ₗ (LinearMap.inl k (Fin m → E) W) = 0 := by
      refine LinearMap.pi_ext fun i x => ?_
      obtain ⟨j, hji⟩ := exists_ne i
      have h := congrArg Prod.snd
        (hL (SpecialLinearGroup.transvection hji.symm 1) (Pi.single j x, 0))
      have hsum : ((Pi.single j x + Pi.single i x, 0) : (Fin m → E) × W) =
          (Pi.single j x, 0) + (Pi.single i x, 0) := by simp
      rw [summandSL_apply_snd, summandSL_apply, transvection_mulVec_eq_add_single,
        Pi.single_eq_same, one_mul, hsum, map_add, Prod.snd_add, left_eq_add] at h
      simpa using h
    exact fun v => LinearMap.congr_fun this v
  set g₁ := (LinearMap.fst k (Fin m → E) W) ∘ₗ L ∘ₗ (LinearMap.inl k (Fin m → E) W) with hg₁
  have hcomm : ∀ (i j : Fin m), i ≠ j → ∀ (t : E) (v : Fin m → E),
      g₁ (Pi.single i (t * v j)) i = t * g₁ v j := by
    intro i j hij t v
    have h := congrArg Prod.fst (hL (SpecialLinearGroup.transvection hij t) (v, 0))
    have hsum : ((v + Pi.single i (t * v j), 0) : (Fin m → E) × W) =
        (v, 0) + (Pi.single i (t * v j), 0) := by simp
    rw [summandSL_apply_fst, summandSL_apply, transvection_mulVec_eq_add_single,
      transvection_mulVec_eq_add_single, hsum, map_add, Prod.fst_add] at h
    have h' : g₁ (Pi.single i (t * v j)) = Pi.single i (t * g₁ v j) := by
      simpa [hg₁] using h.symm
    simp [h']
  let i₀ : Fin m := ⟨0, by omega⟩
  set c := g₁ (Pi.single i₀ 1) i₀
  have ha : ∀ (i : Fin m) (x : E), g₁ (Pi.single i x) i = x * c := by
    have hline : ∀ i j, i ≠ j → ∀ x : E, g₁ (Pi.single i x) i = x * g₁ (Pi.single j 1) j := by
      intro i j hij x
      simpa using hcomm i j hij x (Pi.single j 1)
    intro i x
    by_cases hi : i = i₀
    · obtain ⟨j, hj⟩ := exists_ne i
      rw [hline i j hj.symm, hline j i hj, one_mul, hi]
    · exact hline i i₀ hi x
  have hv : ∀ (v : Fin m → E) (j : Fin m), g₁ v j = c * v j := by
    intro v j
    obtain ⟨i, hij⟩ := exists_ne j
    have h := hcomm i j hij 1 v
    rw [one_mul, one_mul, ha, mul_comm] at h
    exact h.symm
  refine ⟨c, (LinearMap.snd k (Fin m → E) W) ∘ₗ L ∘ₗ (LinearMap.inr k (Fin m → E) W),
    fun v w => ?_⟩
  have hvw : ((v, w) : (Fin m → E) × W) = (v, 0) + (0, w) := by simp
  rw [hvw, map_add]
  refine Prod.ext ?_ ?_
  · funext j
    have := hv v j
    simp only [hg₁, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
      LinearMap.fst_apply] at this
    simp [h0, this]
  · simp [h1]

theorem summandSL_apply_comm {g : LinearMap.GeneralLinearGroup k ((Fin m → E) × W)}
    (hg : g ∈ Subgroup.centralizer ((summandSL k E W m).range : Set _))
    (h : SpecialLinearGroup (Fin m) E) (x : (Fin m → E) × W) :
    (summandSL k E W m h : (Fin m → E) × W →ₗ[k] (Fin m → E) × W)
        ((g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x) =
      (g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W)
        ((summandSL k E W m h : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x) :=
  congrArg (fun u : LinearMap.GeneralLinearGroup k ((Fin m → E) × W) =>
    (u : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x)
    (Subgroup.mem_centralizer_iff.mp hg _ ⟨h, rfl⟩)

theorem setOf_forall_summandSL_apply_eq (hm : 2 ≤ m) :
    {x : (Fin m → E) × W | ∀ s ∈ (summandSL k E W m).range,
        (s : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x = x} =
      Set.range (LinearMap.inr k (Fin m → E) W) := by
  ext ⟨v, w⟩
  constructor
  · intro hx
    have hv : v = 0 := eq_zero_of_forall_transvection_mulVec_eq hm fun i j hij =>
      congrArg Prod.fst (hx _ ⟨SpecialLinearGroup.transvection hij 1, rfl⟩)
    exact ⟨w, by rw [hv]; rfl⟩
  · rintro ⟨w', hw'⟩ _ ⟨g, rfl⟩
    rw [← hw']
    simp

theorem mem_centralizer_summandSL_iff (hm : 2 ≤ m)
    (g : LinearMap.GeneralLinearGroup k ((Fin m → E) × W)) :
    g ∈ Subgroup.centralizer ((summandSL k E W m).range : Set _) ↔
      ∃ (c : Eˣ) (D : LinearMap.GeneralLinearGroup k W), ∀ (v : Fin m → E) (w : W),
        (g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, w) =
          ((c : E) • v, (D : W →ₗ[k] W) w) := by
  constructor
  · intro hg
    obtain ⟨c, D, hcD⟩ := exists_smul_prod_of_commute_summandSL hm (summandSL_apply_comm hg)
    obtain ⟨c', D', hcD'⟩ :=
      exists_smul_prod_of_commute_summandSL hm (summandSL_apply_comm (Subgroup.inv_mem _ hg))
    have h₁ : ∀ x, (g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W)
        (((g⁻¹ : LinearMap.GeneralLinearGroup k ((Fin m → E) × W)) :
          (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have h₂ : ∀ x, ((g⁻¹ : LinearMap.GeneralLinearGroup k ((Fin m → E) × W)) :
        (Fin m → E) × W →ₗ[k] (Fin m → E) × W)
          ((g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    let i₀ : Fin m := ⟨0, by omega⟩
    have hcc : c * c' = 1 := by
      have := congrArg (fun x => x.1 i₀) (h₁ (Pi.single i₀ 1, 0))
      simpa [hcD, hcD'] using this
    have hD : ∀ w, D (D' w) = w := fun w => by
      simpa [hcD, hcD'] using congrArg Prod.snd (h₁ (0, w))
    have hD' : ∀ w, D' (D w) = w := fun w => by
      simpa [hcD, hcD'] using congrArg Prod.snd (h₂ (0, w))
    exact ⟨⟨c, c', hcc, by rw [mul_comm, hcc]⟩, ⟨D, D', LinearMap.ext hD, LinearMap.ext hD'⟩,
      hcD⟩
  · rintro ⟨c, D, hcD⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨h, rfl⟩
    refine Units.ext (LinearMap.ext fun x => ?_)
    obtain ⟨v, w⟩ := x
    simp [hcD, mulVec_smul]

open scoped commutatorElement in
theorem apply_inl_eq_of_isPerfect_of_le_centralizer (hm : 2 ≤ m)
    (R : Subgroup (LinearMap.GeneralLinearGroup k ((Fin m → E) × W)))
    (hR : R ≤ Subgroup.centralizer ((summandSL k E W m).range : Set _))
    (hRp : Group.IsPerfect R) {g : LinearMap.GeneralLinearGroup k ((Fin m → E) × W)}
    (hg : g ∈ R) (v : Fin m → E) :
    (g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, 0) = (v, 0) := by
  let F : Subgroup (LinearMap.GeneralLinearGroup k ((Fin m → E) × W)) :=
    { carrier := {g | ∀ v : Fin m → E, (g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, 0) = (v, 0)}
      mul_mem' := fun {a b} ha hb v => by
        rw [Units.val_mul, Module.End.mul_apply, hb v, ha v]
      one_mem' := fun v => rfl
      inv_mem' := fun {a} ha v => by
        conv_lhs => rw [← ha v]
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply] }
  have hscalar : ∀ a : LinearMap.GeneralLinearGroup k ((Fin m → E) × W),
      a ∈ Subgroup.centralizer ((summandSL k E W m).range : Set _) → ∃ c : Eˣ,
      (∀ v, (a : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, 0) = ((c : E) • v, 0)) ∧
      ∀ v, ((a⁻¹ : LinearMap.GeneralLinearGroup k ((Fin m → E) × W)) :
        (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, 0) = (((c⁻¹ : Eˣ) : E) • v, 0) := by
    intro a ha
    obtain ⟨c, D, hcD⟩ := (mem_centralizer_summandSL_iff hm a).mp ha
    refine ⟨c, fun v => by simp [hcD], fun v => ?_⟩
    have h : (a : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (((c⁻¹ : Eˣ) : E) • v, 0) = (v, 0) := by
      simp [hcD, smul_smul]
    conv_lhs => rw [← h]
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hC : ∀ a b : LinearMap.GeneralLinearGroup k ((Fin m → E) × W),
      a ∈ Subgroup.centralizer ((summandSL k E W m).range : Set _) →
      b ∈ Subgroup.centralizer ((summandSL k E W m).range : Set _) → ⁅a, b⁆ ∈ F := by
    intro a b ha hb v
    obtain ⟨ca, hca, hca'⟩ := hscalar a ha
    obtain ⟨cb, hcb, hcb'⟩ := hscalar b hb
    have hsc : (ca : E) * cb * ((ca⁻¹ : Eˣ) : E) * ((cb⁻¹ : Eˣ) : E) = 1 := by
      rw [mul_right_comm (ca : E), Units.mul_inv, one_mul, Units.mul_inv]
    show ((⁅a, b⁆ : LinearMap.GeneralLinearGroup k ((Fin m → E) × W)) :
      (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, 0) = (v, 0)
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, hcb', hca', hcb, hca, smul_smul, smul_smul,
      smul_smul, hsc, one_smul]
  have hRF : R ≤ F := calc
    R = ⁅R, R⁆ := (Subgroup.isPerfect_iff.mp hRp).symm
    _ ≤ F := Subgroup.commutator_le.mpr fun a ha b hb => hC a b (hR ha) (hR hb)
  exact hRF hg v

end

theorem natural_special_linear_summand_centralizer (hm : 2 ≤ m) :
    {x : (Fin m → E) × W | ∀ s ∈ (summandSL k E W m).range,
        (s : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) x = x} =
      Set.range (LinearMap.inr k (Fin m → E) W) ∧
    (∀ g : LinearMap.GeneralLinearGroup k ((Fin m → E) × W),
      g ∈ Subgroup.centralizer ((summandSL k E W m).range : Set _) ↔
        ∃ (c : Eˣ) (D : LinearMap.GeneralLinearGroup k W), ∀ (v : Fin m → E) (w : W),
          (g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, w) =
            ((c : E) • v, (D : W →ₗ[k] W) w)) ∧
    ∀ R : Subgroup (LinearMap.GeneralLinearGroup k ((Fin m → E) × W)),
      R ≤ Subgroup.centralizer ((summandSL k E W m).range : Set _) → Group.IsPerfect R →
        ∀ g ∈ R, ∀ v : Fin m → E,
          (g : (Fin m → E) × W →ₗ[k] (Fin m → E) × W) (v, 0) = (v, 0) :=
  ⟨setOf_forall_summandSL_apply_eq hm, mem_centralizer_summandSL_iff hm,
    fun R hR hRp _ hg v => apply_inl_eq_of_isPerfect_of_le_centralizer hm R hR hRp hg v⟩

end CFSG.LocalAnalysis.ComponentInitial
