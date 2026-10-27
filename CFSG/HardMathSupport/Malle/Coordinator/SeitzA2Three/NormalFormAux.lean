module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.SubfieldGL
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GL
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Foote.ModuleExclusions.ProjectiveLinear
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.FieldCubeStd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF exists_semilinear_of_cube_eq_one
  exists_conj_fieldAut_of_cube_eq_one)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
  (mem_zpowers_of_pow_three_eq_one sc scal mem_sc_iff scal_mem_sc scal_injective torusThree
    heisenbergThree diagGL monomGL)

set_option linter.unusedSectionVars false

section Std

variable {F : Type} [Field F] [Finite F]

theorem fieldCube_standardForm_noinn
    (B : Subgroup (MulAut (projectiveSL 3 F))) (hB : IsElemAbelian 3 B)
    (hout : ¬ B ≤ linearAutGroup 3 F) :
    ∃ (g : GL (Fin 3) F) (σ : F ≃+* F), orderOf σ = 3 ∧
      B.map (MulAut.conj (conjAut 3 F g)).toMonoidHom =
        Subgroup.zpowers (fieldAut 3 F σ) ⊔ (B.map (MulAut.conj (conjAut 3 F g)).toMonoidHom ⊓
          linearAutGroup 3 F) ∧
      B.map (MulAut.conj (conjAut 3 F g)).toMonoidHom ⊓ linearAutGroup 3 F ≤
        Subgroup.centralizer {fieldAut 3 F σ} := by
  obtain ⟨b₀, hb₀B, hb₀⟩ := Set.not_subset.1 hout
  have hb₀3 : b₀ ^ 3 = 1 := hB.2 b₀ hb₀B
  obtain ⟨A, σ, hα, hσ3⟩ := exists_semilinear_of_cube_eq_one (n := 3) le_rfl hb₀3
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hb₀
    rw [hα, map_one, mul_one]
    exact conjAut_mem_linearAutGroup A
  obtain ⟨hord, g₀, hg₀⟩ := exists_conj_fieldAut_of_cube_eq_one (n := 3) le_rfl hb₀3 σ A hα hσ1 hσ3
  refine ⟨g₀⁻¹, σ, hord, ?_⟩
  set c : MulAut (projectiveSL 3 F) := conjAut 3 F g₀⁻¹ with hc
  have hclin : c ∈ linearAutGroup 3 F := conjAut_mem_linearAutGroup _
  set B' : Subgroup (MulAut (projectiveSL 3 F)) := B.map (MulAut.conj c).toMonoidHom with hB'
  have hcomm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    have := congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show c * b * c⁻¹ * (c * b' * c⁻¹) = c * b' * c⁻¹ * (c * b * c⁻¹)
    have h1 : b * b' = b' * b := this
    calc c * b * c⁻¹ * (c * b' * c⁻¹) = c * (b * b') * c⁻¹ := by group
      _ = c * (b' * b) * c⁻¹ := by rw [h1]
      _ = _ := by group
  have hf : fieldAut 3 F σ ∈ B' := by
    refine ⟨b₀, hb₀B, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hg₀, hc, map_inv]
    group
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB.2 b hb, map_one]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    obtain ⟨A', τ, hx', hτ3⟩ := exists_semilinear_of_cube_eq_one (n := 3) le_rfl (hB'3 x hx)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_three_eq_one σ τ hord hτ3)
    have hfk : fieldAut 3 F σ ^ k ∈ B' := Subgroup.zpow_mem B' hf k
    have hy : x * (fieldAut 3 F σ ^ k)⁻¹ ∈ B' ⊓ linearAutGroup 3 F := by
      refine ⟨B'.mul_mem hx (B'.inv_mem hfk), ?_⟩
      have : x * (fieldAut 3 F σ ^ k)⁻¹ = conjAut 3 F A' := by
        rw [hx', mul_assoc, ← map_zpow, hk, mul_inv_cancel, mul_one]
      rw [this]; exact conjAut_mem_linearAutGroup _
    have : x = fieldAut 3 F σ ^ k * (x * (fieldAut 3 F σ ^ k)⁻¹) := by
      rw [← mul_assoc, hcomm _ hfk x hx]
      group
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩) hy
  · exact sup_le (Subgroup.zpowers_le.2 hf) inf_le_left
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm _ hf x hx.1

end Std

section Sup

variable {G : Type*} [Group G]

theorem exists_pow_mul_of_mem_sup {f : G} (hf3 : f ^ 3 = 1) {A : Subgroup G}
    (hA : ∀ a ∈ A, Commute a f) :
    ∀ x ∈ Subgroup.zpowers f ⊔ A, ∃ k : ℕ, ∃ a ∈ A, x = f ^ k * a := by
  let S : Subgroup G :=
    { carrier := {b | ∃ k : ℕ, ∃ a ∈ A, b = f ^ k * a}
      mul_mem' := by
        rintro _ _ ⟨k, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
        refine ⟨k + m, a * b, A.mul_mem ha hb, ?_⟩
        rw [pow_add, mul_assoc, ← mul_assoc a, ((hA a ha).pow_right m).eq]
        group
      one_mem' := ⟨0, 1, A.one_mem, by rw [pow_zero, mul_one]⟩
      inv_mem' := by
        rintro _ ⟨k, a, ha, rfl⟩
        refine ⟨2 * k, a⁻¹, A.inv_mem ha, ?_⟩
        have hk : (f ^ k)⁻¹ = f ^ (2 * k) := by
          rw [inv_eq_of_mul_eq_one_right]
          rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hf3, one_pow]
        rw [_root_.mul_inv_rev, ← hk, (((hA a ha).pow_right k).inv_left).inv_right.eq] }
  have hle : Subgroup.zpowers f ⊔ A ≤ S := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (fun a ha => ⟨0, a, ha, by rw [pow_zero, one_mul]⟩)
    exact ⟨1, 1, A.one_mem, by rw [pow_one, mul_one]⟩
  exact fun x hx => hle hx

end Sup

section Scalars

variable {F : Type} [Field F] [Finite F]

theorem conjAut_liftGL_eq_one_iff (σ : F ≃+* F) (M : GL (Fin 3) (fixF σ)) :
    conjAut 3 F (liftGL σ M) = 1 ↔ M ∈ sc (fixF σ) := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff
      (by norm_num) _).1 h
    have hfix : mapσ σ (Matrix.GeneralLinearGroup.scalar (Fin 3) u) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) u := by rw [← hu, mapσ_liftGL]
    rw [mapσ_scalar] at hfix
    have h0 := congrArg (fun K : GL (Fin 3) F => (K : Matrix (Fin 3) (Fin 3) F) 0 0) hfix
    simp [Matrix.GeneralLinearGroup.scalar] at h0
    have hmem : (u : F) ∈ fixF σ := mem_fixF.2 h0
    have hne : (⟨(u : F), hmem⟩ : fixF σ) ≠ 0 := fun h' => u.ne_zero (congrArg Subtype.val h')
    refine mem_sc_iff.2 ⟨Units.mk0 ⟨(u : F), hmem⟩ hne, liftGL_injective σ ?_⟩
    rw [hu]
    apply Units.ext
    ext i j
    simp [liftGL, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
    split_ifs <;> rfl
  · intro hM
    obtain ⟨c, rfl⟩ := mem_sc_iff.1 hM
    have : liftGL σ (scal c) = Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map (fixF σ).subtype.toMonoidHom c) := by
      apply Units.ext
      ext i j
      simp [liftGL, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, scal]
      split_ifs <;> rfl
    rw [this]
    exact conjAut_scalar _

end Scalars

section Nonab

open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

variable {F : Type} [Field F]

theorem nonabelian_heisenberg_any [Finite F] (h3 : 3 ∣ Nat.card F - 1) (A : Subgroup (GL (Fin 3) F))
    (hS : sc F ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc F)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ sc F)
    (hidx : ((sc F).subgroupOf A).index = 9)
    {x₀ z₀ : GL (Fin 3) F} (hx₀ : x₀ ∈ A) (hz₀ : z₀ ∈ A) (hne : x₀ * z₀ ≠ z₀ * x₀) :
    ∃ (g : GL (Fin 3) F) (lam ω : Fˣ), IsPrimitiveRoot (ω : F) 3 ∧
      A.map (MulAut.conj g).toMonoidHom = heisenbergThree F lam ω := by
  obtain ⟨ω₀, hxz⟩ := exists_scal_commutator A hcomm hx₀ hz₀
  have hω₀3 : ω₀ ^ 3 = 1 := cube_eq_one_of_commutator hxz
  have hω₀1 : ω₀ ≠ 1 := by
    rintro rfl
    apply hne
    rw [hxz, scal_one, one_mul]
  have hω₀ : IsPrimitiveRoot (ω₀ : F) 3 := isPrimitiveRoot_of_pow_three hω₀3 hω₀1
  obtain ⟨y, hyA, hy3, hyn⟩ := exists_cubeone_noncentral h3 A hS hcube hx₀ hz₀ hω₀ hxz
  obtain ⟨v, hv, ε, hyv⟩ := exists_eigenvector_of_pow_three h3 y hy3
  have hε : ε ≠ 0 := by
    rintro rfl
    apply hv
    have h1 : ((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have := congrArg (((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec) hyv
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, zero_smul, Matrix.mulVec_zero] at this
  set e : Fˣ := Units.mk0 ε hε with he
  set y₁ : GL (Fin 3) F := y * scal e⁻¹ with hy₁
  have hy₁A : y₁ ∈ A := A.mul_mem hyA (hS (scal_mem_sc _))
  have hy₁n : y₁ ∉ sc F := by
    intro h
    apply hyn
    have := (sc F).mul_mem h (scal_mem_sc e)
    rwa [hy₁, mul_assoc, ← scal_mul, inv_mul_cancel, scal_one, mul_one] at this
  have hy₁v : (y₁ : Matrix (Fin 3) (Fin 3) F).mulVec v = v := by
    rw [hy₁, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scal]
    have : (Matrix.scalar (Fin 3) ((e⁻¹ : Fˣ) : F)).mulVec v = ((e⁻¹ : Fˣ) : F) • v := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [this, Matrix.mulVec_smul, hyv, smul_smul]
    simp [he]
    rw [inv_mul_cancel₀ hε, one_smul]
  obtain ⟨w, hwA, ω', hω', hyw⟩ := exists_partner A hidx hx₀ hz₀ hω₀ hxz hy₁A hy₁n
  obtain ⟨b, hb⟩ := mem_sc_iff.mp (hcube w hwA)
  obtain ⟨g, hg1, hg2⟩ := normal_form hω' hyw hb hv hy₁v
  have hgen := eq_monomial_mul_scal A hidx hy₁A hwA hω' hyw
  refine ⟨g, b, ω', hω', ?_⟩
  have hcen : ∀ s ∈ sc F, g * s * g⁻¹ = s := by
    intro s hs
    rw [Subgroup.mem_center_iff.mp (sc_mem_center hs) g, mul_assoc, mul_inv_cancel, mul_one]
  have e1 : (MulAut.conj g).toMonoidHom y₁ = diagGL F 1 ω' (ω' ^ 2) := by
    simpa [MulAut.conj_apply] using hg1
  have e2 : (MulAut.conj g).toMonoidHom w = monomGL F b := by
    simpa [MulAut.conj_apply] using hg2
  have hD : diagGL F 1 ω' (ω' ^ 2) ∈ heisenbergThree F b ω' :=
    Subgroup.subset_closure (by simp)
  have hZ : monomGL F b ∈ heisenbergThree F b ω' := Subgroup.subset_closure (by simp)
  have hSc : ∀ s ∈ sc F, s ∈ heisenbergThree F b ω' := fun s hs =>
    Subgroup.subset_closure (Or.inl hs)
  apply le_antisymm
  · rintro _ ⟨w', hw'A, rfl⟩
    obtain ⟨i, j, c, rfl⟩ := hgen w' hw'A
    have e3 : (MulAut.conj g).toMonoidHom (scal c) = scal c := hcen _ (scal_mem_sc c)
    rw [map_mul, map_mul, map_pow, map_pow, e1, e2, e3]
    exact (heisenbergThree F b ω').mul_mem
      ((heisenbergThree F b ω').mul_mem ((heisenbergThree F b ω').pow_mem hD _)
        ((heisenbergThree F b ω').pow_mem hZ _)) (hSc _ (scal_mem_sc c))
  · rw [heisenbergThree, Subgroup.closure_le]
    refine Set.union_subset ?_ ?_
    · intro s hs
      exact ⟨s, hS hs, hcen s hs⟩
    · intro u hu
      rcases hu with rfl | rfl
      · exact ⟨w, hwA, e2⟩
      · exact ⟨y₁, hy₁A, e1⟩

theorem pgl3_rank_two_classify_any [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    (A : Subgroup (GL (Fin 3) F)) (hS : sc F ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc F)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ sc F)
    (hrank : Nat.card (A ⧸ (sc F).subgroupOf A) = 9) :
    (∃ g : GL (Fin 3) F, A.map (MulAut.conj g).toMonoidHom ≤ torusThree F) ∨
    (∃ (g : GL (Fin 3) F) (lam ω : Fˣ), IsPrimitiveRoot (ω : F) 3 ∧
      A.map (MulAut.conj g).toMonoidHom = heisenbergThree F lam ω) := by
  have hidx : ((sc F).subgroupOf A).index = 9 := hrank
  by_cases habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  · exact Or.inl (abelian_torus h3 A hS hcube habel hidx)
  · push Not at habel
    obtain ⟨x₀, hx₀, z₀, hz₀, hne⟩ := habel
    exact Or.inr (nonabelian_heisenberg_any h3 A hS hcube hcomm hidx hx₀ hz₀ hne)


end Nonab

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
