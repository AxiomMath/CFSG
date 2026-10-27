module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableL3Core
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBoundGen

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Group

variable {F : Type} [Field F] [CharP F 2]

theorem k32_zeta_one {A Ainv u : Matrix (Fin 3) (Fin 3) F} {a b c ζ : F} (hA : A * Ainv = 1)
    (hA' : Ainv * A = 1) (hu : u = k32U3 a b c) (hz : u * A = ζ • (A * u)) : ζ = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : Matrix.trace (Ainv * (u * A)) = Matrix.trace u := by
    rw [Matrix.trace_mul_comm Ainv (u * A), Matrix.mul_assoc, hA, Matrix.mul_one]
  have h2' : Matrix.trace (Ainv * (u * A)) = ζ * Matrix.trace u := by
    rw [hz, Matrix.mul_smul, Matrix.trace_smul, ← Matrix.mul_assoc, hA', Matrix.one_mul,
      smul_eq_mul]
  have h3 : Matrix.trace u = 1 := by
    rw [hu]
    simp only [Matrix.trace_fin_three, k32U3]
    simp
    linear_combination h2
  rw [h3] at h1 h2'
  linear_combination h1 - h2'

theorem k32_l3_comm_of_fix {A : GL (Fin 3) F} {u : Matrix.SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ unitriangular 3 F) (hfix : LinearFlag.conjAut 3 F A (LinearFlag.proj 3 F u) = LinearFlag.proj 3 F u) :
    (A : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) =
      (u : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  rw [LinearFlag.conjAut_proj] at hfix
  obtain ⟨ζ, -, hmat⟩ := proj_eq_proj_iff.mp hfix
  set g := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A u with hg
  have hgu : (u : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * ((ζ : F) • 1) := by
    have h1 : (u : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ * u :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [h1, hmat, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hgmat : (g : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := coe_slConjugation A u
  have hA : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA' : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hz : (u : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (ζ : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F)) := by
    calc (u : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
        = ((g : Matrix (Fin 3) (Fin 3) F) * ((ζ : F) • 1)) * (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [← hgu]
      _ = (ζ : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) *
            ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) := by
          rw [hgmat, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = (ζ : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F)) := by
          rw [Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hA',
            Matrix.mul_one]
  have hζ := k32_zeta_one hA hA' (k32_l3_unitri_eq hu) hz
  rw [hζ, one_smul] at hz
  exact hz.symm

end Group

section Bound

variable {F : Type} [Field F]

theorem k32_l3_lift_Ubar {W : Subgroup (projectiveSL 3 F)} (hW : W ≤ projUnitriangular 3 F) :
    ∃ V : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), V ≤ unitriangular 3 F ∧
      V.map (LinearFlag.proj 3 F) = W ∧ Nat.card V = Nat.card W := by
  set V : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    unitriangular 3 F ⊓ W.comap (LinearFlag.proj 3 F) with hV
  have hVmap : V.map (LinearFlag.proj 3 F) = W := by
    ext w
    constructor
    · rintro ⟨x, ⟨-, hxW⟩, rfl⟩
      exact hxW
    · intro hw
      obtain ⟨x, hxU, hxw⟩ := hW hw
      exact ⟨x, ⟨hxU, Subgroup.mem_comap.mpr (by rw [hxw]; exact hw)⟩, hxw⟩
  refine ⟨V, inf_le_left, hVmap, ?_⟩
  let f : V → W := fun x => ⟨LinearFlag.proj 3 F x, hVmap ▸ Subgroup.mem_map_of_mem _ x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (proj_injOn_unitriangular 3 x.2.1 y.2.1 (congrArg Subtype.val hxy))
    · rintro ⟨w, hw⟩
      rw [← hVmap] at hw
      obtain ⟨x, hxV, hxw⟩ := hw
      exact ⟨⟨x, hxV⟩, Subtype.ext hxw⟩
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem k32_gl_cube {A : GL (Fin 3) F} {c : Fˣ}
    (hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    (A : Matrix (Fin 3) (Fin 3) F) ^ 3 = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hA3
  simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at h
  rw [h, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem k32_gl_not_scalar {A : GL (Fin 3) F}
    (hns : ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A) :
    ¬ ∃ x : F, (A : Matrix (Fin 3) (Fin 3) F) = x • (1 : Matrix (Fin 3) (Fin 3) F) := by
  rintro ⟨x, hx⟩
  apply hns
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hx, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, hx, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rfl

theorem k32_l3_bound_Ubar [CharP F 2] [Finite F] {A : GL (Fin 3) F} {c : Fˣ}
    (hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hns : ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A)
    {W : Subgroup (projectiveSL 3 F)} (hW : W ≤ projUnitriangular 3 F)
    (hfix : ∀ w ∈ W, LinearFlag.conjAut 3 F A w = w) : Nat.card W ≤ Nat.card F := by
  obtain ⟨V, hVU, hVmap, hVcard⟩ := k32_l3_lift_Ubar hW
  rw [← hVcard]
  refine k32_l3_core c.ne_zero (k32_gl_cube hA3) (k32_gl_not_scalar hns) hVU fun u hu => ?_
  exact k32_l3_comm_of_fix (hVU hu) (hfix _ (hVmap ▸ Subgroup.mem_map_of_mem _ hu))

theorem k32_l3_bound_Ubar_four [CharP F 2] (hK : ∀ x : F, x ^ 4 = x) {A : GL (Fin 3) F} {c : Fˣ}
    (hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hns : ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A)
    {W : Subgroup (projectiveSL 3 F)} (hW : W ≤ projUnitriangular 3 F)
    (hfix : ∀ w ∈ W, LinearFlag.conjAut 3 F A w = w) : W = ⊥ := by
  obtain ⟨V, hVU, hVmap, hVcard⟩ := k32_l3_lift_Ubar hW
  have hV : V = ⊥ := k32_l3_core_four hK hdet c.ne_zero (k32_gl_cube hA3) (k32_gl_not_scalar hns)
    hVU fun u hu => k32_l3_comm_of_fix (hVU hu) (hfix _ (hVmap ▸ Subgroup.mem_map_of_mem _ hu))
  rw [← hVmap, hV, Subgroup.map_bot]

end Bound


section Conj

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem k32_gl_scalar_comm (c : Fˣ) (g : GL (Fin 3) F) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 3) c = Matrix.GeneralLinearGroup.scalar (Fin 3) c * g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm

theorem k32_l3_conj_reduce {A : GL (Fin 3) F} {c : Fˣ}
    (hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hns : ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A)
    {W : Subgroup (projectiveSL 3 F)} (hW : IsPGroup 2 ↥W)
    (hfix : ∀ w ∈ W, LinearFlag.conjAut 3 F A w = w) :
    ∃ (A' : GL (Fin 3) F) (W' : Subgroup (projectiveSL 3 F)),
      A' ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c ∧
      (¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A') ∧
      (A' : Matrix (Fin 3) (Fin 3) F).det = (A : Matrix (Fin 3) (Fin 3) F).det ∧
      W' ≤ projUnitriangular 3 F ∧ (∀ w ∈ W', LinearFlag.conjAut 3 F A' w = w) ∧
      Nat.card W' = Nat.card W := by
  obtain ⟨P₂, hP₂⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := k32_exists_conj_le_sylow P₂ hW
  obtain ⟨h, rfl⟩ := LinearFlag.proj_surjective 3 F x
  set g : GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL h with hg
  have hconj : MulAut.conj (LinearFlag.proj 3 F h) = LinearFlag.conjAut 3 F g :=
    CFSG.RankThree.PartTwo.KFacts.conj_proj_eq_conjAut 3 F h
  have hinj : Function.Injective ((MulAut.conj (LinearFlag.proj 3 F h)).toMonoidHom) :=
    (MulAut.conj (LinearFlag.proj 3 F h)).injective
  refine ⟨g * A * g⁻¹, W.map (MulAut.conj (LinearFlag.proj 3 F h)).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (g * A * g⁻¹) ^ 3 = g * A ^ 3 * g⁻¹ := by
      have h1 := map_pow (MulAut.conj g) A 3
      simpa only [MulAut.conj_apply] using h1.symm
    rw [this, hA3, k32_gl_scalar_comm c g, mul_assoc, mul_inv_cancel, mul_one]
  · rintro ⟨x, hxA⟩
    apply hns
    refine ⟨x, ?_⟩
    have h1 : A = g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) x * g := by rw [hxA]; group
    calc Matrix.GeneralLinearGroup.scalar (Fin 3) x
        = Matrix.GeneralLinearGroup.scalar (Fin 3) x * (g⁻¹ * g) := by rw [inv_mul_cancel, mul_one]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) x * g⁻¹) * g := by rw [mul_assoc]
      _ = g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) x * g := by
          rw [k32_gl_scalar_comm x g⁻¹]
      _ = A := h1.symm
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    have h1 : (g : Matrix (Fin 3) (Fin 3) F).det *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    calc (g : Matrix (Fin 3) (Fin 3) F).det * (A : Matrix (Fin 3) (Fin 3) F).det *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det
        = ((g : Matrix (Fin 3) (Fin 3) F).det *
            ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det) *
            (A : Matrix (Fin 3) (Fin 3) F).det := by ring
      _ = (A : Matrix (Fin 3) (Fin 3) F).det := by rw [h1, one_mul]
  · rintro _ ⟨w, hw, rfl⟩
    rw [← hP₂]
    exact hx w hw
  · rintro _ ⟨w, hw, rfl⟩
    change LinearFlag.conjAut 3 F (g * A * g⁻¹) ((MulAut.conj (LinearFlag.proj 3 F h)) w) =
      (MulAut.conj (LinearFlag.proj 3 F h)) w
    have e1 : ((LinearFlag.conjAut 3 F g)⁻¹) ((LinearFlag.conjAut 3 F g) w) = w := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [hconj, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, e1, hfix w hw]
  · exact Subgroup.card_map_of_injective hinj

end Conj


section Bounds

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem k32_l3_bound {A : GL (Fin 3) F} {c : Fˣ}
    (hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hns : ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A)
    {W : Subgroup (projectiveSL 3 F)} (hW : IsPGroup 2 ↥W)
    (hfix : ∀ w ∈ W, LinearFlag.conjAut 3 F A w = w) : Nat.card W ≤ Nat.card F := by
  obtain ⟨A', W', hA3', hns', -, hW'U, hfix', hcard⟩ := k32_l3_conj_reduce hA3 hns hW hfix
  rw [← hcard]
  exact k32_l3_bound_Ubar hA3' hns' hW'U hfix'

theorem k32_l3_bound_four (hK : ∀ x : F, x ^ 4 = x) {A : GL (Fin 3) F} {c : Fˣ}
    (hdet : (A : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hns : ¬ ∃ x : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) x = A)
    {W : Subgroup (projectiveSL 3 F)} (hW : IsPGroup 2 ↥W)
    (hfix : ∀ w ∈ W, LinearFlag.conjAut 3 F A w = w) : Nat.card W = 1 := by
  obtain ⟨A', W', hA3', hns', hdet', hW'U, hfix', hcard⟩ := k32_l3_conj_reduce hA3 hns hW hfix
  have h := k32_l3_bound_Ubar_four hK (hdet'.trans hdet) hA3' hns' hW'U hfix'
  rw [← hcard, h]
  exact Subgroup.card_bot

end Bounds


end CFSG.QuasithinUnique.DoubleA3
