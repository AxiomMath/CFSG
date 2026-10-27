module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Lin
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

open CFSG.LieType.SemisimpleCentralizers.HeldLang CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Foote.ModuleExclusions
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer CFSG.ComponentClassification

theorem exists_descent {N : ℕ} (hN : 3 ≤ N) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (b : MulAut (projectiveSL N K)) (hb3 : b ^ 3 = 1)
    (hbout : b ∉ innAutDerived (projectiveSL N K)) :
    ∃ ι : ((Fin N → ZMod 2) ≃ₗ[ZMod 2] (Fin N → ZMod 2)) →* projectiveSL N K,
      Function.Injective ι ∧ (∀ v, b (ι v) = ι v) ∧
      (∀ x : projectiveSL N K, b x = x → ∀ v, x * ι v * x⁻¹ ∈ ι.range) ∧
      (∀ x : projectiveSL N K, b x = x → x ^ 3 = 1 → x ∈ ι.range) := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨A, σ, hbeq, hσord, c, hc⟩ := exists_sigma_of_outer_three hN b hb3 hbout
  let lift : Matrix.SpecialLinearGroup (Fin N) K →* Matrix.SpecialLinearGroup (Fin N) K :=
    (CatalogueBHigherLinearAction.slConjugation N K A).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map (σ : K →+* K))
  have hlift_proj : ∀ g, proj N K (lift g) = b (proj N K g) := fun g => by
    rw [hbeq, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  have hβ_gl : ∀ g : Matrix.SpecialLinearGroup (Fin N) K,
      Matrix.SpecialLinearGroup.toGL (lift g) =
        A * glMap σ (Matrix.SpecialLinearGroup.toGL g) * A⁻¹ := fun g => by
    show Matrix.SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation N K A
      (Matrix.SpecialLinearGroup.map (σ : K →+* K) g)) = _
    rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    have : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (σ : K →+* K) g) =
        glMap σ (Matrix.SpecialLinearGroup.toGL g) := Units.ext rfl
    rw [this]
  have hcs : Ai σ (A : Matrix (Fin N) (Fin N) K) (orderOf σ) =
      ((c : Kˣ) : K) • (1 : Matrix (Fin N) (Fin N) K) := by
    rw [hσord, ← coe_normProd]
    have : normProd σ A 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c := hc
    rw [this, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  obtain ⟨y, hy⟩ := exists_twist_eq_conj σ A ((c : Kˣ) : K) hcs
  have hfix : ∀ g : Matrix.SpecialLinearGroup (Fin N) K, lift g = g ↔
      y * Matrix.SpecialLinearGroup.toGL g * y⁻¹ ∈ glFix σ := fun g => by
    have h1 : lift g = g ↔
        Matrix.SpecialLinearGroup.toGL (lift g) = Matrix.SpecialLinearGroup.toGL g :=
      ⟨fun h => by rw [h], fun h => Matrix.SpecialLinearGroup.toGL_injective h⟩
    rw [h1, hβ_gl, hy, mem_glFix]
    constructor
    · intro h
      have : glMap σ (y * Matrix.SpecialLinearGroup.toGL g * y⁻¹) =
          y * (y⁻¹ * glMap σ (y * Matrix.SpecialLinearGroup.toGL g * y⁻¹) * y) * y⁻¹ := by group
      rw [this, h]
    · intro h
      rw [h]
      group
  have hF0 : Nat.card (fixField σ) = 2 := by
    have h := card_fixField (K := K) Nat.prime_two (by norm_num : 1 ≤ 3)
      (by rw [hK]; norm_num) σ
    rw [hσord] at h
    simpa using h
  haveI : Finite (fixField σ) := inferInstance
  obtain ⟨e₀⟩ := exists_ringEquiv_zmod2 (fixField σ) hF0
  have hunit1 : ∀ d : (fixField σ)ˣ, d = 1 := fun d =>
    Units.ext ((zero_or_one_of_ringEquiv e₀ (d : fixField σ)).resolve_left d.ne_zero)
  have hdet1 : ∀ x₀ : GL (Fin N) (fixField σ),
      (x₀ : Matrix (Fin N) (Fin N) (fixField σ)).det = 1 := by
    intro x₀
    rcases zero_or_one_of_ringEquiv e₀ (x₀ : Matrix (Fin N) (Fin N) (fixField σ)).det with h | h
    · exfalso
      have := (Matrix.GeneralLinearGroup.det x₀).ne_zero
      rw [Matrix.GeneralLinearGroup.val_det_apply] at this
      exact this h
    · exact h
  have hdetΦ : ∀ x₀ : GL (Fin N) (fixField σ),
      ((y⁻¹ * glFixEmb σ x₀ * y : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det = 1 := by
    intro x₀
    have hx₀ : x₀ ∈ slGL (Fin N) (fixField σ) := mem_slGL.2 (hdet1 x₀)
    have h1 : glFixEmb σ x₀ ∈ slGL (Fin N) K :=
      (Subgroup.mem_inf.1 ((mem_slGL_inf_glFix_iff σ).2 ⟨⟨x₀, hx₀⟩, rfl⟩)).1
    have h2 := conj_mem_slGL y⁻¹ h1
    rw [inv_inv] at h2
    exact mem_slGL.1 h2
  let Φ : GL (Fin N) (fixField σ) →* Matrix.SpecialLinearGroup (Fin N) K :=
    { toFun := fun x₀ => ⟨((y⁻¹ * glFixEmb σ x₀ * y : GL (Fin N) K) : Matrix (Fin N) (Fin N) K),
        hdetΦ x₀⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have h : y⁻¹ * glFixEmb σ (a * b) * y =
            (y⁻¹ * glFixEmb σ a * y) * (y⁻¹ * glFixEmb σ b * y) := by
          rw [map_mul]
          group
        show ((y⁻¹ * glFixEmb σ (a * b) * y : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = _
        rw [h, Units.val_mul]
        rfl) }
  have hΦgl : ∀ x₀, Matrix.SpecialLinearGroup.toGL (Φ x₀) = y⁻¹ * glFixEmb σ x₀ * y :=
    fun x₀ => Units.ext rfl
  have hΦfix : ∀ x₀, lift (Φ x₀) = Φ x₀ := by
    intro x₀
    rw [hfix, hΦgl]
    have : y * (y⁻¹ * glFixEmb σ x₀ * y) * y⁻¹ = glFixEmb σ x₀ := by group
    rw [this]
    exact glFixEmb_mem σ _
  have hΦrange : ∀ g, lift g = g → ∃ x₀, g = Φ x₀ := by
    intro g hg
    have h1 : y * Matrix.SpecialLinearGroup.toGL g * y⁻¹ ∈ (glFixEmb (ι := Fin N) σ).range := by
      rw [glFixEmb_range]
      exact (hfix g).1 hg
    obtain ⟨x₀, hx₀⟩ := h1
    refine ⟨x₀, Matrix.SpecialLinearGroup.toGL_injective ?_⟩
    rw [hΦgl, hx₀]
    group
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h1 := congrArg Matrix.SpecialLinearGroup.toGL hab
    rw [hΦgl, hΦgl] at h1
    have h2 : glFixEmb σ a = glFixEmb σ b := by simpa using h1
    exact glFixEmb_injective σ h2
  have hker : ∀ x₀, proj N K (Φ x₀) = 1 → x₀ = 1 := by
    intro x₀ hx₀
    obtain ⟨c', -, hc'⟩ := (proj_eq_one_iff).1 hx₀
    have h1 : glFixEmb σ x₀ = Matrix.GeneralLinearGroup.scalar (Fin N) c' := by
      have h2 : Matrix.SpecialLinearGroup.toGL (Φ x₀) = Matrix.GeneralLinearGroup.scalar (Fin N) c' :=
        Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar]; exact hc')
      rw [hΦgl] at h2
      have h3 : glFixEmb σ x₀ = y * (y⁻¹ * glFixEmb σ x₀ * y) * y⁻¹ := by group
      rw [h3, h2, ← scalar_mul_comm c' y, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨d, hd⟩ := mem_scalars_of_glFixEmb x₀ c' h1
    rw [← hd, hunit1 d, map_one]
  have hZc : ∀ g : Matrix.SpecialLinearGroup (Fin N) K, proj N K g = 1 →
      ∀ h : Matrix.SpecialLinearGroup (Fin N) K, g * h = h * g := by
    intro g hg h
    have := (scalars_le_center N K) ((proj_eq_one_iff).1 hg)
    exact (Subgroup.mem_center_iff.1 this h).symm
  have hZ7 : ∀ g : Matrix.SpecialLinearGroup (Fin N) K, proj N K g = 1 → g ^ 7 = 1 := by
    intro g hg
    obtain ⟨c', -, hc'⟩ := (proj_eq_one_iff).1 hg
    have hc7 : c' ^ 7 = 1 := by
      have : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]
      rw [← this]
      exact pow_card_eq_one'
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hc', ← map_pow, Matrix.SpecialLinearGroup.coe_one,
      ← Units.val_pow_eq_pow_val, hc7, Units.val_one, map_one]
  let toVec : GL (Fin N) (fixField σ) ≃*
      ((Fin N → ZMod 2) ≃ₗ[ZMod 2] (Fin N → ZMod 2)) :=
    (glKZ2 N e₀).trans (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin N → ZMod 2)))
  let ι : ((Fin N → ZMod 2) ≃ₗ[ZMod 2] (Fin N → ZMod 2)) →* projectiveSL N K :=
    ((proj N K).comp Φ).comp toVec.symm.toMonoidHom
  have hι : ∀ x₀, ι (toVec x₀) = proj N K (Φ x₀) := fun x₀ => by
    show proj N K (Φ (toVec.symm (toVec x₀))) = _
    rw [MulEquiv.symm_apply_apply]
  refine ⟨ι, ?_, ?_, ?_, ?_⟩
  ·
    have hinj : Function.Injective ((proj N K).comp Φ) := by
      rw [injective_iff_map_eq_one]
      intro x₀ hx₀
      exact hker x₀ hx₀
    exact hinj.comp toVec.symm.injective
  · intro v
    obtain ⟨x₀, rfl⟩ := toVec.surjective v
    rw [hι, ← hlift_proj, hΦfix]
  · intro x hx v
    obtain ⟨x₀, rfl⟩ := toVec.surjective v
    obtain ⟨xt, rfl⟩ := proj_surjective N K x
    have hz : proj N K (xt⁻¹ * lift xt) = 1 := by
      rw [map_mul, map_inv, hlift_proj, hx, inv_mul_cancel]
    have hzc := hZc _ hz
    have hlx : lift xt = xt * (xt⁻¹ * lift xt) := by group
    have hfx : lift (xt * Φ x₀ * xt⁻¹) = xt * Φ x₀ * xt⁻¹ := by
      set z := xt⁻¹ * lift xt with hzdef
      have h1 : lift xt = xt * z := by rw [hzdef]; group
      rw [map_mul, map_mul, map_inv, hΦfix, h1]
      have hzc' : z * Φ x₀ = Φ x₀ * z := hzc _
      calc xt * z * Φ x₀ * (xt * z)⁻¹ = xt * (z * Φ x₀) * z⁻¹ * xt⁻¹ := by group
        _ = xt * (Φ x₀ * z) * z⁻¹ * xt⁻¹ := by rw [hzc']
        _ = xt * Φ x₀ * xt⁻¹ := by group
    obtain ⟨x₁, hx₁⟩ := hΦrange _ hfx
    refine ⟨toVec x₁, ?_⟩
    rw [hι, hι, ← hx₁, map_mul, map_mul, map_inv]
  · intro x hx hx3
    obtain ⟨x₂, hx₂, hx₂f⟩ := exists_fixed_lift_of_three (proj N K) (proj_surjective N K) hZc hZ7
      lift b hlift_proj hx hx3
    obtain ⟨x₀, rfl⟩ := hΦrange x₂ hx₂f
    exact ⟨toVec x₀, by rw [hι, hx₂]⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

end
