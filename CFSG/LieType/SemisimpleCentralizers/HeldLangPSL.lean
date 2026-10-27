module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSU

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open Matrix CFSG.HardMathSupport.Foote.ModuleExclusions CFSG.Open

variable {F : Type} [Field F] {d : ℕ}

theorem center_glFixEmb_iff [NeZero d] (σ : F ≃+* F) (x₀ : GL (Fin d) (fixField σ)) :
    glFixEmb σ x₀ ∈ Subgroup.center (GL (Fin d) F) ↔ x₀ ∈ Subgroup.center (GL (Fin d) (fixField σ)) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨c, hc⟩
    exact mem_scalars_of_glFixEmb x₀ c hc.symm
  · rintro ⟨c₀, rfl⟩
    exact ⟨Units.map (fixField σ).subtype.toMonoidHom c₀, (glFixEmb_scalar σ c₀).symm⟩

theorem exists_psl_fix_equiv [Finite F] [NeZero d] (σ : F ≃+* F) (g : GL (Fin d) F) (c : F)
    (hg : Ai σ (g : Matrix (Fin d) (Fin d) F) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) F)) :
    ∃ Y : Subgroup (PSL (Fin d) F), Y ≤ fixHom (slTwistBar σ g) ∧
      (Y.subgroupOf (fixHom (slTwistBar σ g))).Normal ∧
      ⁅fixHom (slTwistBar σ g), fixHom (slTwistBar σ g)⁆ ≤ Y ∧
      Nonempty (Y ≃* PSL (Fin d) (fixField σ)) := by
  obtain ⟨y, -, hfix⟩ := exists_slTwist_fix σ g c hg
  obtain ⟨y', -, hY2, hY3, hY4⟩ := exists_psl_fix σ g c hg
  set Y : Subgroup (PSL (Fin d) F) := (fixHom (slTwist σ g)).map (QuotientGroup.mk' (slScalars (Fin d) F))
    with hYdef
  have hdetΦ : ∀ x₀ : slGL (Fin d) (fixField σ),
      (y⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * y : GL (Fin d) F).val.det = 1 := by
    intro x₀
    have h1 : glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) ∈ slGL (Fin d) F :=
      (Subgroup.mem_inf.1 ((mem_slGL_inf_glFix_iff σ).2 ⟨x₀, rfl⟩)).1
    have h2 := conj_mem_slGL y⁻¹ h1
    rw [inv_inv] at h2
    exact mem_slGL.1 h2
  let Φ : slGL (Fin d) (fixField σ) →* slGL (Fin d) F :=
    { toFun := fun x₀ => ⟨y⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * y, mem_slGL.2 (hdetΦ x₀)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show y⁻¹ * glFixEmb σ ((a * b : slGL (Fin d) (fixField σ)) : GL (Fin d) (fixField σ)) * y =
          (y⁻¹ * glFixEmb σ (a : GL (Fin d) (fixField σ)) * y) *
            (y⁻¹ * glFixEmb σ (b : GL (Fin d) (fixField σ)) * y)
        rw [Subgroup.coe_mul, map_mul]
        group) }
  have hΦZ : slScalars (Fin d) (fixField σ) ≤ (slScalars (Fin d) F).comap Φ := by
    intro x₀ hx₀
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    have h1 : glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) ∈ Subgroup.center (GL (Fin d) F) :=
      (center_glFixEmb_iff σ _).2 (Subgroup.mem_subgroupOf.1 hx₀)
    show y⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * y ∈ Subgroup.center (GL (Fin d) F)
    have h2 := (inferInstance : (Subgroup.center (GL (Fin d) F)).Normal).conj_mem _ h1 y⁻¹
    rwa [inv_inv] at h2
  let Ψ : PSL (Fin d) (fixField σ) →* PSL (Fin d) F :=
    QuotientGroup.map (slScalars (Fin d) (fixField σ)) (slScalars (Fin d) F) Φ hΦZ
  have hΨmk : ∀ x₀ : slGL (Fin d) (fixField σ),
      Ψ (x₀ : PSL (Fin d) (fixField σ)) = ((Φ x₀ : slGL (Fin d) F) : PSL (Fin d) F) :=
    fun x₀ => QuotientGroup.map_mk _ _ _ _ x₀
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hΨmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h1 : y⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * y ∈ Subgroup.center (GL (Fin d) F) := ha
    have h3 : glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) ∈ Subgroup.center (GL (Fin d) F) := by
      have h4 := (inferInstance : (Subgroup.center (GL (Fin d) F)).Normal).conj_mem _ h1 y
      have h5 : y * (y⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * y) * y⁻¹ =
          glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) := by group
      rwa [h5] at h4
    exact (center_glFixEmb_iff σ _).1 h3
  have hrange : Ψ.range = Y := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective a
      refine ⟨Φ x₀, (hfix (Φ x₀)).2 ⟨x₀, rfl⟩, ?_⟩
      exact (hΨmk x₀).symm
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨x₀, hx₀⟩ := (hfix x).1 hx
      refine ⟨(x₀ : PSL (Fin d) (fixField σ)), ?_⟩
      rw [hΨmk]
      have : Φ x₀ = x := Subtype.ext hx₀.symm
      rw [this]
      rfl
  exact ⟨Y, hY2, hY3, hY4, ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hΨinj).symm⟩⟩

end CFSG.LieType.SemisimpleCentralizers.HeldLang
