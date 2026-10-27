module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerF4
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A.GL

open CFSG.Open
open scoped commutatorElement

section FullStruct

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {d : W ≃ₗ[ZMod 2] W}

theorem fix_of_finrank_one {U : Submodule (ZMod 2) W} (hU : Module.finrank (ZMod 2) U = 1)
    {g : W ≃ₗ[ZMod 2] W} (hg : ∀ u ∈ U, g u ∈ U) : ∀ u ∈ U, g u = u := by
  have hne : U ≠ ⊥ := by
    intro h; rw [h] at hU; simp at hU
  obtain ⟨u₀, hu₀, hu₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hU' := (finrank_eq_one_iff_of_nonzero' (⟨u₀, hu₀⟩ : U) (by
    intro h; exact hu₀ne (congrArg Subtype.val h))).1 hU
  have hZ : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hall : ∀ u ∈ U, u = 0 ∨ u = u₀ := by
    intro u hu
    obtain ⟨c, hc⟩ := hU' ⟨u, hu⟩
    have : c • u₀ = u := congrArg Subtype.val hc
    rcases hZ c with rfl | rfl
    · left; rw [← this]; simp
    · right; rw [← this]; simp
  have hgu₀ : g u₀ = u₀ := by
    rcases hall _ (hg u₀ hu₀) with h | h
    · exact absurd (g.injective (by rw [h, map_zero])) hu₀ne
    · exact h
  intro u hu
  rcases hall u hu with rfl | rfl
  · simp
  · exact hgu₀

@[expose] noncomputable def resComEquiv (g : W ≃ₗ[ZMod 2] W) (hg : g * d = d * g) :
    comSp d ≃ₗ[ZMod 2] comSp d :=
  LinearEquiv.ofInjectiveEndo ((g : W →ₗ[ZMod 2] W).restrict (fun a ha => cent_com hg ha)) (by
    intro a b hab
    apply Subtype.ext
    exact g.injective (congrArg Subtype.val hab))

theorem resComEquiv_apply (g : W ≃ₗ[ZMod 2] W) (hg : g * d = d * g) (a : comSp d) :
    ((resComEquiv g hg a : comSp d) : W) = g a := rfl

end FullStruct

section FullF

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {d : W ≃ₗ[ZMod 2] W} (h3 : d ^ 3 = 1)
  [Module Fq (comSp d)] [IsScalarTower (ZMod 2) Fq (comSp d)]

@[expose] noncomputable def restrHom :
    ((comSp d) ≃ₗ[Fq] (comSp d)) →* ((comSp d) ≃ₗ[ZMod 2] (comSp d)) :=
  MonoidHom.mk' (fun g => g.restrictScalars (ZMod 2)) (fun g h => by
    apply LinearEquiv.ext
    intro a
    rfl)

theorem restrHom_injective : Function.Injective (restrHom (d := d)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply LinearEquiv.ext
  intro a
  have := congrArg (fun f : (comSp d) ≃ₗ[ZMod 2] (comSp d) => f a) hg
  exact this

@[expose] noncomputable def PsiHom : ((comSp d) ≃ₗ[Fq] (comSp d)) →* (W ≃ₗ[ZMod 2] W) :=
  (glueHom (isCompl_fixSp_comSp h3).symm).comp restrHom

theorem PsiHom_apply_left (g : (comSp d) ≃ₗ[Fq] (comSp d)) (a : comSp d) :
    PsiHom h3 g (a : W) = ((g a : comSp d) : W) :=
  glue_apply_left (isCompl_fixSp_comSp h3).symm (restrHom g) a

theorem PsiHom_apply_right (g : (comSp d) ≃ₗ[Fq] (comSp d)) (l : fixSp d) :
    PsiHom h3 g (l : W) = (l : W) :=
  glue_apply_right (isCompl_fixSp_comSp h3).symm (restrHom g) l

theorem PsiHom_injective : Function.Injective (PsiHom (d := d) h3) :=
  (glueHom_injective (isCompl_fixSp_comSp h3).symm).comp restrHom_injective

theorem PsiHom_comm (hroot : ∀ a : comSp d, (AdjoinRoot.root q4pol) • a = resComSp d a)
    (g : (comSp d) ≃ₗ[Fq] (comSp d)) : PsiHom h3 g * d = d * PsiHom h3 g := by
  have hc := (isCompl_fixSp_comSp h3).symm
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, l, rfl⟩ := exists_decomp hc v
  simp only [LinearEquiv.mul_apply, map_add]
  have hda : d (a : W) = ((resComSp d a : comSp d) : W) := rfl
  have hdl : d (l : W) = (l : W) := e_fix l.2
  rw [hda, hdl, PsiHom_apply_left, PsiHom_apply_right, PsiHom_apply_left, hdl]
  have : g (resComSp d a) = resComSp d (g a) := by
    rw [← hroot a, map_smul, hroot]
  rw [this]
  rfl

theorem cent_le_PsiHom_range (hroot : ∀ a : comSp d, (AdjoinRoot.root q4pol) • a = resComSp d a)
    (hfix : Module.finrank (ZMod 2) (fixSp d) = 1) {h : W ≃ₗ[ZMod 2] W}
    (hh : h ∈ Subgroup.centralizer ({d} : Set (W ≃ₗ[ZMod 2] W))) :
    h ∈ (PsiHom (d := d) h3).range := by
  have hc := (isCompl_fixSp_comSp h3).symm
  have hhd : h * d = d * h := Subgroup.mem_centralizer_singleton_iff.1 hh
  let hA : comSp d ≃ₗ[ZMod 2] comSp d := resComEquiv h hhd
  have hcomm : ∀ a, hA (resComSp d a) = resComSp d (hA a) := by
    intro a
    apply Subtype.ext
    show h (d (a : W)) = d (h (a : W))
    have h1 : (h * d) (a : W) = (d * h) (a : W) := by rw [hhd]
    exact h1
  let hAF : comSp d ≃ₗ[Fq] comSp d :=
    { toFun := hA
      map_add' := hA.map_add
      map_smul' := fun f a => smul_comm_of_commute hroot hcomm f a
      invFun := hA.symm
      left_inv := hA.left_inv
      right_inv := hA.right_inv }
  refine ⟨hAF, ?_⟩
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, l, rfl⟩ := exists_decomp hc v
  rw [map_add, map_add, PsiHom_apply_left, PsiHom_apply_right]
  have hl : h (l : W) = (l : W) := fix_of_finrank_one hfix (fun u hu => cent_fix hhd hu) _ l.2
  rw [hl]
  rfl

end FullF

section FullML

open Matrix

variable {A : Type} [AddCommGroup A] [Module Fq A] {m : ℕ} (b : Module.Basis (Fin m) Fq A)

@[expose] noncomputable def McompEquiv : (A ≃ₗ[Fq] A) ≃* GL (Fin m) Fq :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv Fq A).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)

@[expose] noncomputable def slToGLF : SpecialLinearGroup (Fin m) Fq →* (A ≃ₗ[Fq] A) :=
  (McompEquiv b).symm.toMonoidHom.comp SpecialLinearGroup.toGL

theorem slToGLF_injective : Function.Injective (slToGLF b) :=
  (McompEquiv b).symm.injective.comp SpecialLinearGroup.toGL_injective

theorem mem_range_slToGLF {g : A ≃ₗ[Fq] A} :
    g ∈ (slToGLF b).range ↔ GeneralLinearGroup.det (McompEquiv b g) = 1 := by
  constructor
  · rintro ⟨s, rfl⟩
    simp [slToGLF]
  · intro hg
    have : McompEquiv b g ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) Fq →* _).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hg
    obtain ⟨s, hs⟩ := this
    refine ⟨s, ?_⟩
    simp only [slToGLF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs, MulEquiv.symm_apply_apply]

end FullML

instance finite_Fq : Finite Fq := Nat.finite_of_card_ne_zero (by rw [card_Fq]; norm_num)

section FullLayer

open Matrix

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem fullLayer {d : W ≃ₗ[ZMod 2] W} (h3 : d ^ 3 = 1)
    (hfix : Module.finrank (ZMod 2) (fixSp d) = 1) {m : ℕ}
    (hm : Module.finrank (ZMod 2) (comSp d) = 2 * m) (hm2 : 2 ≤ m) :
    ∃ F : Subgroup (W ≃ₗ[ZMod 2] W),
      F ≤ Subgroup.centralizer ({d} : Set (W ≃ₗ[ZMod 2] W)) ∧
      (F.subgroupOf (Subgroup.centralizer ({d} : Set (W ≃ₗ[ZMod 2] W)))).Normal ∧
      ⁅Subgroup.centralizer ({d} : Set (W ≃ₗ[ZMod 2] W)),
        Subgroup.centralizer ({d} : Set (W ≃ₗ[ZMod 2] W))⁆ ≤ F ∧
      CFSG.Open.IsQuasisimple ↥F ∧ 3 ∣ Nat.card ↥F ∧
      Nonempty (↥F ⧸ Subgroup.center ↥F ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin m) (GaloisField 2 2)) := by
  classical
  have hq : ∀ a : comSp d, resComSp d (resComSp d a) + resComSp d a + a = 0 := by
    intro a
    apply Subtype.ext
    have := quad_of_mem_comSp h3 a.2
    simpa [resComSp_apply] using this
  obtain ⟨inst, hts, hroot⟩ := exists_fModule (resComSp d) hq
  letI := inst
  haveI := hts
  haveI : Module.Finite Fq (comSp d) := Module.Finite.of_restrictScalars_finite (ZMod 2) Fq _
  have hfrF : Module.finrank Fq (comSp d) = m := by
    have := finrank_two_mul (A := comSp d)
    omega
  let b : Module.Basis (Fin m) Fq (comSp d) := Module.finBasisOfFinrankEq Fq (comSp d) hfrF
  let Ψ := PsiHom (d := d) h3
  let ΘSL := slToGLF b
  have hinj : Function.Injective (Ψ.comp ΘSL) :=
    (PsiHom_injective h3).comp (slToGLF_injective b)
  have hΨrange : ∀ g : W ≃ₗ[ZMod 2] W,
      g ∈ Subgroup.centralizer ({d} : Set (W ≃ₗ[ZMod 2] W)) ↔ g ∈ Ψ.range := by
    intro g
    constructor
    · exact cent_le_PsiHom_range h3 hroot hfix
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (PsiHom_comm h3 hroot x)
  let F : Subgroup (W ≃ₗ[ZMod 2] W) := (Ψ.comp ΘSL).range
  have hFle : F ≤ Subgroup.centralizer ({d} : Set (W ≃ₗ[ZMod 2] W)) := by
    rintro _ ⟨s, rfl⟩
    exact (hΨrange _).2 ⟨ΘSL s, rfl⟩
  have eF : SpecialLinearGroup (Fin m) Fq ≃* ↥F := MonoidHom.ofInjective hinj
  have hdet : ∀ (g : (comSp d) ≃ₗ[Fq] (comSp d)), g ∈ ΘSL.range ↔
      GeneralLinearGroup.det (McompEquiv b g) = 1 := fun g => mem_range_slToGLF b
  have hcard4 : 4 ≤ Nat.card Fq := by rw [card_Fq]
  refine ⟨F, hFle, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.normal_subgroupOf_iff hFle]
    intro h k hh hk
    obtain ⟨s, rfl⟩ := hh
    obtain ⟨g, rfl⟩ := (hΨrange k).1 hk
    have hs1 : GeneralLinearGroup.det (McompEquiv b (ΘSL s)) = 1 := (hdet _).1 ⟨s, rfl⟩
    have hmem : g * ΘSL s * g⁻¹ ∈ ΘSL.range := by
      rw [hdet]
      simp only [map_mul, map_inv]
      rw [hs1]
      simp [mul_comm]
    obtain ⟨s', hs'⟩ := hmem
    refine ⟨s', ?_⟩
    simp only [MonoidHom.comp_apply, hs', map_mul, map_inv]
  ·
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨g₁, rfl⟩ := (hΨrange k₁).1 hk₁
    obtain ⟨g₂, rfl⟩ := (hΨrange k₂).1 hk₂
    have hmem : ⁅g₁, g₂⁆ ∈ ΘSL.range := by
      rw [hdet]
      rw [map_commutatorElement, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    obtain ⟨s', hs'⟩ := hmem
    refine ⟨s', ?_⟩
    simp only [MonoidHom.comp_apply, hs', map_commutatorElement]
  ·
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eF
      (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple_sl hm2 hcard4)
  ·
    rw [← Nat.card_congr eF.toEquiv]
    have h15 := CFSG.StandardType.LayerPDiv.sq_sub_one_dvd_card_SL (D := Fq) (d := m) hm2
    rw [card_Fq] at h15
    exact dvd_trans (by norm_num : 3 ∣ 4 ^ 2 - 1) h15
  ·
    let σ : Fq ≃+* GaloisField 2 2 :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField Fq 2 2 (by norm_num)
        (by rw [card_Fq]; norm_num)
    let eQ : ↥F ⧸ Subgroup.center ↥F ≃* SpecialLinearGroup (Fin m) Fq ⧸
        Subgroup.center (SpecialLinearGroup (Fin m) Fq) :=
      QuotientGroup.congr _ _ eF.symm (Subgroup.map_center_eq eF.symm)
    exact ⟨eQ.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv σ (Fin m))⟩

end FullLayer

end CFSG.LocalAnalysis.GLTheoremA.S172A.GL

end
