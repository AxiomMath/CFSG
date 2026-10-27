module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoSLTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerFull

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.LocalAnalysis.GLTheoremA.S172A.GL

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

section Layer

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {d : W ≃ₗ[ZMod 2] W}

private theorem resComEquiv_resComSp {k : W ≃ₗ[ZMod 2] W} (hk : k * d = d * k)
    (a : comSp d) :
    resComEquiv k hk (resComSp d a) = resComSp d (resComEquiv k hk a) := by
  apply Subtype.ext
  show k (d (a : W)) = d (k (a : W))
  have h1 : (k * d) (a : W) = (d * k) (a : W) := by rw [hk]
  exact h1

private noncomputable def resComEquivFq
    [Module Fq (comSp d)] [IsScalarTower (ZMod 2) Fq (comSp d)]
    (hroot : ∀ a : comSp d, (AdjoinRoot.root q4pol) • a = resComSp d a)
    (k : W ≃ₗ[ZMod 2] W) (hk : k * d = d * k) : comSp d ≃ₗ[Fq] comSp d :=
  { toFun := resComEquiv k hk
    map_add' := (resComEquiv k hk).map_add
    map_smul' := fun f a =>
      smul_comm_of_commute hroot (resComEquiv_resComSp (d := d) hk) f a
    invFun := (resComEquiv k hk).symm
    left_inv := (resComEquiv k hk).left_inv
    right_inv := (resComEquiv k hk).right_inv }

private theorem PsiHom_resComEquivFq (h3 : d ^ 3 = 1)
    [Module Fq (comSp d)] [IsScalarTower (ZMod 2) Fq (comSp d)]
    (hroot : ∀ a : comSp d, (AdjoinRoot.root q4pol) • a = resComSp d a)
    {k : W ≃ₗ[ZMod 2] W} (hk : k * d = d * k) (hfix : ∀ l ∈ fixSp d, k l = l) :
    PsiHom (d := d) h3 (resComEquivFq hroot k hk) = k := by
  have hc := (isCompl_fixSp_comSp h3).symm
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, l, rfl⟩ := exists_decomp hc v
  rw [map_add, map_add, PsiHom_apply_left, PsiHom_apply_right]
  rw [hfix (l : W) l.2]
  rfl

private theorem conj_glue_comSp (h3 : d ^ 3 = 1) {k : W ≃ₗ[ZMod 2] W}
    (hk : k * d = d * k) (f : comSp d ≃ₗ[ZMod 2] comSp d) :
    k * glue (isCompl_fixSp_comSp h3).symm f * k⁻¹ =
      glue (isCompl_fixSp_comSp h3).symm
        (resComEquiv k hk * f * (resComEquiv k hk)⁻¹) := by
  have hc := (isCompl_fixSp_comSp h3).symm
  have hki : k⁻¹ * d = d * k⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.1
      ((Subgroup.centralizer _).inv_mem (Subgroup.mem_centralizer_singleton_iff.2 hk))
  have hkF_inv : (resComEquiv k hk)⁻¹ = resComEquiv k⁻¹ hki :=
    inv_eq_of_mul_eq_one_right (by
      apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      exact LinearEquiv.apply_symm_apply k (u : W))
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, u', rfl⟩ := exists_decomp hc v
  simp only [LinearEquiv.mul_apply, map_add]
  have hu : k⁻¹ (u : W) ∈ comSp d := cent_com hki u.2
  have hu' : k⁻¹ (u' : W) ∈ fixSp d := cent_fix hki u'.2
  rw [show k⁻¹ (u : W) = (((⟨_, hu⟩ : comSp d)) : W) from rfl,
    show k⁻¹ (u' : W) = (((⟨_, hu'⟩ : fixSp d)) : W) from rfl,
    glue_apply_left, glue_apply_right]
  have e1 : (resComEquiv k hk)⁻¹ u = ⟨k⁻¹ (u : W), hu⟩ := by
    rw [hkF_inv]
    apply Subtype.ext
    rfl
  rw [glue_apply_left, glue_apply_right]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, resComEquiv_apply]
  congr 1
  exact apply_inv_apply k (u' : W)

end Layer

section DetBasis

variable {A : Type} [AddCommGroup A] [Module Fq A] {m : ℕ}
  (b : Module.Basis (Fin m) Fq A)

private theorem det_McompEquiv_eq_one {g : A ≃ₗ[Fq] A}
    (hg : LinearMap.det (g : A →ₗ[Fq] A) = 1) :
    Matrix.GeneralLinearGroup.det (McompEquiv b g) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hmat : ((McompEquiv b g : Matrix.GeneralLinearGroup (Fin m) Fq) :
      Matrix (Fin m) (Fin m) Fq) = LinearMap.toMatrix b b (g : A →ₗ[Fq] A) := rfl
  rw [hmat, LinearMap.det_toMatrix, hg]

end DetBasis

private theorem two_eq_zero_Fq : (2 : Fq) = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc (2 : Fq) = algebraMap (ZMod 2) Fq (2 : ZMod 2) :=
        (map_natCast (algebraMap (ZMod 2) Fq) 2).symm
    _ = algebraMap (ZMod 2) Fq 0 := by rw [h2]
    _ = 0 := map_zero _

private theorem neg_one_eq_one_Fq : (-1 : Fq) = 1 := by
  have h : (1 : Fq) + 1 = 0 := by rw [one_add_one_eq_two, two_eq_zero_Fq]
  exact neg_eq_of_add_eq_zero_right h

theorem lin_two_gf4_layer {g : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1) {m : ℕ}
    (hm : Module.finrank (ZMod 2) (comSp g) = 2 * m) (hm2 : 2 ≤ m) :
    ∃ F : Subgroup (V ≃ₗ[ZMod 2] V),
      F ≤ Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)) ∧
      (F.subgroupOf (Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥F ∧ (∀ f ∈ F, ∀ l ∈ fixSp g, f l = l) ∧
      (∀ u ∈ comSp g, ∀ w ∈ comSp g, u ≠ 0 → w ≠ 0 → ∃ f ∈ F, f u = w) ∧
      ∀ k ∈ Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)),
        (∀ l ∈ fixSp g, k l = l) → k * k = 1 → k ∈ F := by
  classical
  have hq : ∀ a : comSp g, resComSp g (resComSp g a) + resComSp g a + a = 0 := by
    intro a
    apply Subtype.ext
    have := quad_of_mem_comSp hg3 a.2
    simpa [resComSp_apply] using this
  obtain ⟨inst, hts, hroot⟩ := exists_fModule (resComSp g) hq
  letI := inst
  haveI := hts
  haveI : Module.Finite Fq (comSp g) := Module.Finite.of_restrictScalars_finite (ZMod 2) Fq _
  have hfrF : Module.finrank Fq (comSp g) = m := by
    have := finrank_two_mul (A := comSp g)
    omega
  let b : Module.Basis (Fin m) Fq (comSp g) := Module.finBasisOfFinrankEq Fq (comSp g) hfrF
  let Ψ := PsiHom (d := g) hg3
  let ΘSL := slToGLF b
  have hinj : Function.Injective (Ψ.comp ΘSL) :=
    (PsiHom_injective hg3).comp (slToGLF_injective b)
  let F : Subgroup (V ≃ₗ[ZMod 2] V) := (Ψ.comp ΘSL).range
  have hFle : F ≤ Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V)) := by
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact PsiHom_comm hg3 hroot (ΘSL s)
  have hcard4 : 4 ≤ Nat.card Fq := by rw [card_Fq]
  refine ⟨F, hFle, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hFle]
    intro h k hh hk
    obtain ⟨s, rfl⟩ := hh
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    have hc := (isCompl_fixSp_comSp hg3).symm
    let kF := resComEquivFq (d := g) hroot k hk
    have hs1 : Matrix.GeneralLinearGroup.det (McompEquiv b (ΘSL s)) = 1 :=
      (mem_range_slToGLF b).1 ⟨s, rfl⟩
    have hconj : k * (Ψ.comp ΘSL) s * k⁻¹ = Ψ (kF * ΘSL s * kF⁻¹) := by
      show k * Ψ (ΘSL s) * k⁻¹ = Ψ (kF * ΘSL s * kF⁻¹)
      rw [show Ψ (ΘSL s) = glue hc (restrHom (ΘSL s)) from rfl,
        conj_glue_comSp hg3 hk (restrHom (ΘSL s))]
      congr 1
    have hdet : Matrix.GeneralLinearGroup.det (McompEquiv b (kF * ΘSL s * kF⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hs1]
      simp [mul_comm]
    obtain ⟨s', hs'⟩ := (mem_range_slToGLF b).2 hdet
    refine ⟨s', ?_⟩
    rw [MonoidHom.comp_apply, hs', ← hconj]
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective hinj)
      (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple_sl hm2 hcard4)
  · intro f hf l hl
    obtain ⟨s, rfl⟩ := hf
    exact PsiHom_apply_right hg3 (ΘSL s) ⟨l, hl⟩
  · intro u hu w hw hu0 hw0
    let u' : comSp g := ⟨u, hu⟩
    let w' : comSp g := ⟨w, hw⟩
    have hu' : u' ≠ 0 := fun h => hu0 (Subtype.ext_iff.mp h)
    have hw' : w' ≠ 0 := fun h => hw0 (Subtype.ext_iff.mp h)
    have hA : 2 ≤ Module.finrank Fq (comSp g) := by rw [hfrF]; exact hm2
    obtain ⟨T, hTdet, hTu⟩ := lin_two_sl_transitive (K := Fq) (A := comSp g) hA hu' hw'
    have hdetT : Matrix.GeneralLinearGroup.det (McompEquiv b T) = 1 :=
      det_McompEquiv_eq_one b hTdet
    obtain ⟨s, hs⟩ := (mem_range_slToGLF b).2 hdetT
    refine ⟨(Ψ.comp ΘSL) s, ⟨s, rfl⟩, ?_⟩
    change Ψ (ΘSL s) (u' : V) = (w' : V)
    rw [PsiHom_apply_left, hs, hTu]
  · intro k hk hkfix hk2
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    let kF := resComEquivFq (d := g) hroot k hk
    have hk_eq : Ψ kF = k := PsiHom_resComEquivFq (d := g) hg3 hroot hk hkfix
    have hkF2 : kF * kF = 1 := by
      apply PsiHom_injective hg3
      rw [map_mul, hk_eq, hk2, map_one]
    have hdet : LinearMap.det (kF : comSp g →ₗ[Fq] comSp g) = 1 := by
      have hd1 : LinearEquiv.det kF * LinearEquiv.det kF = 1 := by
        rw [← map_mul, hkF2, map_one]
      have hd2 : (LinearMap.det (kF : comSp g →ₗ[Fq] comSp g)) ^ 2 = 1 := by
        have := congrArg (fun u : Fqˣ => (u : Fq)) hd1
        simpa [LinearEquiv.coe_det, pow_two] using this
      rcases sq_eq_one_iff.mp hd2 with h | h
      · exact h
      · rw [h]; exact neg_one_eq_one_Fq
    have hdetGL : Matrix.GeneralLinearGroup.det (McompEquiv b kF) = 1 :=
      det_McompEquiv_eq_one b hdet
    obtain ⟨s, hs⟩ := (mem_range_slToGLF b).2 hdetGL
    exact ⟨s, by rw [MonoidHom.comp_apply, hs, hk_eq]⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
