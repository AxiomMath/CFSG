module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslHb
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslType
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.RankThree.CentralLift CFSG.RankThree.PartOne.Sec66T
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.HardMathSupport.Dickson.Sec6.I923

section SU

variable {ℓ f : ℕ} {E : Type} [Field E]

theorem t6psuh_not_isTypeL2_gramSU (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hE : UnitaryFieldData ℓ f E) {m : ℕ} (hm : 3 ≤ m) (hnq : ¬ (m = 3 ∧ ℓ ^ f = 2)) {r : ℕ}
    (hr : 10 ≤ r) : ¬ IsTypeL2 r ↥(gramSU hE (idGram E m)) := by
  intro hT
  haveI := hE.finite
  have hperf : Group.IsPerfect ↥(gramSU hE (idGram E m)) :=
    CFSG.RankThree.Classical.isPerfect_gramSU_one hE hm hnq
  have h1 : IsTypeL2 r (primeFormP hE (idGram E m)) :=
    (isTypeL2_congr_of_central hperf (QuotientGroup.mk' (normOneScalars hE (gramSU hE (idGram E m)) m))
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact normOneScalars_le_center hE _ m)).1 hT
  haveI hs : IsSimpleGroup (primeFormP hE (idGram E m)) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one hE hm hnq
  have hnab : ∃ a b : primeFormP hE (idGram E m), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact CFSG.RankThree.Classical.not_commute_primeFormP_one hE hm hnq hcon
  have hadm : StatedLieAdmissible .PSU m ℓ f :=
    ⟨hE.prime, hE.one_le, hm, fun hc => hnq ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv hE (isPrimeFormGram_idGram (n := m) (K := E))
  have hmodel : LieModel (primeFormP hE (idGram E m)) .PSU m ℓ f :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, E, inferInstance, inferInstance, hE.card_eq_sq,
        ⟨eP.trans (unitaryPSUEquiv hE (by omega))⟩⟩
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp)
    (center_eq_bot_of_simple hnab) hr h1

theorem t6psuh_not_isTypeL2_sesqSpecialUnitary
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hE : UnitaryFieldData ℓ f E) {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hm : 3 ≤ Module.finrank E W) (hnq : ¬ (Module.finrank E W = 3 ∧ ℓ ^ f = 2)) {r : ℕ}
    (hr : 10 ≤ r) : ¬ IsTypeL2 r ↥(sesqSpecialUnitaryGroup Hf) := by
  intro hT
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
  obtain ⟨φ⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e
    (G := (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E))
    (fun i j => by rw [he i j, Matrix.one_apply])
  exact t6psuh_not_isTypeL2_gramSU hO hE hm hnq hr (p6_isTypeL2_of_equiv φ hT)

end SU

section Rank

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem t6psuh_specialBlock_eq_kerImage {Ω : Type*} [Group Ω]
    (b : primaryFactors (x : Module.End K V)) (φ : ↥(orbitFactor B x (b : K[X])) ≃* Ω)
    (D : Ω →* (AdjoinRoot (b : K[X]))ˣ)
    (hD : ∀ s : ↥(orbitFactor B x (b : K[X])), D (φ s) =
      blockGLDet (x : Module.End K V) (b : K[X])
        (blockRestrict x (b : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩)) :
    specialBlock B x (b : K[X]) = kerImage (orbitFactor B x (b : K[X])) φ D := by
  ext g
  rw [mem_specialBlock, mem_kerImage]
  constructor
  · rintro ⟨hs, hg, h⟩
    refine ⟨hs, ?_⟩
    rw [hD ⟨g, hs⟩]
    exact h
  · rintro ⟨hs, h⟩
    refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
    rw [hD ⟨g, hs⟩] at h
    exact h

theorem t6psuh_rank_two (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ ℓ ^ f)
    (b : primaryFactors (x : Module.End K V)) (hgood : IsGoodBlock hK x b) {r : ℕ} (hr : 10 ≤ r)
    (hT : IsTypeL2 r ↥(specialBlock B x (b : K[X]))) :
    primaryMultiplicity (x : Module.End K V) (b : K[X]) = 2 := by
  by_contra hne
  haveI := hK.finite
  have hm3 : 3 ≤ primaryMultiplicity (x : Module.End K V) (b : K[X]) := by
    have := hgood.1
    omega
  by_cases hself : dualPoly hK.bar (b : K[X]) = b
  · obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ :=
      exists_selfDualFactor hself (selfDualPrimaryBlock H b hself)
    let D : ↥(sesqUnitaryGroup Hf) →* (AdjoinRoot (b : K[X]))ˣ :=
      (blockGLDet (x : Module.End K V) (b : K[X])).comp (sesqUnitaryGroup Hf).subtype
    have hD : ∀ s : ↥(orbitFactor B x (b : K[X])), D (φ s) =
        blockGLDet (x : Module.End K V) (b : K[X])
          (blockRestrict x (b : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) := fun s => by
      have h1 : (φ s : blockGL (x : Module.End K V) (b : K[X])) =
          blockRestrict x (b : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
        blockGL_ext fun v hv => hφ s v hv
      change blockGLDet (x : Module.End K V) (b : K[X])
        (φ s : blockGL (x : Module.End K V) (b : K[X])) = _
      rw [h1]
    have hspec := t6psuh_specialBlock_eq_kerImage b φ D hD
    obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (b : K[X])) φ D
    have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
      ext δ
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
      constructor
      · intro h
        refine ⟨δ.2, ?_⟩
        have := congrArg Units.val h
        simpa [D, blockGLDet] using this
      · rintro ⟨-, h⟩
        apply Units.ext
        simpa [D, blockGLDet] using h
    let e2 : ↥(specialBlock B x (b : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf) :=
      ((MulEquiv.subgroupCongr hspec).trans e).trans ((MulEquiv.subgroupCongr hker).trans
        (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)))
    have hnq : ¬ (Module.finrank (AdjoinRoot (b : K[X]))
        (primaryComponent (x : Module.End K V) (b : K[X])) = 3 ∧
        ℓ ^ (f * (b : K[X]).natDegree) = 2) := by
      rintro ⟨h3, h2⟩
      have := (isGoodBlock_numeric hq hself hgood).2 h3
      omega
    exact t6psuh_not_isTypeL2_sesqSpecialUnitary hO hE hHf hHfl hm3 hnq hr
      (p6_isTypeL2_of_equiv e2 hT)
  · obtain ⟨φ, hφ, -⟩ := exists_pairedFactor (pairedPrimaryBlock H b (Ne.symm hself))
    have hD : ∀ s : ↥(orbitFactor B x (b : K[X])),
        blockGLDet (x : Module.End K V) (b : K[X]) (φ s) =
        blockGLDet (x : Module.End K V) (b : K[X])
          (blockRestrict x (b : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) := fun s => by
      rw [show φ s = blockRestrict x (b : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ from
        blockGL_ext fun v hv => hφ s v hv]
    have hspec := t6psuh_specialBlock_eq_kerImage b φ
      (blockGLDet (x : Module.End K V) (b : K[X])) hD
    obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (b : K[X])) φ
      (blockGLDet (x : Module.End K V) (b : K[X]))
    obtain ⟨eSL⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det
      (E := AdjoinRoot (b : K[X])) (W := primaryComponent (x : Module.End K V) (b : K[X]))
    haveI : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
    exact not_isTypeL2_specialLinear hO hm3 hr
      (p6_isTypeL2_of_equiv (((MulEquiv.subgroupCongr hspec).trans e).trans eSL.symm) hT)

end Rank

end CFSG.HardMathSupport.Dickson.Sec6.I1431
