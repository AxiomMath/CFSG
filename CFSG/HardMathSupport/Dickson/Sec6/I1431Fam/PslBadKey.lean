module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslType
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadSplit

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.HardMathSupport.Dickson.Sec6.I923

section Key

variable {n : ℕ} {K : Type} [Field K] [Finite K]

noncomputable def specialFactorEquiv {g : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin n → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin n → K))) :
    specialFactor g h ≃* linearSpecialBlock (glA g) h := by
  refine (Subgroup.equivMapOfInjective _ (slGL n K) slGL_injective).trans
    (MulEquiv.subgroupCongr ?_)
  rw [specialFactor, Subgroup.map_comap_eq, inf_eq_right]
  exact fun _ hg => mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)

theorem specialFactor_multiplicity_eq_two
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) {g : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin n → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin n → K))) (hgood : IsGoodFactor g h)
    {r : ℕ} (hr : 10 ≤ r) (hT : IsTypeL2 r (specialFactor g h)) :
    primaryMultiplicity (glA g : Module.End K (Fin n → K)) h = 2 := by
  by_contra hne
  have hm3 : 3 ≤ primaryMultiplicity (glA g : Module.End K (Fin n → K)) h := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact h3
    · omega
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have h2 : IsTypeL2 r (linearSpecialBlock (glA g) h) :=
    p6_isTypeL2_of_equiv (specialFactorEquiv hsq hh) hT
  let b : Module.Basis (Fin (primaryMultiplicity (glA g : Module.End K (Fin n → K)) h))
      (AdjoinRoot h) (primaryComponent (glA g : Module.End K (Fin n → K)) h) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : linearSpecialBlock (glA g) h ≃*
      _root_.SpecialLinearGroup (AdjoinRoot h) (primaryComponent (glA g :
        Module.End K (Fin n → K)) h) :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict (glA g) h)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  have h3 := p6_isTypeL2_of_equiv ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm).symm h2
  exact not_isTypeL2_specialLinear hO hm3 hr h3

theorem key_specialFactor {g : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin n → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin n → K)))
    (hm2 : primaryMultiplicity (glA g : Module.End K (Fin n → K)) h = 2) {h' : GL (Fin n) K}
    (hcomm : h' * g = g * h') {ν : Kˣ}
    (h3 : h' ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) ν) :
    ∃ s ∈ specialFactor g h, ∀ m ∈ specialFactor g h, slConjugation n K h' m = s * m * s⁻¹ := by
  have hHc : glA h' ∈ gl_centralizer (glA g) := by
    show glA h' ∈ Subgroup.centralizer ({glA g} : Set _)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcomm]
  have hH3 : ∀ v, (((glA h') ^ 3 : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = (ν : K) • v := by
    intro v
    have : (glA h') ^ 3 = glA (Matrix.GeneralLinearGroup.scalar (Fin n) ν) := by
      rw [← map_pow, h3]
    rw [this]
    show (Matrix.toLin' ((Matrix.GeneralLinearGroup.scalar (Fin n) ν : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) v = (ν : K) • v
    rw [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  obtain ⟨s, hs, c, hc, hcm, hsc⟩ := exists_block_split_scalar hsq hh hm2 hHc hH3
  have hsr : s ∈ (slGL n K).range := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hs)
  obtain ⟨s0, rfl⟩ := hsr
  refine ⟨s0, by rw [specialFactor, Subgroup.mem_comap]; exact hs, fun m hm => ?_⟩
  apply slGL_injective
  have hmb : slGL n K m ∈ linearSpecialBlock (glA g) h := hm
  have e1 : slGL n K (slConjugation n K h' m) = glA h' * slGL n K m * (glA h')⁻¹ := by
    simp only [slGL, MonoidHom.comp_apply, toGL_slConjugation, map_mul, map_inv]
    rfl
  rw [e1, map_mul, map_mul, map_inv, hsc]
  have hcm' := hcm _ hmb
  calc slGL n K s0 * c * slGL n K m * (slGL n K s0 * c)⁻¹
      = slGL n K s0 * (c * slGL n K m) * c⁻¹ * (slGL n K s0)⁻¹ := by group
    _ = slGL n K s0 * (slGL n K m * c) * c⁻¹ * (slGL n K s0)⁻¹ := by rw [hcm']
    _ = slGL n K s0 * slGL n K m * (slGL n K s0)⁻¹ := by group

end Key

end CFSG.HardMathSupport.Dickson.Sec6.I1431
