module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLin
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped Matrix

variable {K : Type} [Field K] [Finite K]

theorem conjAut_eq_one_of_isGoodFactor_two {A : GL (Fin 2) K} {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin 2 → K))) (hgood : IsGoodFactor A h) :
    LinearFlag.conjAut 2 K A = 1 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm : 2 ≤ finrank (AdjoinRoot h) (primaryComponent (glA A : Module.End K (Fin 2 → K)) h) := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact le_trans (by norm_num) h3
    · exact h2
  have hdeg : 0 < h.natDegree := natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible (irreducible_of_mem_primaryFactors hh))
  have hfr := finrank_primaryComponent (x := (glA A : Module.End K (Fin 2 → K))) (a := h)
  have hle : finrank K (primaryComponent (glA A : Module.End K (Fin 2 → K)) h) ≤ 2 := by
    have := Submodule.finrank_le (primaryComponent (glA A : Module.End K (Fin 2 → K)) h)
    simpa using this
  have hdeg1 : h.natDegree = 1 := by
    rw [hfr] at hle
    nlinarith
  have htop : primaryComponent (glA A : Module.End K (Fin 2 → K)) h = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hfr, hdeg1, one_mul]
    simp only [finrank_fin_fun]
    rw [hfr, hdeg1, one_mul] at hle
    omega
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hX : h = X + C (h.coeff 0) := hmon.eq_X_add_C hdeg1
  have hAv : ∀ v : Fin 2 → K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v = (-h.coeff 0) • v := by
    intro v
    have hv : v ∈ primaryComponent (glA A : Module.End K (Fin 2 → K)) h := by
      rw [htop]
      exact Submodule.mem_top
    have h1 := mem_primaryComponent.mp hv
    rw [hX, map_add, aeval_X, aeval_C, LinearMap.add_apply, Module.algebraMap_end_apply,
      glA_apply_eq_mulVec] at h1
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h1
  have hb : -h.coeff 0 ≠ 0 := by
    intro h0
    have h1 := hAv (Pi.single 0 1)
    rw [h0, zero_smul] at h1
    have h2 : (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ (Pi.single 0 1 : Fin 2 → K))) = Pi.single 0 1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [h1, Matrix.mulVec_zero] at h2
    have := congrFun h2 0
    simp at this
  have hAsc : A = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ hb) := by
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hAv v, glScalar_mulVec, Units.val_mk0]
  rw [hAsc]
  exact CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.conjAut_scalar' _

theorem planeNoComp_projectiveSL_two {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    PlaneNoComp p (LinearFlag.projectiveSL 2 K) := by
  classical
  intro P hP hcard J hJ
  haveI : Fact p.Prime := ⟨hp⟩
  set e : PSL2 K ≃* LinearFlag.projectiveSL 2 K := psl2Equiv K with he
  set P₀ : Subgroup (MulAut (PSL2 K)) := P.map (MulAut.congr e.symm).toMonoidHom with hP₀
  have hP₀e : IsElemAbelian p P₀ := hP.map _
  have hcard₀ : Nat.card P₀ = p ^ 2 := by
    rw [← hcard, hP₀]
    exact Subgroup.card_map_of_injective (MulAut.congr e.symm).injective
  haveI : IsElementaryAbelian p ↥P₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p P₀).2 hP₀e
  set φ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom with hφ
  obtain ⟨β₀, hβ₀P, hβ₀1, hφβ₀⟩ : ∃ β₀ ∈ P₀, β₀ ≠ 1 ∧ φ β₀ = 1 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (φ.comp P₀.subtype) := by
      rw [injective_iff_map_eq_one]
      intro b hb
      by_contra hb1
      exact hcon b b.2 (fun h1 => hb1 (Subtype.ext h1)) hb
    haveI := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isCyclic_ringAut K
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard₀
      (isCyclic_of_injective _ hinj)
  set y := (semilinearEquivAut K).symm β₀ with hy
  have hyr : y.right = 1 := hφβ₀
  have hyl : y = SemidirectProduct.inl y.left := by
    apply SemidirectProduct.ext
    · rfl
    · rw [hyr]
      rfl
  have hβ₀ : β₀ = pglAction K y.left := by
    have h1 : β₀ = semilinearEquivAut K y := by rw [hy, MulEquiv.apply_symm_apply]
    rw [h1, hyl]
    exact semilinearAction_inl K _
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective y.left
  obtain ⟨β, hβP, hββ₀⟩ := hβ₀P
  have hβ : β = LinearFlag.conjAut 2 K A := by
    have h1 : β = MulAut.congr e β₀ := by
      rw [← hββ₀]
      change β = MulAut.congr e (MulAut.congr e.symm β)
      ext x
      simp [MulAut.congr_apply]
    rw [h1, hβ₀, ← hA]
    exact congr_pglAction_mk A
  have hβ1 : β ≠ 1 := by
    rintro rfl
    apply hβ₀1
    rw [← hββ₀]
    exact map_one _
  have hβ₀p : β₀ ^ p = 1 := hP₀e.2 β₀ ⟨β, hβP, hββ₀⟩
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, A ^ p = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    have h1 : pglAction K (Matrix.ProjGenLinGroup.mk (A ^ p)) = pglAction K 1 := by
      rw [map_pow, map_pow, hA, ← hβ₀, hβ₀p, map_one]
    have h2 := Matrix.ProjGenLinGroup.mk_eq_one.1 (pglAction_injective K h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, hc.symm⟩
  have hJA := hJ β hβP hβ1
  rw [hβ] at hJA
  have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJA
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJA (perfectInLayer_conjAut hpK hc J hJA.1 hperfJ)).1
  obtain ⟨⟨⟨h, hh⟩, hgood⟩, -⟩ := linear_inner_components hpK hc J hcomp
  exact hβ1 (hβ.trans (conjAut_eq_one_of_isGoodFactor_two hh hgood))

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
