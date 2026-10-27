module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrTools
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLGraph

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Gr

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL

variable {n : ℕ} {K : Type} [Field K]

noncomputable abbrev graphLiftAut (A : GL (Fin n) K) :
    MulAut (Matrix.SpecialLinearGroup (Fin n) K) :=
  CatalogueBHigherLinearAction.slConjugation n K A * CatalogueBGraphForm.slGraphAut n K

theorem graphLiftAut_apply (A : GL (Fin n) K) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    graphLiftAut A g = graphLift A g := rfl

theorem fixedGroup_graphLiftAut (A : GL (Fin n) K) :
    ClassicalInvolution.Balance.fixedGroup (graphLiftAut A) = isometrySL n A⁻¹ := by
  ext g
  rw [ClassicalInvolution.Balance.mem_fixedGroup, graphLiftAut_apply, graphLift_eq_iff]

theorem odd_orderOf_of_mem {G : Type*} [Group G] {R : Subgroup G} [Finite R]
    (hR : Odd (Nat.card R)) {r : G} (hr : r ∈ R) : Odd (orderOf r) := by
  have h := orderOf_dvd_natCard (⟨r, hr⟩ : R)
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hR h

variable [Finite K]

theorem isQuasisimple_isometrySL_alt' (hK : ringChar K ≠ 2) (hn : 4 ≤ n) {R : GL (Fin n) K}
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) :
    IsQuasisimple (isometrySL n R) := by
  have hI : IsQuasisimple (CatalogueBGraphForm.isometryGroup n K R) :=
    LocalCores.isQuasisimple_of_mulEquiv (CatalogueBLinearHigherB.isometryGroupEquiv R)
      (CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le _
        (CatalogueBLinearHigherB.matrixForm_isAlt hK R hR)
        (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
        (by rwa [Module.finrank_fin_fun])
        (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK))
  have hdet : ∀ G ∈ CatalogueBGraphForm.isometryGroup n K R,
      (G : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro G hG
    have hperf : commutator (CatalogueBGraphForm.isometryGroup n K R) = ⊤ :=
      hI.1.commutator_eq_top
    have hle : commutator (CatalogueBGraphForm.isometryGroup n K R) ≤
        (GeneralLinearGroup.det.comp (CatalogueBGraphForm.isometryGroup n K R).subtype).ker :=
      Abelianization.commutator_subset_ker _
    have h1 := hle (hperf ▸ mem_top (⟨G, hG⟩ : CatalogueBGraphForm.isometryGroup n K R))
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff,
      GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    exact h1
  have hmap : (isometrySL n R).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K R := by
    ext G
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hG
      have hGe : SpecialLinearGroup.toGL
          (⟨(G : Matrix (Fin n) (Fin n) K), hdet G hG⟩ : SpecialLinearGroup (Fin n) K) = G :=
        Units.ext rfl
      refine ⟨_, ?_, hGe⟩
      show _ ∈ isometrySL n R
      exact Subgroup.mem_comap.2 (by rw [hGe]; exact hG)
  exact LocalCores.isQuasisimple_of_mulEquiv (((isometrySL n R).equivMapOfInjective _
    SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmap)).symm hI

theorem eq_one_symplectic (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {A : GL (Fin n) K} (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = -(A : Matrix (Fin n) (Fin n) K))
    {R : Subgroup (MulAut (projectiveSL n K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * (conjAut n K A * dualAut n K) = conjAut n K A * dualAut n K * r)
    (hRc : ∀ s, (conjAut n K A * dualAut n K) s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  set F := A⁻¹ with hFdef
  have hF : (F : Matrix (Fin n) (Fin n) K)ᵀ = -(F : Matrix (Fin n) (Fin n) K) :=
    inv_transpose_of_transpose_eq_neg A hA
  have hn4 : 4 ≤ n := by
    have hev := CatalogueBAlternatingIsometry.even_finrank _
      (CatalogueBLinearHigherB.matrixForm_isAlt hK F hF)
      (CatalogueBLinearHigherB.matrixForm_nondegenerate F)
    rw [Module.finrank_fin_fun] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  have hq := isQuasisimple_isometrySL_alt' hK hn4 hF
  have hQ₀ : Open.IsComponentOf (isometrySL n F)
      (ClassicalInvolution.Balance.fixedGroup (graphLiftAut A)) := by
    rw [fixedGroup_graphLiftAut]
    exact ⟨le_rfl, Open.IsSubnormal.refl _,
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
        ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq)⟩
  intro r hr
  obtain ⟨D, τ, rfl⟩ := Burgoyne.PSL.exists_semilinear_of_odd hn (odd_orderOf_of_mem hRodd hr)
  have hfix : ∀ g ∈ isometrySL n F,
      (conjAut n K D * fieldAut n K τ) (proj n K g) = proj n K g :=
    fun g hg => fix_of_component hinj (graphLiftAut A) (conjAut_mul_dualAut_proj A) hQ₀ hRodd hRi
      hRc hr hg
  have hv : ∀ v : Fin n → K, v ≠ 0 → τ = 1 ∧ ∃ μ : K, (D : Matrix (Fin n) (Fin n) K) *ᵥ v =
      μ • v := by
    intro v hv
    obtain ⟨b, hb⟩ := exists_vecMul_ne_zero F hv
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have hN := vecMulVec_mul_self (vecMul_dotProduct_self_of_alt hK hF v)
    obtain ⟨hτ, hD⟩ := fix_unipotent_family (p := p) hN (a := a) (b := b)
      (by rw [vecMulVec_apply]; exact mul_ne_zero ha hb)
      (fun c => unipSL (vecMul_dotProduct_self_of_alt hK hF v) c) (fun c => rfl)
      (fun c => hfix _ (symTransv_mem hK hF v c))
    exact ⟨hτ, exists_eigen_of_commute_vecMulVec hb hD⟩
  have h0 : (Pi.single ⟨0, by omega⟩ 1 : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have hτ := (hv _ h0).1
  have hD : conjAut n K D = 1 := by
    refine conjAut_eq_one_of_eq_scalar ⟨0, by omega⟩ (eq_scalar_of_eigen _ fun v => ?_)
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, mulVec_zero, smul_zero]⟩
    · exact (hv v hv0).2
  rw [hD, hτ, map_one, one_mul]

end CFSG.ComponentClassification.Foote5.OddLieCore.Gr
