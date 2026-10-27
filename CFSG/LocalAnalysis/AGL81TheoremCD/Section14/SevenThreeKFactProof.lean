module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFact
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactCore
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactQuad
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactScalars
import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineSp
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeSpMain
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LargeExtraspecial.OfFStar
import CFSG.LargeExtraspecial.Types
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.SignLines
import CFSG.RankThree.GroupTheory.ClassTwoThree
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
import CFSG.Sporadic.Co2Smith.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.Timmesfeld.Outcome
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

open CFSG.Open Matrix
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.Sp6
  (three_ne_zero_of_not_dvd_card)

private theorem three_ne_zero_of_card_eq_pow {K : Type} [Field K] [Finite K] {q k : ℕ}
    (hK : Nat.card K = q ^ k) (hq : q % 3 ≠ 0) : (3 : K) ≠ 0 := by
  refine three_ne_zero_of_not_dvd_card ?_
  rw [hK]
  intro hd
  exact hq (Nat.dvd_iff_mod_eq_zero.mp (Nat.prime_three.dvd_of_dvd_pow hd))

private theorem isometry_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    (Q : QuadraticForm K (ι → K)) {H : Subgroup (GL ι K)}
    (hH : ∀ g ∈ H, ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    (ρ : GL ι K →* ((ι → K) ≃ₗ[K] (ι → K)))
    (hρ : ∀ A : GL ι K, (ρ A).toLinearMap = Matrix.toLin' (A : Matrix ι ι K))
    {g : GL ι K} (hg : g ∈ H) : ∀ v, Q (ρ g v) = Q v := by
  intro v
  have hv : ρ g v = (Matrix.toLin' (g : Matrix ι ι K)) v := by
    have h := congrArg (fun f : (ι → K) →ₗ[K] (ι → K) => f v) (hρ g)
    simpa using h
  rw [hv, Matrix.toLin'_apply]
  exact hH g hg v

theorem false_of_statedProj_of_card_le_seven {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : (3 : K) ≠ 0) (hι : Fintype.card ι ≤ 7)
    {H : Subgroup (GL ι K)} (hsc : ∀ g ∈ H, g ∈ StatedScalars ι K → g ^ 3 = 1 → g = 1)
    {S : Type} [Group S] (e : S ≃* StatedProj H) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨X, ψ, -, hψ, h3⟩ := exists_subgroup_surjective_of_statedProj hsc e I φ hφ hker
  have h8 := eight_le_card_of_surjective hK X ψ hψ h3
  omega

theorem false_of_statedProj_of_isometry_of_card_eq_eight {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] (hK : (3 : K) ≠ 0)
    (hι : Fintype.card ι = 8) (Q : QuadraticForm K (ι → K)) {H : Subgroup (GL ι K)}
    (hH : ∀ g ∈ H, ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    (hQ : ∀ W : Submodule K (ι → K), (∀ w ∈ W, Q w = 0) → Module.finrank K W ≤ 3)
    (hsc : ∀ g ∈ H, g ∈ StatedScalars ι K → g ^ 3 = 1 → g = 1)
    {S : Type} [Group S] (e : S ≃* StatedProj H) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  classical
  let ρ : GL ι K →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom.comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hρ : ∀ A : GL ι K, (ρ A).toLinearMap = Matrix.toLin' (A : Matrix ι ι K) :=
    fun A => toLinearMap_generalLinearEquiv_toLin A
  obtain ⟨X, ψ, hXH, hψ, h3⟩ := exists_subgroup_surjective_of_statedProj hsc e I φ hφ hker
  obtain ⟨y, hyX, z, hzX, hy3, hz3, hyz, hle⟩ :=
    exists_commute_eight_add_finrank_le_card hK X ψ hψ h3
  have hfixdim : Module.finrank K ↥((Matrix.toLin' (y : Matrix ι ι K) - 1).ker ⊓
      (Matrix.toLin' (z : Matrix ι ι K) - 1).ker) = 0 := by
    rw [hι] at hle
    omega
  have hfix : ((ρ y).toLinearMap - 1).ker ⊓ ((ρ z).toLinearMap - 1).ker = ⊥ := by
    rw [hρ y, hρ z]
    exact Submodule.finrank_eq_zero.mp hfixdim
  have hdim : 8 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨W, hWdim, hWsing⟩ :=
    exists_totallySingular_of_commute hK Q (isometry_of_mem Q hH ρ hρ (hXH hyX))
      (isometry_of_mem Q hH ρ hρ (hXH hzX)) (by rw [← map_pow, hy3, map_one])
      (by rw [← map_pow, hz3, map_one]) (hyz.map ρ) hfix hdim
  have hle3 := hQ W hWsing
  rw [hWdim] at hle3
  norm_num at hle3

theorem false_of_statedProj_statedOmega_quadMinus {K : Type} [Field K] [Finite K]
    (hK : (3 : K) ≠ 0) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {S : Type}
    [Group S] (e : S ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  refine false_of_statedProj_of_isometry_of_card_eq_eight hK (by simp)
    (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) ?_ ?_ ?_ e I φ hφ hker
  · intro g hg v
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.mem_statedOmega_quad
      (StatedQuadMinus 4 K b c) hg v
  · intro W hW
    exact finrank_le_three_of_statedQuadMinus_four hirr fun w hw => by
      rw [← CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact hW w hw
  · intro g hg hs h3
    exact eq_one_of_mem_statedOmega_statedQuadMinus_of_mem_statedScalars 4 b c hg hs h3

private theorem false_of_psp_three {S : Type} [Group S] {p f : ℕ} (hp3 : p ≠ 3)
    (hL : CFSG.Blueprint.LieModel S .PSp 3 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hpmod : p % 3 ≠ 0 := by
    intro h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
  exact false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p) (k := f) hcard hpmod) (by simp)
    (fun g hg hs h3 => eq_one_of_mem_statedSp_of_mem_statedScalars hg hs h3) e I φ hφ hker

private theorem false_of_pomegaMinus_four {S : Type} [Group S] {p f : ℕ} (hp3 : p ≠ 3)
    (hL : CFSG.Blueprint.LieModel S .POmegaMinus 4 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, b, c, hirr, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hpmod : p % 3 ≠ 0 := by
    intro h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
  exact false_of_statedProj_statedOmega_quadMinus
    (three_ne_zero_of_card_eq_pow (q := p) (k := f) hcard hpmod) hirr e I φ hφ hker

private theorem false_of_psl_four {S : Type} [Group S] {p f : ℕ} (hq : p ^ f % 3 = 1)
    (hL : CFSG.Blueprint.LieModel S .PSL 4 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨-, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hq0 : p ^ f % 3 ≠ 0 := by omega
  refine false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p ^ f) (k := 1) (by simpa using hcard) hq0)
    (by simp) ?_ e I φ hφ hker
  intro g hg hs h3
  exact eq_one_of_mem_statedSL_of_mem_statedScalars (Or.inl (by norm_num)) hg hs h3

private theorem false_of_psu_four {S : Type} [Group S] {p f : ℕ} (hq : p ^ f % 3 = 2)
    (hL : CFSG.Blueprint.LieModel S .PSU 4 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hq0 : p ^ f % 3 ≠ 0 := by omega
  refine false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p ^ f) (k := 2) hcard hq0) (by simp) ?_ e I φ hφ hker
  intro g hg hs h3
  exact eq_one_of_mem_statedSU_of_mem_statedScalars hp hcard (Or.inl (by norm_num)) hg hs h3

private theorem false_of_psl_six {S : Type} [Group S] {p f : ℕ} (hq : p ^ f % 3 = 2)
    (hL : CFSG.Blueprint.LieModel S .PSL 6 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨-, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hnd1 : ¬ 3 ∣ Nat.card K - 1 := by
    rw [hcard]
    intro hd
    have h0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  have hq0 : p ^ f % 3 ≠ 0 := by omega
  refine false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p ^ f) (k := 1) (by simpa using hcard) hq0)
    (by simp) ?_ e I φ hφ hker
  intro g hg hs h3
  exact eq_one_of_mem_statedSL_of_mem_statedScalars (Or.inr hnd1) hg hs h3

private theorem false_of_psu_six {S : Type} [Group S] {p f : ℕ} (hq : p ^ f % 3 = 1)
    (hL : CFSG.Blueprint.LieModel S .PSU 6 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hnd1 : ¬ 3 ∣ p ^ f + 1 := by
    intro hd
    have h0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  have hq0 : p ^ f % 3 ≠ 0 := by omega
  refine false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p ^ f) (k := 2) hcard hq0) (by simp) ?_ e I φ hφ hker
  intro g hg hs h3
  exact eq_one_of_mem_statedSU_of_mem_statedScalars hp hcard (Or.inr hnd1) hg hs h3

private theorem false_of_psl_seven {S : Type} [Group S] {p f : ℕ} (hq : p ^ f % 3 = 2)
    (hL : CFSG.Blueprint.LieModel S .PSL 7 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨-, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hq0 : p ^ f % 3 ≠ 0 := by omega
  refine false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p ^ f) (k := 1) (by simpa using hcard) hq0)
    (by simp) ?_ e I φ hφ hker
  intro g hg hs h3
  exact eq_one_of_mem_statedSL_of_mem_statedScalars (Or.inl (by norm_num)) hg hs h3

private theorem false_of_psu_seven {S : Type} [Group S] {p f : ℕ} (hq : p ^ f % 3 = 1)
    (hL : CFSG.Blueprint.LieModel S .PSU 7 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hq0 : p ^ f % 3 ≠ 0 := by omega
  refine false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p ^ f) (k := 2) hcard hq0) (by simp) ?_ e I φ hφ hker
  intro g hg hs h3
  exact eq_one_of_mem_statedSU_of_mem_statedScalars hp hcard (Or.inl (by norm_num)) hg hs h3

private theorem false_of_pomegaOdd_three {S : Type} [Group S] {p f : ℕ} (hp3 : p ≠ 3)
    (hL : CFSG.Blueprint.LieModel S .POmegaOdd 3 p f) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : False := by
  obtain ⟨⟨hp, -⟩, K, _, _, hcard, ⟨e⟩⟩ := hL.statedClassicalModel (by decide)
  have hpmod : p % 3 ≠ 0 := by
    intro h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
  exact false_of_statedProj_of_card_le_seven
    (three_ne_zero_of_card_eq_pow (q := p) (k := f) hcard hpmod) (by simp)
    (fun g hg hs h3 => eq_one_of_mem_statedOmega_statedQuadOdd_of_mem_statedScalars 3 hg hs h3)
    e I φ hφ hker

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

theorem kFactA9NotInvolvedK34Classical_holds : KFactA9NotInvolvedK34Classical := by
  intro S _ _ h I _ φ hφ hker
  rcases h with ⟨p, f, hp3, hL⟩ | ⟨p, f, hp3, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, -, hL⟩ |
    ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hp3, hL⟩
  · exact false_of_psp_three hp3 hL I φ hφ hker
  · exact false_of_pomegaMinus_four hp3 hL I φ hφ hker
  · exact false_of_psl_four hq hL I φ hφ hker
  · exact false_of_psu_four hq hL I φ hφ hker
  · exact false_of_psl_six hq hL I φ hφ hker
  · exact false_of_psu_six hq hL I φ hφ hker
  · exact false_of_psl_seven hq hL I φ hφ hker
  · exact false_of_psu_seven hq hL I φ hφ hker
  · exact false_of_pomegaOdd_three hp3 hL I φ hφ hker

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
