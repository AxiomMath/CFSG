module

public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelectorSymmetry
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaHigherRank

public noncomputable section

namespace CFSG.ComponentClassification.EvenOrthSelector

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
  (derivedOrthogonal_map_isometry)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  evenOrthogonalRealization_of_regular)

theorem exists_derived_embedding {k W : Type} [Field k] [AddCommGroup W] [Module k W] {m : ℕ}
    {Q₀ : QuadraticForm k W} {Qc : QuadraticForm k (Fin m → k)} (ψ : Q₀.IsometryEquiv Qc) :
    ∃ j : matrixDerived Qc →* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆, Function.Injective j := by
  set c := LinearEquiv.autCongr ψ.symm.toLinearEquiv with hc
  have hmem : ∀ g : matrixDerived Qc, c (matrixLinearIso (g : GL (Fin m) k)) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q₀, TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ := by
    intro g
    rw [← derivedOrthogonal_map_isometry ψ.symm]
    exact Subgroup.mem_map_of_mem _ ((mem_matrixDerived_iff Qc _).mp g.2)
  refine ⟨(c.toMonoidHom.comp (matrixLinearIso.toMonoidHom.comp
    (matrixDerived Qc).subtype)).codRestrict _ hmem, fun g h hgh => ?_⟩
  have h1 := congrArg Subtype.val hgh
  exact Subtype.ext (matrixLinearIso.injective (c.injective h1))

variable {K : Type} [Field K]

theorem field_component {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {α : MulAut (matrixProjectiveDerived Q)} (hα : α ∈ matrixProjectiveImage Q)
    (hα2 : orderOf α = 2) {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hSα : matrixProjectiveConjugationHom Q S = α) (hσ1 : S.val.right ≠ 1)
    {X : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hX : CFSG.Assembly.IsComponentOf X
      (inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {α})) :
    IsSimpleGroup X ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (g : ℕ), Nat.card k = 2 ^ g ∧
      ∃ ι : StatedSp (n - 1) k →* X, Function.Injective ι := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := OmegaRadical.finite_mulAut_matrixProjectiveDerived Q
  have hd : 1 ≤ 2 * n := by omega
  obtain ⟨-, -, hsimple, -, ext, -, -, hinj, hinn, hNC, hnormal, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α hα hα2 S hS hSα hσ1
  set N := (extKappa Q ext).range with hNdef
  have hNY : N ≤ inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {α} := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hinn hx, (Subgroup.mem_inf.mp (hNC hx)).2⟩
  have hYE : inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {α} ≤
      matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} :=
    inf_le_inf_right _ (matrixProjective_inner_le_image Q)
  have hXN : CFSG.Assembly.IsComponentOf X N := by
    refine OutcomeLocal.isComponentOf_of_normal_of_comm hNY
      (fun y hy => OutcomeLocal.mem_normalizer_of_normal_subgroupOf hNC hnormal (hYE hy))
      (fun x hx hxN y hy hyN => ?_) hX
    have hxZ : x ∈ matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} ⊓
        Subgroup.centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) :=
      Subgroup.mem_inf.mpr ⟨hYE hx, hxN⟩
    have hyZ : y ∈ matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} ⊓
        Subgroup.centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) :=
      Subgroup.mem_inf.mpr ⟨hYE hy, hyN⟩
    rw [hcent] at hxZ hyZ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyZ
    exact zpow_mul_comm α i j
  have eN : ↥(pairDescentDerived hS) ≃* N := MonoidHom.ofInjective hinj
  have : IsSimpleGroup ↥(pairDescentDerived hS) := hsimple
  have hNs : IsSimpleGroup N := eN.symm.isSimpleGroup
  have hXeq : X = N := OutcomeLocal.eq_of_isComponentOf_simple hNs hXN
  have eX : N ≃* X := MulEquiv.subgroupCongr hXeq.symm
  refine ⟨eX.symm.isSimpleGroup, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ := evenOrthogonalRealization_of_regular hf hK hd Q hQ hT hE
  obtain ⟨hSS, hTT, -⟩ := hinv α hα hα2 S hS hSα
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs Q => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfeven, hk, -⟩ := card_descentField hf hK hσσ hσ1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent
    hσσ hσ1 hQ (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : CharP (descentField S.val.right) 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hk2 hk
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨Qc, ⟨ψ⟩, hQc, hTc, hEc⟩ := exists_coordinate_isometry hn (pairDescentForm hS) hQ₀ hdim
  obtain ⟨v, hv⟩ := exists_eq_one hd hQc
  obtain ⟨eB⟩ := exists_derivedSymmetryEquiv hQc hTc hEc hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hdimU : Module.finrank (descentField S.val.right) (vQuot Qc v) = 2 * (n - 1) := by
    have := finrank_vQuot hQc hv
    omega
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp (vQuotForm Qc v)
    (vQuotForm_isAlt Qc v) (vQuotForm_nondegenerate hQc hv0) hdimU
  obtain ⟨j, hj⟩ := exists_derived_embedding ψ
  have hle : derivedSymmetryCentralizer Qc v ≤ matrixDerived Qc := fun _ hg => hg.1
  have e₁ : StatedSp (n - 1) (descentField S.val.right) ≃* derivedSymmetryCentralizer Qc v :=
    (eSp.symm.trans (bilinIsometryGroupEquiv _).symm).trans eB.symm
  exact ⟨descentField S.val.right, inferInstance, inferInstance, f / 2, hk,
    eX.toMonoidHom.comp (eN.toMonoidHom.comp (j.comp ((Subgroup.inclusion hle).comp
      e₁.toMonoidHom))),
    eX.injective.comp (eN.injective.comp (hj.comp ((Subgroup.inclusion_injective hle).comp
      e₁.injective)))⟩

end CFSG.ComponentClassification.EvenOrthSelector
