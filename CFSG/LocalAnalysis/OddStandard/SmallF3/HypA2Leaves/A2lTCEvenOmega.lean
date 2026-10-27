module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

namespace A2lPumpEvenTCOmega

section StatedSp

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem evenTCConc_statedSp (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    {g r : ℕ} (hg : 1 ≤ g) (hK : Nat.card K = 2 ^ g) (hr : 3 ≤ r) {τ : StatedLieTag} {n f : ℕ}
    (M : Subgroup (StatedSp r K)) (hM : IsPComponent 2 M) : EvenTCConc τ n f M :=
  fun hS => absurd (a2l_statedSp_tc hO hg hK (by omega) M hM hS).1 (by omega)

end StatedSp

section Omega

open CFSG Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatLeafProof

theorem exists_lieModel_derivedOrthogonal_typed {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {g n : ℕ} (hg : 1 ≤ g) (hk : Nat.card k = 2 ^ g)
    (hn : 4 ≤ n) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : finrank k W = 2 * n) :
    ∃ (τ' : StatedLieTag) (Y : Type) (_ : Group Y), (τ' = .POmegaPlus ∨ τ' = .POmegaMinus) ∧
      StatedLieAdmissible τ' n 2 g ∧ Blueprint.LieModel Y τ' n 2 g ∧
      Nonempty (↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ ≃* Y) := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have key : ∀ (Qc : QuadraticForm k (Fin (2 * n) → k)), Q₀.IsometryEquiv Qc →
      Qc.polarBilin.Nondegenerate →
      (∃ T : Submodule k (Fin (2 * n) → k), finrank k T = 3 ∧ ∀ x ∈ T, Qc x = 0) →
      ⁅TauCeti.QuadraticMap.orthogonalGroup Qc, TauCeti.QuadraticMap.orthogonalGroup Qc⁆ =
        elementaryGroup Qc →
      Nonempty (↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
        TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ ≃* matrixProjectiveDerived Qc) := by
    intro Qc ψ hQc hTc hEc
    have hZ := (evenOrthogonalRealization_of_regular hg hk (by omega) Qc hQc hTc hEc).1
    have e1 := (Subgroup.equivMapOfInjective _
      (LinearEquiv.autCongr ψ.toLinearEquiv).toMonoidHom
      (LinearEquiv.autCongr ψ.toLinearEquiv).injective).trans
        (MulEquiv.subgroupCongr
          (CatalogueBOrthogonalPointIsometry.derivedOrthogonal_map_isometry ψ))
    have e2 := ((matrixDerived Qc).equivMapOfInjective matrixLinearIso.toMonoidHom
      matrixLinearIso.injective).trans
        (MulEquiv.subgroupCongr (CatalogueBOrthogonalFixedTransfer.matrixDerived_map Qc))
    exact ⟨e1.trans (e2.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)⟩
  rcases (finite_even_regular_quadratic_normal_forms Q₀ hQ₀).2.2.1 n (by omega) hdim with
    ⟨b, hb⟩ | ⟨β, γ, -, hroot, b, hb⟩
  · have hreg := regular_coordinateQuadPlus n k (by omega)
    obtain ⟨e⟩ := key _ ((plusBasisIsometry b hb).trans (coordinatePlusIsometry n k)) hreg.1
      hreg.2 (commutator_coordinateQuadPlus n k (by omega))
    exact ⟨.POmegaPlus, _, inferInstance, Or.inl rfl, ⟨Nat.prime_two, hg, hn⟩,
      Or.inl ⟨by decide, ⟨Nat.prime_two, hg, hn⟩, k, inferInstance, inferInstance, hk,
        ⟨(coordinatePlusWitnessEquiv k (MulEquiv.refl _)).symm⟩⟩, ⟨e⟩⟩
  · have hreg := regular_coordinateQuadMinus n k β γ hn hroot
    obtain ⟨e⟩ := key _ ((minusBasisIsometry b hb).trans
      (coordinateMinusIsometry n k (by omega) β γ)) hreg.1 hreg.2
      (commutator_coordinateQuadMinus n k β γ hn hroot)
    exact ⟨.POmegaMinus, _, inferInstance, Or.inr rfl, ⟨Nat.prime_two, hg, hn⟩,
      Or.inl ⟨by decide, ⟨Nat.prime_two, hg, hn⟩, k, inferInstance, inferInstance, hk, β, γ,
        hroot, ⟨(coordinateMinusWitnessEquiv k (by omega) β γ (MulEquiv.refl _)).symm⟩⟩, ⟨e⟩⟩

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem even_omega_field_evenTCConc (hO : LieOrderFormulasInput) (τ : StatedLieTag)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) (M : Subgroup (fixedSubgroup α)) (hM : IsPComponent 2 M) :
    EvenTCConc τ n f M := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  have hd : 1 ≤ 2 * n := by omega
  obtain ⟨-, -, hsimple, heven, ext, -, -, hinj, hinn, hNC, hnormal, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α hα hα2 S hS hSα hσ1
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  set N := (extKappa Q ext).range with hNdef
  set Y := OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {α}
    with hYdef
  have hNY : N ≤ Y := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hinn hx, (Subgroup.mem_inf.mp (hNC hx)).2⟩
  have hYE : Y ≤ matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} :=
    inf_le_inf_right _ (matrixProjective_inner_le_image Q)
  obtain ⟨NY, hNYdef⟩ : ∃ NY : Subgroup Y, NY = N.subgroupOf Y := ⟨_, rfl⟩
  have hNYn : NY.Normal := ⟨fun x hx y => by
    rw [hNYdef, Subgroup.mem_subgroupOf] at hx ⊢
    have hn' := (hnormal.conj_mem ⟨x, hNC hx⟩ hx ⟨y, hYE y.2⟩)
    exact hn'⟩
  have eNY : NY ≃* N := (MulEquiv.subgroupCongr hNYdef).trans (Subgroup.subgroupOfEquivOfLe hNY)
  have eJ : ↥(pairDescentDerived hS) ≃* N := MonoidHom.ofInjective hinj
  have : IsSimpleGroup ↥(pairDescentDerived hS) := hsimple
  have hNYs : IsSimpleGroup NY := (eNY.trans eJ.symm).isSimpleGroup
  have hNY2 : Even (Nat.card NY) := by
    rw [Nat.card_congr (eNY.trans eJ.symm).toEquiv]
    exact heven
  have hα2' : α * α = 1 := by
    have h2 := pow_orderOf_eq_one α
    rw [hα2] at h2
    rw [← pow_two]
    exact h2
  have hCY : ∀ y : Y, (∀ x ∈ NY, y * x = x * y) → y = 1 := by
    intro y hy
    have hyN : (y : MulAut (matrixProjectiveDerived Q)) ∈
        matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} ⊓
          Subgroup.centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) := by
      refine Subgroup.mem_inf.mpr ⟨hYE y.2, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
      have h1 := hy ⟨n, hNY hn⟩ (by rw [hNYdef]; exact hn)
      exact (congrArg Subtype.val h1).symm
    rw [hcent, Subgroup.mem_zpowers_iff] at hyN
    obtain ⟨i, hi⟩ := hyN
    apply Subtype.ext
    rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [← two_mul, _root_.zpow_mul, zpow_two, hα2', _root_.one_zpow] at hi
      exact hi.symm
    · exfalso
      rw [_root_.zpow_add, _root_.zpow_mul, zpow_two, hα2', _root_.one_zpow, one_mul,
        zpow_one] at hi
      exact hout (hi ▸ (Subgroup.mem_inf.mp y.2).1)
  refine EvenTCConc.of_mulEquiv (fixedInnerEquiv hcj α) (fun M' hM' => ?_) hM
  have hM'eq := eq_of_isPComponent_of_normal_simple hNYn hNYs hNY2 hCY hM'
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
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨τ', Y', _, hτ, hadm, hlie, ⟨eY⟩⟩ :=
    exists_lieModel_derivedOrthogonal_typed hk2 hk hn (pairDescentForm hS) hQ₀ hdim
  have hne : τ' ≠ .PSU := by rcases hτ with rfl | rfl <;> decide
  have : IsSimpleGroup Y' := eY.symm.isSimpleGroup
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hM'
    ((MulEquiv.subgroupCongr hM'eq).trans ((eNY.trans eJ.symm).trans eY))
  exact EvenTCConc.of_model_ne hO hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hlie) hne

theorem even_omega_outer_fixed_cases_tc (hO : LieOrderFormulasInput) (τ : StatedLieTag)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    IsCharacteristicP 2 (fixedSubgroup α) ∨
      ∀ M : Subgroup (fixedSubgroup α), IsPComponent 2 M → EvenTCConc τ n f M := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  have hαα : α * α = 1 := by
    have h2 := pow_orderOf_eq_one α
    rw [hα] at h2
    rw [← pow_two]
    exact h2
  obtain ⟨β, hβ⟩ := hconj α hαα
  have hc : MulAut.congr β⁻¹ α = β⁻¹ * α * β := MulEquiv.ext fun _ => rfl
  have hγ2 : orderOf (β⁻¹ * α * β) = 2 := by
    rw [← hc]
    exact (orderOf_injective (MulAut.congr β⁻¹).toMonoidHom (MulAut.congr β⁻¹).injective
      α).trans hα
  have hγo : β⁻¹ * α * β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [← hc, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  let eβ : fixedSubgroup α ≃* fixedSubgroup (β⁻¹ * α * β) :=
    (fixedSubgroupCongrEquiv β⁻¹ α).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))
  obtain ⟨S, hS, hSγ⟩ := exists_unit_rep hβ
  by_cases hσ : S.val.right = 1
  · obtain ⟨-, -, -, -, F, hF, hker, -, -⟩ :=
      evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
    have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
        F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        β⁻¹ * α * β := hs.trans hSγ
    have hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2 := by
      rw [hs']
      exact hγ2
    have hso : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) ∉
        OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
      rw [hs']
      exact hγo
    let es := eβ.trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hs'.symm))
    rcases even_omega_linear_fixed_cases hf hK hn hQ hT hE s hs2 hso with hch | ⟨⟨Φ⟩⟩
    · exact Or.inl (LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv es.symm hch)
    · have : Finite (GL (Fin (n - 1) ⊕ Fin (n - 1)) K) :=
        Finite.of_injective Units.val Units.val_injective
      refine Or.inr (fun M hM => EvenTCConc.of_mulEquiv (es.trans Φ)
        (fun M' hM' => evenTCConc_statedSp hO (r := n - 1) hf hK (by omega) M' hM') hM)
  · refine Or.inr (fun M hM => ?_)
    exact EvenTCConc.of_mulEquiv eβ (fun M' hM' =>
      even_omega_field_evenTCConc hO τ hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ M' hM') hM

theorem a2l_evenTCOuter_of_orthogonal (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) : EvenTCOuter t := by
  intro J _ n f hadm hm α hα hαo P hP
  have hC : StatedClassicalModel J t n 2 f := EvenOrthSelector.statedModel_of_lieModel
    (by rcases ht with rfl | rfl <;> decide) hm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 4 ≤ n := by rcases ht with rfl | rfl <;> exact hadm.2.2
  obtain ⟨K, _, _, Q, hK, hQ, hT, hE, hconj, ⟨e⟩⟩ :=
    EvenOrthSelector.exists_coordinate_witness ht hC
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβo : MulAut.congr e α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  let eα := fixedSubgroupCongrEquiv e α
  rcases even_omega_outer_fixed_cases_tc hO t hf hK hn hQ hT hE hconj _ hβ hβo with hch | hall
  · exact absurd hP (not_isPComponent_of_isCharacteristicP
      (LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv eα.symm hch) P)
  · exact EvenTCConc.of_mulEquiv eα hall hP

end Omega

end A2lPumpEvenTCOmega

theorem a2l_evenTCOuter_POmegaPlus (hO : LieOrderFormulasInput) : EvenTCOuter .POmegaPlus :=
  A2lPumpEvenTCOmega.a2l_evenTCOuter_of_orthogonal hO (Or.inl rfl)

theorem a2l_evenTCOuter_POmegaMinus (hO : LieOrderFormulasInput) : EvenTCOuter .POmegaMinus :=
  A2lPumpEvenTCOmega.a2l_evenTCOuter_of_orthogonal hO (Or.inr rfl)

end CFSG.OddStandard.SmallF3.HypA2Leaves
