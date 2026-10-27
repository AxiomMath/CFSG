module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOmegaLinear
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical

theorem eq_of_isPComponent_of_normal_simple {A : Type*} [Group A] [Finite A] {N : Subgroup A}
    (hNn : N.Normal) (hNs : IsSimpleGroup N) (hN2 : Even (Nat.card N))
    (hC : ∀ a : A, (∀ x ∈ N, a * x = x * a) → a = 1) {P : Subgroup A}
    (hP : IsPComponent 2 P) : P = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 A = ⊥ := by
    have hOn : (pPrimeCore 2 A).Normal := pPrimeCore_normal
    have hdis : Disjoint (pPrimeCore 2 A) N := by
      have hsn : ((pPrimeCore 2 A).subgroupOf N).Normal := hOn.subgroupOf N
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hNs _ hsn with h | h
      · exact Subgroup.subgroupOf_eq_bot.mp h
      · exfalso
        have hle : N ≤ pPrimeCore 2 A := Subgroup.subgroupOf_eq_top.mp h
        have hdvd : 2 ∣ Nat.card (pPrimeCore 2 A) :=
          (even_iff_two_dvd.mp hN2).trans (Subgroup.card_dvd_of_le hle)
        exact absurd (Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card hdvd) (by norm_num)
    rw [eq_bot_iff]
    intro o ho
    exact hC o fun x hx =>
      Subgroup.commute_of_normal_of_disjoint _ _ hOn hNn hdis o x ho hx
  obtain ⟨hs, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 P).1 hP
  have hcore : pPrimeCore 2 P = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hs
    rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ P.subtype_injective] at h1
    exact h1
  have hPc : IsComponent P := ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)).1 hq, hs⟩
  have hnt := GrSLit.nontrivial_of_isPComponent hP
  rcases LocalCores.component_normal_subgroup hPc hNn with hle | hcomm
  · have hsub : (P.subgroupOf N).IsSubnormal := Subgroup.IsSubnormal.subgroupOf hs
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hNs hsub with h | h
    · exfalso
      have hP0 : P = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : (⟨x, hle hx⟩ : N) ∈ P.subgroupOf N := hx
        rw [h, Subgroup.mem_bot] at hx'
        exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
      rw [hP0] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    · refine le_antisymm hle fun x hx => ?_
      have hx' : (⟨x, hx⟩ : N) ∈ P.subgroupOf N := h ▸ Subgroup.mem_top _
      exact hx'
  · exfalso
    have hP0 : P = ⊥ := by
      rw [eq_bot_iff]
      intro p hp
      have hpC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hp
      rw [Subgroup.mem_bot]
      exact hC p fun x hx => (Subgroup.mem_centralizer_iff.mp hpC x hx).symm
    rw [hP0] at hnt
    exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt

theorem exists_lieModel_derivedOrthogonal {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {g n : ℕ} (hg : 1 ≤ g) (hk : Nat.card k = 2 ^ g)
    (hn : 4 ≤ n) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : finrank k W = 2 * n) :
    ∃ (τ' : StatedLieTag) (Y : Type) (_ : Group Y), StatedLieAdmissible τ' n 2 g ∧
      Blueprint.LieModel Y τ' n 2 g ∧
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
    exact ⟨.POmegaPlus, _, inferInstance, ⟨Nat.prime_two, hg, hn⟩,
      Or.inl ⟨by decide, ⟨Nat.prime_two, hg, hn⟩, k, inferInstance, inferInstance, hk,
        ⟨(coordinatePlusWitnessEquiv k (MulEquiv.refl _)).symm⟩⟩, ⟨e⟩⟩
  · have hreg := regular_coordinateQuadMinus n k β γ hn hroot
    obtain ⟨e⟩ := key _ ((minusBasisIsometry b hb).trans
      (coordinateMinusIsometry n k (by omega) β γ)) hreg.1 hreg.2
      (commutator_coordinateQuadMinus n k β γ hn hroot)
    exact ⟨.POmegaMinus, _, inferInstance, ⟨Nat.prime_two, hg, hn⟩,
      Or.inl ⟨by decide, ⟨Nat.prime_two, hg, hn⟩, k, inferInstance, inferInstance, hk, β, γ,
        hroot, ⟨(coordinateMinusWitnessEquiv k (by omega) β γ (MulEquiv.refl _)).symm⟩⟩, ⟨e⟩⟩

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem even_omega_field_actual (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) (M : Subgroup (fixedSubgroup α)) (hM : IsPComponent 2 M) :
    EvenLieConclusion M ∧ IsSimpleGroup ↥M := by
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
  have hcore : ∀ M' : Subgroup Y, IsPComponent 2 M' → EvenLieConclusion M' ∧ IsSimpleGroup ↥M' := by
    intro M' hM'
    have hM'eq := eq_of_isPComponent_of_normal_simple hNYn hNYs hNY2 hCY hM'
    have hM'simple : IsSimpleGroup ↥M' := (MulEquiv.subgroupCongr hM'eq).isSimpleGroup
    obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ :=
      evenOrthogonalRealization_of_regular hf hK hd Q hQ hT hE
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
    obtain ⟨τ', Y', _, hadm, hlie, ⟨eY⟩⟩ :=
      exists_lieModel_derivedOrthogonal hk2 hk hn (pairDescentForm hS) hQ₀ hdim
    have : IsSimpleGroup Y' := eY.symm.isSimpleGroup
    obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hM'
      ((MulEquiv.subgroupCongr hM'eq).trans ((eNY.trans eJ.symm).trans eY))
    exact ⟨Or.inl ⟨τ', n, f / 2, hadm,
      LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hlie⟩, hM'simple⟩
  have hPtrans := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
    (fixedInnerEquiv hcj α) hM
  refine ⟨evenLieConclusion_of_mulEquiv (fixedInnerEquiv hcj α)
    (fun M' hM' => (hcore M' hM').1) hM, ?_⟩
  have hMsimp := (hcore _ hPtrans).2
  exact (M.equivMapOfInjective (fixedInnerEquiv hcj α).toMonoidHom
    (fixedInnerEquiv hcj α).injective).isSimpleGroup

theorem even_omega_field_evenLieConclusion (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) (M : Subgroup (fixedSubgroup α)) (hM : IsPComponent 2 M) :
    EvenLieConclusion M :=
  (even_omega_field_actual hf hK hn hQ hT hE hα hα2 hout hS hSα hσ1 M hM).1

theorem even_omega_outer_actual_cases (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    IsCharacteristicP 2 (fixedSubgroup α) ∨ Nonempty (fixedSubgroup α ≃* StatedSp (n - 1) K) ∨
      ((∃ σ : K ≃+* K, σ ≠ 1) ∧
        ∀ M : Subgroup (fixedSubgroup α), IsPComponent 2 M →
          IsSimpleGroup ↥M ∧ EvenLieConclusion M) := by
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
    · exact Or.inr (Or.inl ⟨es.trans Φ⟩)
  · refine Or.inr (Or.inr ⟨⟨S.val.right, hσ⟩, fun M hM => ?_⟩)
    have hscale : ∀ M' : Subgroup (fixedSubgroup (β⁻¹ * α * β)), IsPComponent 2 M' →
        IsSimpleGroup ↥M' := fun M' hM' =>
      (even_omega_field_actual hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ M' hM').2
    have hM' : IsPComponent 2 (M.map eβ.toMonoidHom) :=
      LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 eβ hM
    have hsimple : IsSimpleGroup ↥(M.map eβ.toMonoidHom) := hscale _ hM'
    exact ⟨(M.equivMapOfInjective eβ.toMonoidHom eβ.injective).isSimpleGroup,
      evenLieConclusion_of_mulEquiv eβ (fun M' hM' =>
        (even_omega_field_actual hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ M' hM').1) hM⟩

theorem even_omega_outer_fixed_cases (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    IsCharacteristicP 2 (fixedSubgroup α) ∨ Nonempty (fixedSubgroup α ≃* StatedSp (n - 1) K) ∨
      ((∃ σ : K ≃+* K, σ ≠ 1) ∧
        ∀ M : Subgroup (fixedSubgroup α), IsPComponent 2 M → EvenLieConclusion M) := by
  rcases even_omega_outer_actual_cases hf hK hn hQ hT hE hconj α hα hout with
    hch | ⟨⟨Φ⟩⟩ | ⟨hσ, h⟩
  · exact Or.inl hch
  · exact Or.inr (Or.inl ⟨Φ⟩)
  · exact Or.inr (Or.inr ⟨hσ, fun M hM => (h M hM).2⟩)



theorem even_omega_outer_evenLieConclusion (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q))
    (M : Subgroup (fixedSubgroup α)) (hM : IsPComponent 2 M) : EvenLieConclusion M := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  have : Finite (GL (Fin (n - 1) ⊕ Fin (n - 1)) K) :=
    Finite.of_injective Units.val Units.val_injective
  rcases even_omega_outer_fixed_cases hf hK hn hQ hT hE hconj α hα hout with
    hch | ⟨⟨Φ⟩⟩ | ⟨-, h⟩
  · exact absurd hM (not_isPComponent_of_isCharacteristicP hch M)
  · exact evenLieConclusion_of_mulEquiv Φ
      (fun M' hM' => evenLieConclusion_statedSp hf hK (by omega) M' hM') hM
  · exact h M hM

theorem evenOrthogonal_outer_fixed_cases {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {J : Type} [Group J]
    (hadm : StatedLieAdmissible t n 2 f) (hm : Blueprint.LieModel J t n 2 f) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      (IsCharacteristicP 2 (fixedSubgroup α) ∨ Nonempty (fixedSubgroup α ≃* StatedSp (n - 1) K) ∨
        ((∃ σ : K ≃+* K, σ ≠ 1) ∧
          ∀ M : Subgroup (fixedSubgroup α), IsPComponent 2 M → EvenLieConclusion M)) := by
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
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  rcases even_omega_outer_fixed_cases hf hK hn hQ hT hE hconj _ hβ hβo with
    hch | ⟨⟨Φ⟩⟩ | ⟨hσ, h⟩
  · exact Or.inl (LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv eα.symm hch)
  · exact Or.inr (Or.inl ⟨eα.trans Φ⟩)
  · exact Or.inr (Or.inr ⟨hσ, fun M hM => evenLieConclusion_of_mulEquiv eα h hM⟩)

theorem evenOuterFamilyInput_of_orthogonal {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) : EvenOuterFamilyInput t := by
  intro J _ n f hadm hm α hα hαo P hP
  change EvenLieConclusion P
  have hC : StatedClassicalModel J t n 2 f := EvenOrthSelector.statedModel_of_lieModel
    (by rcases ht with rfl | rfl <;> decide) hm
  obtain ⟨K₀, _, _, Q₀, -, -, -, -, -, ⟨e⟩⟩ := EvenOrthSelector.exists_coordinate_witness ht hC
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  have hn : 4 ≤ n := by rcases ht with rfl | rfl <;> exact hadm.2.2
  obtain ⟨K, _, _, hK, hcases⟩ := evenOrthogonal_outer_fixed_cases ht hadm hm α hα hαo
  have : Finite (GL (Fin (n - 1) ⊕ Fin (n - 1)) K) :=
    Finite.of_injective Units.val Units.val_injective
  rcases hcases with hch | ⟨⟨Φ⟩⟩ | ⟨-, h⟩
  · exact absurd hP (not_isPComponent_of_isCharacteristicP hch P)
  · exact evenLieConclusion_of_mulEquiv Φ
      (fun M hM => evenLieConclusion_statedSp hadm.2.1 hK (by omega) M hM) hP
  · exact h P hP

theorem evenOuterFamilyInput_POmegaPlus : EvenOuterFamilyInput .POmegaPlus :=
  evenOuterFamilyInput_of_orthogonal (Or.inl rfl)

theorem evenOuterFamilyInput_POmegaMinus : EvenOuterFamilyInput .POmegaMinus :=
  evenOuterFamilyInput_of_orthogonal (Or.inr rfl)

end CFSG.ComponentClassification.CatLeafProof
