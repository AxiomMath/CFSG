module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSUPSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalOmega

public noncomputable section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv fixedInnerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical

@[expose] def OmegaPComponents (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, IsPComponent 2 P → ∃ (t : StatedLieTag) (n f : ℕ),
    (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ StatedLieAdmissible t n 2 f ∧ LieModel P t n 2 f

theorem omegaPComponents_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OmegaPComponents Y) : OmegaPComponents X := by
  intro P hP
  obtain ⟨t, n, f, ht, hadm, hm⟩ :=
    h _ (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP)
  exact ⟨t, n, f, ht, hadm,
    LieType.CurtisTits.lieModel_of_mulEquiv (P.equivMapOfInjective e.toMonoidHom e.injective).symm
      hm⟩

@[expose] def OmegaOuterFixed (X : Type) [Group X] (g : ℕ) : Prop :=
  SpFixedOrNoPComponent X g ∨ OmegaPComponents X

theorem omegaOuterFixed_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {g : ℕ}
    (h : OmegaOuterFixed Y g) : OmegaOuterFixed X g := by
  rcases h with h | h
  · exact Or.inl (spFixedOrNoPComponent_of_mulEquiv e h)
  · exact Or.inr (omegaPComponents_of_mulEquiv e h)

theorem isSimpleGroup_of_lieModel_POmega {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (h : LieModel X t n p f) : IsSimpleGroup X := by
  have hst : StatedClassicalModel X t n p f := by
    rcases h with ⟨-, h⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact h
    · rcases ht with rfl | rfl <;> simp [chevalleyExceptionalTags] at ht'
    · rcases ht with rfl | rfl <;> simp [reeTitsTags] at ht'
    · rcases ht with rfl | rfl <;> cases ht'
  rcases ht with rfl | rfl
  · exact (isSimpleGroup_of_statedClassicalModel_POmegaPlus X n p f hst).2
  · exact (isSimpleGroup_of_statedClassicalModel_POmegaMinus X n p f hst).2

section DerivedOrthogonal

open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf

theorem exists_lieModel_derivedOrthogonal_tag {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {g n : ℕ} (hg : 1 ≤ g) (hk : Nat.card k = 2 ^ g)
    (hn : 4 ≤ n) (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : finrank k W = 2 * n) :
    ∃ (τ' : StatedLieTag) (Y : Type) (_ : Group Y), (τ' = .POmegaPlus ∨ τ' = .POmegaMinus) ∧
      StatedLieAdmissible τ' n 2 g ∧
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

end DerivedOrthogonal

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem omega_field_pComponents (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) : OmegaPComponents (fixedSubgroup α) := by
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
  refine omegaPComponents_of_mulEquiv (fixedInnerEquiv hcj α) fun M' hM' => ?_
  have hM'eq := CatLeafProof.eq_of_isPComponent_of_normal_simple hNYn hNYs hNY2 hCY hM'
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
  obtain ⟨τ', Y', _, hτ', hadm, hlie, ⟨eY⟩⟩ :=
    exists_lieModel_derivedOrthogonal_tag hk2 hk hn (pairDescentForm hS) hQ₀ hdim
  exact ⟨τ', n, f / 2, hτ', hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((MulEquiv.subgroupCongr hM'eq).trans ((eNY.trans eJ.symm).trans eY)).symm hlie⟩

theorem omega_outer_fixed_exact (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    OmegaOuterFixed (fixedSubgroup α) f := by
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
  refine omegaOuterFixed_of_mulEquiv ((fixedSubgroupCongrEquiv β⁻¹ α).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))) ?_
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
    refine omegaOuterFixed_of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hs'.symm)) ?_
    rcases F4Pilot.omega_linear_fixed hf hK hn hQ hT hE s hs2 hso with hΦ | hch
    · exact Or.inl (Or.inl ⟨K, inferInstance, inferInstance, n - 1, hK, by omega, hΦ⟩)
    · exact Or.inl (Or.inr (CatLeafProof.not_isPComponent_of_isCharacteristicP hch))
  · exact Or.inr (omega_field_pComponents hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ)

omit [Finite K] in
theorem omega_family_fixed_exact {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {J : Type} [Group J] {e : ℕ} (hadm : StatedLieAdmissible t n 2 e) (hm : LieModel J t n 2 e)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    OmegaOuterFixed (fixedSubgroup α) e := by
  have hC : StatedClassicalModel J t n 2 e := EvenOrthSelector.statedModel_of_lieModel
    (by rcases ht with rfl | rfl <;> decide) hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 4 ≤ n := by rcases ht with rfl | rfl <;> exact hadm.2.2
  obtain ⟨K, _, _, Q, hK, hQ, hT, hE, hconj, ⟨eJ⟩⟩ :=
    EvenOrthSelector.exists_coordinate_witness ht hC
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβo : MulAut.congr eJ α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact omegaOuterFixed_of_mulEquiv (fixedSubgroupCongrEquiv eJ α)
    (omega_outer_fixed_exact hf hK hn hQ hT hE hconj _ hβ hβo)


theorem false_of_omegaOuterFixed {m : ℕ} (hdet : SLmEvenTypeDetAt m) {X : Type} [Group X]
    [Finite X] {g : ℕ} (h : OmegaOuterFixed X g) {D : Subgroup X} (hD : IsComponent D)
    {f : ℕ} (hm : 3 ≤ m) (hDm : LieModel (D ⧸ center D) .PSL m 2 f) : False := by
  rcases h with h | h
  · exact false_of_spFixedOrNoPComponent hdet h hD hm hDm
  · obtain ⟨t, n, f', ht, hadm, hmD⟩ :=
      h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)
    obtain ⟨rfl, -, -⟩ := typeDet_of_simple hdet hD.1 (isSimpleGroup_of_lieModel_POmega ht hmD)
      hDm hadm hmD
    rcases ht with h | h <;> exact absurd h (by decide)

omit [Finite K] in
theorem catSLmEvenOuterFamilyAt_POmegaPlus {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) :
    CatSLmEvenOuterFamilyAt .POmegaPlus m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  exact false_of_omegaOuterFixed hdet (omega_family_fixed_exact (Or.inl rfl) hadm hmS σ hσ hout)
    hD hm hDm |>.elim

omit [Finite K] in
theorem catSLmEvenOuterFamilyAt_POmegaMinus {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) :
    CatSLmEvenOuterFamilyAt .POmegaMinus m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm _
  exact false_of_omegaOuterFixed hdet (omega_family_fixed_exact (Or.inr rfl) hadm hmS σ hσ hout)
    hD hm hDm |>.elim

end CFSG.SeitzReduction.LinearPilot
