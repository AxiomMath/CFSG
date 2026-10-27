module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatPlusType
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public noncomputable section

namespace CFSG.SeitzReduction.OmegaPilot

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
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (SpFixedOrNoPComponent spFixedOrNoPComponent_of_mulEquiv
  exists_lieModel_derivedOrthogonal_tag)
open CFSG.GroupTheory.WeirSylow (IsPlusType)

@[expose] def OmegaFieldComponents (X : Type) [Group X] (n e : ℕ) : Prop :=
  2 * (e / 2) = e ∧ ∀ P : Subgroup X, IsPComponent 2 P → ∃ t : StatedLieTag,
    (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ StatedLieAdmissible t n 2 (e / 2) ∧
      LieModel P t n 2 (e / 2)

theorem omegaFieldComponents_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n e' : ℕ} (h : OmegaFieldComponents Y n e') : OmegaFieldComponents X n e' := by
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨t, ht, hadm, hm⟩ :=
    h.2 _ (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP)
  exact ⟨t, ht, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    (P.equivMapOfInjective e.toMonoidHom e.injective).symm hm⟩

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem omega_field_pComponents_exact (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) : OmegaFieldComponents (fixedSubgroup α) n f ∧ IsPlusType Q := by
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
  have hplus : IsPlusType Q := isPlusType_of_semilinear_involution hf hK (by omega : 1 ≤ n)
    (by rw [Module.finrank_fin_fun]) hσσ hσ1 hQ hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨τ', Y', _, hτ', hadm, hlie, ⟨eY⟩⟩ :=
    exists_lieModel_derivedOrthogonal_tag hk2 hk hn (pairDescentForm hS) hQ₀ hdim
  refine ⟨⟨by obtain ⟨m, hm⟩ := hfeven; omega, fun M' hM' => ?_⟩, hplus⟩
  refine omegaFieldComponents_of_mulEquiv (fixedInnerEquiv hcj α) ?_ |>.2 M' hM'
  refine ⟨by obtain ⟨m, hm⟩ := hfeven; omega, fun M'' hM'' => ?_⟩
  have hM'eq := CatLeafProof.eq_of_isPComponent_of_normal_simple hNYn hNYs hNY2 hCY hM''
  exact ⟨τ', hτ', hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((MulEquiv.subgroupCongr hM'eq).trans ((eNY.trans eJ.symm).trans eY)).symm hlie⟩

omit [Finite K] in
theorem outerFixedExact_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {g : ℕ}
    {P : Prop} (h : SpFixedOrNoPComponent Y g ∨ (OmegaFieldComponents Y n g ∧ P)) :
    SpFixedOrNoPComponent X g ∨ (OmegaFieldComponents X n g ∧ P) := by
  rcases h with h | ⟨h, hP⟩
  · exact Or.inl (spFixedOrNoPComponent_of_mulEquiv e h)
  · exact Or.inr ⟨omegaFieldComponents_of_mulEquiv e h, hP⟩

theorem omega_outer_fixed_exact' (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    SpFixedOrNoPComponent (fixedSubgroup α) f ∨
      (OmegaFieldComponents (fixedSubgroup α) n f ∧ IsPlusType Q) := by
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
  refine outerFixedExact_of_mulEquiv ((fixedSubgroupCongrEquiv β⁻¹ α).trans
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
    refine outerFixedExact_of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hs'.symm)) ?_
    rcases F4Pilot.omega_linear_fixed hf hK hn hQ hT hE s hs2 hso with hΦ | hch
    · exact Or.inl (Or.inl ⟨K, inferInstance, inferInstance, n - 1, hK, by omega, hΦ⟩)
    · exact Or.inl (Or.inr (CatLeafProof.not_isPComponent_of_isCharacteristicP hch))
  · exact Or.inr (omega_field_pComponents_exact hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ)

omit [Finite K] in
theorem not_isPlusType_coordinateQuadMinus [Finite K] (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ IsPlusType (coordinateQuadMinus n K (by omega) b c) := fun h =>
  CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega : 1 ≤ n) hirr
    (h.of_isometryEquiv (coordinateMinusIsometry n K (by omega) b c).symm)

theorem exists_coordinate_witness_minus {W : Type} [Group W] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel W .POmegaMinus n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      Nat.card K = 2 ^ f ∧
      (∀ α : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)),
        α * α = 1 → ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage (coordinateQuadMinus n K (by omega) b c)) ∧
      Nonempty (W ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) := by
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image W .POmegaMinus
    (Or.inr rfl) n f h).1
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, b, c, hirr, hK, hI (by omega) K hK b c hirr e,
    ⟨coordinateMinusWitnessEquiv K (by omega) b c e⟩⟩

omit [Finite K] in
theorem omega_minus_fixed_exact {J : Type} [Group J] {e : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 2 e) (hm : LieModel J .POmegaMinus n 2 e)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNoPComponent (fixedSubgroup α) e := by
  have hC : StatedClassicalModel J .POmegaMinus n 2 e :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨K, _, _, b, c, hirr, hK, hconj, ⟨eJ⟩⟩ := exists_coordinate_witness_minus hn hC
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβo : MulAut.congr eJ α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived _) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  rcases omega_outer_fixed_exact' hf hK hn hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr) hconj _ hβ hβo with h | ⟨-, hplus⟩
  · exact spFixedOrNoPComponent_of_mulEquiv (fixedSubgroupCongrEquiv eJ α) h
  · exact (not_isPlusType_coordinateQuadMinus hn hirr hplus).elim

omit [Finite K] in
theorem omega_plus_fixed_exact {J : Type} [Group J] {e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 2 e) (hm : LieModel J .POmegaPlus n 2 e)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNoPComponent (fixedSubgroup α) e ∨ OmegaFieldComponents (fixedSubgroup α) n e := by
  have hC : StatedClassicalModel J .POmegaPlus n 2 e :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨K, _, _, Q, hK, hQ, hT, hE, hconj, ⟨eJ⟩⟩ :=
    EvenOrthSelector.exists_coordinate_witness (Or.inl rfl) hC
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβo : MulAut.congr eJ α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  rcases omega_outer_fixed_exact' hf hK hn hQ hT hE hconj _ hβ hβo with h | ⟨h, -⟩
  · exact Or.inl (spFixedOrNoPComponent_of_mulEquiv (fixedSubgroupCongrEquiv eJ α) h)
  · exact Or.inr (omegaFieldComponents_of_mulEquiv (fixedSubgroupCongrEquiv eJ α) h)

omit [Finite K] in
theorem catOmegaEvenOuterFamilyAt_POmegaPlus {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .POmegaPlus m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout t f D ht hD hDm _
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases omega_plus_fixed_exact hadm hmS σ hσ hout with h | ⟨he, h⟩
  · exact (false_of_spFixedOrNoPComponent_omega hdet ht h hD hDm).elim
  · obtain ⟨t', ht', hadm', hmD⟩ := h D hDp
    obtain ⟨-, hnm, hef⟩ := omegaTypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_POmega ht' hmD) ht hDm hadm' hmD
    subst hnm
    rw [← hef, he]
    exact hmS

omit [Finite K] in
theorem catOmegaEvenOuterFamilyAt_POmegaMinus {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .POmegaMinus m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout t f D ht hD hDm _
  exact (false_of_spFixedOrNoPComponent_omega hdet ht
    (omega_minus_fixed_exact hadm hmS σ hσ hout) hD hDm).elim

end CFSG.SeitzReduction.OmegaPilot
