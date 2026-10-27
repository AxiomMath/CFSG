module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenOuter

public noncomputable section

namespace CFSG.SeitzReduction.F4Pilot

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

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

omit [Finite K] in
theorem omega_symmetry_fixed (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin (2 * n) → K} (hv : Q v = 1)
    (hout : symmetryAut Q v ∉ inner (matrixProjectiveDerived Q)) :
    Nonempty (fixedSubgroup (symmetryAut Q v) ≃* StatedSp (n - 1) K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ two_ne_zero)
  exact CFSG.ComponentClassification.CatLeafProof.even_omega_symmetry_fixed_equiv hf hK hn hQ hT hE
    hv hout

theorem omega_linear_fixed (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (s : matrixIsometries Q)
    (hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2)
    (hout : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) ∉
      inner (matrixProjectiveDerived Q)) :
    Nonempty (fixedSubgroup (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) ≃*
        StatedSp (n - 1) K) ∨
      IsCharacteristicP 2
        (fixedSubgroup (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hss : s * s = 1 := by
    apply isometryKappa_injective hQ hT hE
    rw [map_mul, map_one]
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = 1
    have h2 := pow_orderOf_eq_one
      (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))
    rw [hs2] at h2
    rw [← pow_two]
    exact h2
  have hs1 : (s : GL (Fin (2 * n)) K) ≠ 1 := by
    intro h
    have h1 : s = 1 := Subtype.ext h
    rw [h1, map_one, map_one, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  by_cases hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank
  · right
    have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
      hQ hT hE
    exact LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv (fixedInnerEquiv hcj _).symm
      (CatLeafProof.isCharacteristicP_inner_centralizer_of_two_le_rank hQ hT hE s hs2 hr)
  · left
    obtain ⟨v, hv, hsv⟩ := exists_symmetry_of_rank_le_one hQ s.2
      (congrArg Subtype.val hss) hs1 (by omega)
    have hincl : s = symmetryIsometry Q v := Subtype.ext hsv
    subst hincl
    exact omega_symmetry_fixed hf hK hn hQ hT hE hv hout

theorem notSp6Components_omega_field (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) : NotSp6Components (fixedSubgroup α) := by
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
  refine notSp6Components_of_mulEquiv (fixedInnerEquiv hcj α) fun M' hM' => ?_
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
  obtain ⟨τ', Y', _, hadm, hlie, ⟨eY⟩⟩ :=
    CatLeafProof.exists_lieModel_derivedOrthogonal hk2 hk hn (pairDescentForm hS) hQ₀ hdim
  exact ⟨τ', n, f / 2, classicalOrSuzukiTag_of_admissible hadm (by omega), hadm,
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((MulEquiv.subgroupCongr hM'eq).trans ((eNY.trans eJ.symm).trans eY)).symm hlie,
    fun h => by omega⟩

theorem omega_outer_fixed (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    SpFixedOrNotSp6 (fixedSubgroup α) (fun r g => g = f ∧ r + 1 = n) := by
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
  refine spFixedOrNotSp6_of_mulEquiv ((fixedSubgroupCongrEquiv β⁻¹ α).trans
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
    refine spFixedOrNotSp6_of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hs'.symm)) ?_
    rcases omega_linear_fixed hf hK hn hQ hT hE s hs2 hso with hΦ | hch
    · exact Or.inl ⟨K, inferInstance, inferInstance, n - 1, f, hK, by omega,
        ⟨rfl, by omega⟩, hΦ⟩
    · exact Or.inr (notSp6Components_of_isCharacteristicP hch)
  · exact Or.inr (notSp6Components_omega_field hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ)

omit [Finite K] in
theorem omega_family_fixed {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {J : Type} [Group J] {e : ℕ} (hadm : StatedLieAdmissible t n 2 e) (hm : LieModel J t n 2 e)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNotSp6 (fixedSubgroup α) (fun r g => g = e ∧ r + 1 = n) := by
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
  exact spFixedOrNotSp6_of_mulEquiv (fixedSubgroupCongrEquiv eJ α)
    (omega_outer_fixed hf hK hn hQ hT hE hconj _ hβ hβo)

theorem catSp6EvenOuterFamily_POmegaPlus (hdet : Sp6EvenTypeDet) :
    CatSp6EvenOuterFamily .POmegaPlus := by
  intro S _ _ _ _ n e hadm hm σ hσ hout f D hD hD6 _
  obtain ⟨⟨rfl, hn⟩, hfix⟩ :=
    sp6_of_spFixedOrNotSp6 hdet (omega_family_fixed (Or.inl rfl) hadm hm σ hσ hout) hD hD6
  subst hn
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))), hfix⟩

theorem catSp6EvenOuterFamily_POmegaMinus (hdet : Sp6EvenTypeDet) :
    CatSp6EvenOuterFamily .POmegaMinus := by
  intro S _ _ _ _ n e hadm hm σ hσ hout f D hD hD6 _
  obtain ⟨⟨rfl, hn⟩, hfix⟩ :=
    sp6_of_spFixedOrNotSp6 hdet (omega_family_fixed (Or.inr rfl) hadm hm σ hσ hout) hD hD6
  subst hn
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm))))), hfix⟩

end CFSG.SeitzReduction.F4Pilot
