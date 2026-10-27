module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearDelta
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIUnitaryRigid
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents

public section

namespace CFSG.SeitzReduction

namespace UnitaryOuter

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag LinearFlag FourGroupEvenCanonical
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.RankTwoHypIIY (eq_one_or_eq_of_mem_zpowers)
open CFSG.ComponentClassification.UnbalancingLocal.EvenUnitaryComponents
  (conj_injective_primeFormP)
open CFSG.ComponentClassification.RankTwoHypIIUnitary (exists_fixed_gram
  centralizer_inf_le_zpowers nonempty_matrixIsometryGroup_mulEquiv_statedSp
  mem_centralizer_of_mem_centralizer_commutator)

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem canonical_case_fixed {C : GL (Fin n) K} {Cl : GL (Fin n) h.fixedField}
    (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C) {r : ℕ}
    (hn : 3 ≤ n) (hCr : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ n = 2 * r + 1)) :
    (n = 2 * r ∧ (Cl : Matrix (Fin n) (Fin n) h.fixedField) = blockSwapJ n r) ∨
      ((Cl : Matrix (Fin n) (Fin n) h.fixedField) = 1 ∧ n = 2 * r + 1) := by
  have hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Or.inr ⟨r, h1, h2⟩
    · exact Or.inl h1
  rcases canonical_case_of_map h hCl hcase with h1 | ⟨r', hr', hJ⟩
  · right
    refine ⟨h1, ?_⟩
    rcases hCr with ⟨h2, h3⟩ | ⟨-, h2⟩
    · exfalso
      have h4 : (C : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← hCl, h1, Matrix.map_one _ (map_zero _) (map_one _)]
      have h5 := congrFun (congrFun (h4.symm.trans h3) ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [blockSwapJ_apply_self (by omega), one_apply_eq] at h5
      exact one_ne_zero h5
    · exact h2
  · left
    rcases hCr with ⟨h2, -⟩ | ⟨h2, h3⟩
    · exact ⟨h2, by rw [hJ, show r' = r by omega]⟩
    · exfalso
      have h4 : (C : Matrix (Fin n) (Fin n) K) = 1 := h2
      have hJK : (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r' := by
        rw [← hCl, hJ]
        ext a b
        simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
        split_ifs <;> simp
      have h5 := congrFun (congrFun (h4.symm.trans hJK) ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [blockSwapJ_apply_self (by omega), one_apply_eq] at h5
      exact one_ne_zero h5

theorem involutionCriterion_primeFormFieldHom_of_perfect (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C) {r : ℕ}
    (hfr : 2 ≤ f ∨ 3 ≤ r)
    (hCr : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ n = 2 * r + 1))
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    InvolutionCriterion (primeFormFieldHom h hC σ) := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := h.finite
  have : CharP K 2 := h.charP
  have hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Or.inr ⟨r, h1, h2⟩
    · exact Or.inl h1
  have hodd : (C : Matrix (Fin n) (Fin n) K) = 1 → Odd n := by
    intro h1
    rcases hCr with ⟨h2, h3⟩ | ⟨-, h2⟩
    · exfalso
      have h4 := congrFun (congrFun (h1.symm.trans h3) ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [blockSwapJ_apply_self (by omega), one_apply_eq] at h4
      exact one_ne_zero h4
    · exact ⟨r, h2⟩
  obtain ⟨Cl, hCl⟩ := exists_fixed_gram h hcase
  obtain ⟨-, -, hinjU, hNinn, hNC, -, -, -, -, -, hord2, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC hcase Cl hCl σ hσ
  have hCN := centralizer_inf_le_zpowers h hn hq hC hcase hodd Cl hCl σ hσ
  obtain ⟨eSp⟩ := nonempty_matrixIsometryGroup_mulEquiv_statedSp
    (canonical_case_fixed h hCl hn hCr)
  have := LinearOuter.isPerfect_statedSp_of_card (K := h.fixedField) h.one_le h.card_fixedField hfr
  have eN : ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)).range ≃* StatedSp r h.fixedField :=
    (MonoidHom.ofInjective hinjU).symm.trans eSp
  have hperf : Group.IsPerfect ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
      (fixedIsometryHom h hCl)).range :=
    Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have h2 : primeFormFieldHom h hC σ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (primeFormFieldHom h hC σ)
    rwa [hord2] at this
  exact involutionCriterion_of_inner_perfect (conj_injective_primeFormP h hC hn) h2 hNinn hNC
    (Subgroup.isPerfect_iff.mp hperf) hCN

theorem involutionCriterion_primeFormFieldHom_five_two (hf : f = 1) {C : GL (Fin 5) K}
    (hC : IsPrimeFormGram C) (hC1 : (C : Matrix (Fin 5) (Fin 5) K) = 1) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = h.bar x) : InvolutionCriterion (primeFormFieldHom h hC σ) := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := h.finite
  have : CharP K 2 := h.charP
  have hq : ¬(5 = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hcase : (C : Matrix (Fin 5) (Fin 5) K) = 1 ∨
      ∃ r, 5 = 2 * r ∧ (C : Matrix (Fin 5) (Fin 5) K) = blockSwapJ 5 r := Or.inl hC1
  obtain ⟨Cl, hCl⟩ := exists_fixed_gram h hcase
  obtain ⟨-, -, hinjU, hNinn, hNC, hNnormal, -, -, -, -, hord2, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h (by omega) hq hC hcase Cl hCl σ hσ
  have hCN := centralizer_inf_le_zpowers h (by omega) hq hC hcase
    (fun _ => ⟨2, rfl⟩) Cl hCl σ hσ
  obtain ⟨eSp⟩ := nonempty_matrixIsometryGroup_mulEquiv_statedSp (r := 2)
    (canonical_case_fixed h hCl (by omega) (Or.inr ⟨hC1, rfl⟩))
  have hk2 : Nat.card h.fixedField = 2 := by rw [h.card_fixedField, hf, pow_one]
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    CFSG.ComponentClassification.SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp 2 h.fixedField) h.card_fixedField (by omega) ⟨MulEquiv.refl _⟩
  set N := ((primeFormConjHom h (C : Matrix (Fin 5) (Fin 5) K)).comp
    (fixedIsometryHom h hCl)).range with hN
  let e : N ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (((MonoidHom.ofInjective hinjU).symm.trans eSp).trans eProj.symm).trans
      (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hk2)
  set L : Subgroup (MulAut (primeFormP h (C : Matrix (Fin 5) (Fin 5) K))) := ⁅N, N⁆ with hL
  have eL : L ≃* commutator CFSG.ComponentClassification.PresentationLocal.sympFour :=
    CFSG.ComponentClassification.RankTwoHypIILinear.commutatorEquivOfMulEquiv e
  have hLsimple : IsSimpleGroup L := by
    have := CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
    exact eL.isSimpleGroup
  have hnc : ¬ ∀ a b : L, a * b = b * a := by
    intro hab
    apply CFSG.ComponentClassification.PresentationLocal.not_isMulCommutative_commutator_sympFour
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eL.symm.injective
    rw [map_mul, map_mul, hab]
  have hLp : ⁅L, L⁆ = L :=
    CFSG.ComponentClassification.RankTwoHypIIY.commutator_eq_self_of_isSimpleGroup hLsimple hnc
  have hLN : L ≤ N := by
    rw [hL, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hCNn : centralizer {primeFormFieldHom h hC σ} ≤
      normalizer (N : Set (MulAut (primeFormP h (C : Matrix (Fin 5) (Fin 5) K)))) :=
    (normal_subgroupOf_iff_le_normalizer hNC).mp hNnormal
  have h2 : primeFormFieldHom h hC σ ^ 2 = 1 := by
    have := pow_orderOf_eq_one (primeFormFieldHom h hC σ)
    rwa [hord2] at this
  refine involutionCriterion_of_inner_perfect (conj_injective_primeFormP h hC (by omega)) h2
    (hLN.trans hNinn) (hLN.trans hNC) hLp fun s hs => ?_
  obtain ⟨hsM, hsL⟩ := mem_inf.mp hs
  exact hCN (mem_inf.mpr ⟨hsM,
    mem_centralizer_of_mem_centralizer_commutator e
      CFSG.ComponentClassification.PresentationLocal.centralizer_commutator_sympFour
      (hCNn hsM) hsL⟩)

theorem primeFormFieldU_fixedIsometryHom {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    {Cl : GL (Fin n) h.fixedField}
    (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)
    {φ : K ≃+* K} (hφ : fixedRestrict h φ = 1)
    (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) :
    primeFormFieldU h hC φ (fixedIsometryHom h hCl g) = fixedIsometryHom h hCl g := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_primeFormFieldU, coe_glAut, coe_fixedIsometryHom]
  ext a b
  have h1 := congrArg Subtype.val (RingEquiv.congr_fun hφ
    (((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) a b))
  rw [fixedRestrict_apply] at h1
  exact h1

theorem mul_self_eq_one_of_fixedRestrict_eq_one {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x)
    {φ : K ≃+* K} (hφ : fixedRestrict h φ = 1) : φ * φ = 1 := by
  have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [pow_two]
    change σ (σ x) = x
    rw [hσ, hσ, h.bar_bar]
  rcases eq_one_or_eq_of_mem_zpowers hσ2 (mem_zpowers_of_fixedRestrict_eq_one h hσ hφ) with
    rfl | rfl
  · exact mul_one 1
  · rw [← pow_two, hσ2]

theorem involutionCriterion_primeFormFieldHom_of_even (hn : 4 ≤ n) (heven : Even n)
    (hnf : ¬(n = 4 ∧ f = 1)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hC1 : (C : Matrix (Fin n) (Fin n) K) = 1) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    InvolutionCriterion (primeFormFieldHom h hC σ) := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := h.finite
  have : CharP K 2 := h.charP
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hn3 : 3 ≤ n := by omega
  have hCl : ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = C := by
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), hC1]
  obtain ⟨hcent, -, -, hNinn, hNC, -, Θ, hΘ, -, -, -, -, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn3 hq hC (Or.inl hC1) 1 hCl σ hσ
  set i : Fin n := ⟨0, by omega⟩ with hi
  set O := matrixIsometryGroup ((1 : GL (Fin n) h.fixedField) :
    Matrix (Fin n) (Fin n) h.fixedField) with hO
  set R₀ := NonalternatingRadical.radicalGroup (K := h.fixedField) i with hR₀
  set F := (primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)
    with hF
  have hRO : R₀ ≤ O := NonalternatingRadical.radicalGroup_le heven i
  set A := (R₀.subgroupOf O).map F with hA
  have hsub : R₀.subgroupOf O ≤ ⁅R₀.subgroupOf O, (⊤ : Subgroup O)⁆ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have h1 := LinearDelta.radicalGroup_le_commutator (K := h.fixedField) h.one_le
      h.card_fixedField heven hn hnf hx
    have e : ⁅R₀, O⁆ = (⁅R₀.subgroupOf O, (⊤ : Subgroup O)⁆).map O.subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRO, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h2 : (x : GL (Fin n) h.fixedField) ∈ ⁅R₀, O⁆ := h1
    rw [e] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    rwa [show x = y from Subtype.ext hyx.symm]
  have hAcomm : A ≤ ⁅A, F.range⁆ := by
    rw [hA, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hsub
  refine involutionCriterion_of_inner_commutator (conj_injective_primeFormP h hC hn3)
    (Subgroup.map_le_range F _) hNinn hNC hAcomm fun β hβ => ?_
  obtain ⟨hβM, hβA⟩ := mem_inf.mp hβ
  obtain ⟨g, φ, rfl⟩ := (hcent _).mp hβM
  have hΘβ := hΘ g φ hβM
  have hc : ∀ x ∈ R₀, conjAut n h.fixedField (g : GL (Fin n) h.fixedField) *
      fieldAut n h.fixedField (fixedRestrict h φ) * conjAut n h.fixedField x *
        (conjAut n h.fixedField (g : GL (Fin n) h.fixedField) *
          fieldAut n h.fixedField (fixedRestrict h φ))⁻¹ = conjAut n h.fixedField x := by
    intro x hx
    set y : O := ⟨x, hRO hx⟩ with hy
    have hFy : F y = primeFormPsi h hC ⟨fixedIsometryHom h hCl y, 1⟩ := by
      rw [primeFormPsi_apply, map_one, mul_one]
      rfl
    have hyM : primeFormPsi h hC ⟨fixedIsometryHom h hCl y, 1⟩ ∈
        centralizer {primeFormFieldHom h hC σ} := hFy ▸ hNC ⟨y, rfl⟩
    have hΘy := hΘ y 1 hyM
    rw [map_one, map_one, mul_one] at hΘy
    have hβy : primeFormPsi h hC ⟨fixedIsometryHom h hCl g, φ⟩ *
        primeFormPsi h hC ⟨fixedIsometryHom h hCl y, 1⟩ =
          primeFormPsi h hC ⟨fixedIsometryHom h hCl y, 1⟩ *
            primeFormPsi h hC ⟨fixedIsometryHom h hCl g, φ⟩ := by
      rw [← hFy]
      exact (mem_centralizer_iff.mp hβA (F y) ⟨y, mem_subgroupOf.mpr hx, rfl⟩).symm
    have hcomm : Θ ⟨_, hβM⟩ * Θ ⟨_, hyM⟩ = Θ ⟨_, hyM⟩ * Θ ⟨_, hβM⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hβy
    rw [hΘβ, hΘy] at hcomm
    rw [hcomm, mul_inv_cancel_right]
  obtain ⟨hφ1, hgR⟩ := NonalternatingRadical.eq_radical_of_centralizes heven hn3 i g.2
    (fixedRestrict h φ) hc
  have hgg : g * g = 1 :=
    Subtype.ext (NonalternatingRadical.mul_self_of_mem_radicalGroup heven hgR)
  have hφφ := mul_self_eq_one_of_fixedRestrict_eq_one h hσ hφ1
  have hfix := primeFormFieldU_fixedIsometryHom h hC hCl hφ1 g
  rw [sq, ← map_mul]
  have e : (⟨fixedIsometryHom h hCl g, φ⟩ * ⟨fixedIsometryHom h hCl g, φ⟩ :
      primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K)) = 1 := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, hfix, ← map_mul, hgg, map_one, SemidirectProduct.one_left]
    · rw [SemidirectProduct.mul_right, hφφ, SemidirectProduct.one_right]
  rw [e, map_one]

theorem involutionCriterion_of_fieldFactor_bar (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hnf : ¬(n = 4 ∧ f = 1)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (hα : orderOf α = 2)
    (hφ : ∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x) : InvolutionCriterion α := by
  have : CharP K 2 := h.charP
  have hf1 := h.one_le
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθα⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq α hα hφ
  have hαθ : α = MulAut.congr θ (primeFormFieldHom h hC₀ (primeFormFieldFactor h hC hn hq α)) :=
    MulEquiv.ext fun x => by
      rw [hθα x, MulAut.congr_apply]
      rfl
  rw [hαθ]
  refine InvolutionCriterion.congr θ ?_
  rcases hcase₀ with h1 | ⟨r, hr, hJ⟩
  · rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
    · obtain ⟨m, hm⟩ := hev
      exact involutionCriterion_primeFormFieldHom_of_even h (by omega) ⟨m, hm⟩ hnf hC₀ h1 _ hφ
    · by_cases h52 : r = 2 ∧ f = 1
      · obtain ⟨rfl, hf⟩ := h52
        subst hr
        exact involutionCriterion_primeFormFieldHom_five_two h hf hC₀ h1 _ hφ
      · refine involutionCriterion_primeFormFieldHom_of_perfect h hn hq hC₀ (r := r) ?_
          (Or.inr ⟨h1, hr⟩) _ hφ
        by_cases hf : f = 1
        · subst hf
          right
          have h3 : n ≠ 3 := fun h3 => hq ⟨h3, by norm_num⟩
          omega
        · left
          omega
  · refine involutionCriterion_primeFormFieldHom_of_perfect h hn hq hC₀ (r := r) ?_
      (Or.inl ⟨hr, hJ⟩) _ hφ
    by_cases hf : f = 1
    · subst hf
      right
      omega
    · left
      omega

end UnitaryOuter

end CFSG.SeitzReduction
