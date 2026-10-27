module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuterBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearFiveTwo
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearRigid

public section

namespace CFSG.SeitzReduction

namespace LinearOuter

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog FourGroupEvenCanonical
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField mem_fixedField)
open CFSG.RankThree.PartOne (linearSubfieldInclusion
  fixingSubgroup_range_linearSubfieldInclusion simple_nonabelian_range_linearSubfieldInclusion)
open CFSG.ComponentClassification.RankTwoHypIIY (commutator_eq_self_of_isSimpleGroup)
open CFSG.ComponentClassification.RankTwoHypIILinear (ringEquiv_eq_one_of_card_two
  commutatorEquivOfMulEquiv eq_one_of_mem_centralizer_commutator)
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)
open CFSG.ComponentClassification.PresentationLocal (sympFour centralizer_commutator_sympFour
  isSimpleGroup_commutator_sympFour not_isMulCommutative_commutator_sympFour)
open CFSG.Assembly.LowTwoRank (StatedSp StatedSU)

variable {K : Type} [Field K] {n : ℕ}

theorem conj_injective (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) :=
  CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL hn

theorem involutionCriterion_fieldAut [Finite K] (hn : 3 ≤ n) (σ : K ≃+* K)
    (hσ : fieldAut n K σ ^ 2 = 1) : InvolutionCriterion (fieldAut n K σ) := by
  have hk : ∀ x, x ∈ fixedField K σ ↔ σ x = x := fun x => mem_fixedField K σ x
  have hfix := fixingSubgroup_range_linearSubfieldInclusion hk hn
  obtain ⟨hsimple, hnc⟩ := simple_nonabelian_range_linearSubfieldInclusion (K := K) hn
    (fixedField K σ)
  have hperf := commutator_eq_self_of_isSimpleGroup hsimple hnc
  have hσmem : fieldAut n K σ ∈ fixingSubgroup (MulAut (projectiveSL n K))
      ((linearSubfieldInclusion n (fixedField K σ)).range : Set (projectiveSL n K)) := by
    rw [hfix]
    exact mem_zpowers _
  refine involutionCriterion_of_le_zpowers hσ (le_closure_odd_fixed_of_perfect
    (fun c hc => (mem_fixingSubgroup_iff _).mp hσmem c hc) hperf) fun β _ hβ => ?_
  rw [← hfix]
  exact (mem_fixingSubgroup_iff _).mpr hβ

theorem involutionCriterion_conjAut_mul_fieldAut [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    InvolutionCriterion (conjAut n K A * fieldAut n K σ) := by
  obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent hf hK hn A σ hσ hα
  rw [hH] at hα ⊢
  rw [conj_pow, conj_eq_one_iff] at hα
  exact (involutionCriterion_fieldAut hn σ hα).conj _

theorem involutionCriterion_fieldAut_mul_dualAut {e : ℕ} (h : UnitaryFieldData 2 e K)
    (hn : 3 ≤ n) (hq : (n, 2 ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    InvolutionCriterion (fieldAut n K σ * dualAut n K) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hinn, -, hcent, -, hC⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := n) hn σ hσ
  have hSU : Group.IsPerfect (StatedSU n (2 ^ e) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (by rw [h.card, ← pow_mul, mul_comm])
      hn hq
  let eN := ι.symm.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (n := n) (by omega))
  have hperf : Group.IsPerfect
      ((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 e K n).map (conjAut n K)) :=
    Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hσσ : σ * σ = 1 := RingEquiv.ext fun x => by
    change σ (σ x) = x
    rw [hσ, hσ, h.bar_bar]
  obtain ⟨-, hff, -, hdd, -⟩ := standard_automorphism_transport (n := n) (K := K)
  have hx2 : (fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
    rw [sq, mul_assoc, ← mul_assoc (dualAut n K), dualAut_mul_fieldAut, mul_assoc, hdd, mul_one,
      hff, hσσ, map_one]
  exact involutionCriterion_of_inner_perfect (conj_injective hn) hx2 hinn hcent
    (Subgroup.isPerfect_iff.mp hperf) (inf_le_right.trans hC.le)

theorem involutionCriterion_conjAut_mul_fieldAut_mul_dualAut [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hnf : ¬(n = 3 ∧ f = 2)) (A : GL (Fin n) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    InvolutionCriterion (conjAut n K A * fieldAut n K σ * dualAut n K) := by
  obtain ⟨⟨e, he⟩, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn A σ hσ hα
  have hud : UnitaryFieldData 2 e K := ⟨Nat.prime_two, by omega, by rw [hK, he, two_mul]⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by
    rw [hσx, UnitaryFieldData.bar_apply, show f / 2 = e by omega]
  have hq : (n, 2 ^ e) ≠ (3, 2) := by
    intro hq
    have h1 := congrArg Prod.fst hq
    have h2 : 2 ^ e = 2 ^ 1 := by simpa using congrArg Prod.snd hq
    have := Nat.pow_right_injective le_rfl h2
    simp only at h1
    omega
  rw [hH]
  exact (involutionCriterion_fieldAut_mul_dualAut hud hn hq σ hσbar).conj _

theorem isPerfect_statedSp_of_card [Finite K] {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hfr : 2 ≤ f ∨ 3 ≤ r) : Group.IsPerfect (StatedSp r K) := by
  apply CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp
  by_cases hf1 : f = 1
  · right
    right
    exact ⟨by rw [hK, hf1, pow_one], by omega⟩
  · left
    have := Fintype.ofFinite K
    have h4 : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩

theorem involutionCriterion_symplecticGraph {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (C : GL (Fin n) K) {r : ℕ} (hfr : 2 ≤ f ∨ 3 ≤ r)
    (hCr : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ n = 2 * r + 1)) :
    InvolutionCriterion (conjAut n K C * dualAut n K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hC : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Or.inr ⟨r, h1, h2⟩
    · exact Or.inl h1
  obtain ⟨hinj, hNinn, hβ2, -, hNC, -, hcan⟩ :=
    even_linear_canonical_graph_symplectic_centralizers hf hK hn C hC
  have hcent := (hcan (by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨r, h1, h2⟩
    · exact Or.inr ⟨h1, ⟨r, h2⟩⟩)).1
  have eN : (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) ≃*
      matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) :=
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
      (MonoidHom.ofInjective hinj).symm
  obtain ⟨eSp⟩ : Nonempty (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃*
      StatedSp r K) := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(MulEquiv.subgroupCongr (congrArg matrixIsometryGroup h2)).trans
        (blockSwapIsometryEquivStatedSp (by omega))⟩
    · have hC1 : (C : Matrix (Fin n) (Fin n) K) =
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, Units.val_one]
      obtain ⟨e₂⟩ := nonempty_altIsometry_mulEquiv_statedSp _
        (dotForm_restrict_isAlt (k := K) (n := n)) (dotForm_restrict_nondegenerate h2)
        (finrank_dotForm_ker h2)
      exact ⟨((MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hC1)).trans
        (oneRestrictEquiv h2)).trans e₂⟩
  have := isPerfect_statedSp_of_card hf hK hfr
  have hperf : Group.IsPerfect
      ((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K)) :=
    Group.IsPerfect.ofSurjective (f := (eN.trans eSp).symm.toMonoidHom)
      (eN.trans eSp).symm.surjective
  exact involutionCriterion_of_inner_perfect (conj_injective hn) hβ2 hNinn hNC
    (Subgroup.isPerfect_iff.mp hperf) hcent.le

theorem commutator_isometry_rigid_five_two [Finite K] (hK : Nat.card K = 2) :
    ⁅⁅(matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K),
        (matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K)⁆,
      ⁅(matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K),
        (matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map
          (conjAut 5 K)⁆⁆ =
      ⁅(matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K),
        (matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K)⁆ ∧
    ⁅(matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K),
        (matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K)⁆ ≤
      (MulAut.conj : projectiveSL 5 K →* MulAut (projectiveSL 5 K)).range ⊓
        centralizer {dualAut 5 K} ∧
    centralizer {dualAut 5 K} ⊓
        centralizer ((⁅(matrixIsometryGroup ((1 : GL (Fin 5) K) :
          Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K), (matrixIsometryGroup ((1 : GL (Fin 5) K) :
            Matrix (Fin 5) (Fin 5) K)).map (conjAut 5 K)⁆ : Subgroup (MulAut (projectiveSL 5 K))) :
          Set (MulAut (projectiveSL 5 K))) ≤
      zpowers (dualAut 5 K) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hK'
  obtain ⟨hinj, hNinn, -, hM, hNC, -, -⟩ :=
    even_linear_canonical_graph_symplectic_centralizers le_rfl hK' (n := 5) (by norm_num) 1
      (Or.inl rfl)
  have hβ : conjAut 5 K 1 * dualAut 5 K = dualAut 5 K := by rw [map_one, one_mul]
  rw [hβ] at hM hNC
  set O := matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hO
  set N := O.map (conjAut 5 K) with hN
  have eN : N ≃* O := (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
    (MonoidHom.ofInjective hinj).symm
  obtain ⟨e₂⟩ := nonempty_altIsometry_mulEquiv_statedSp _
    (dotForm_restrict_isAlt (k := K) (n := 5)) (dotForm_restrict_nondegenerate (r := 2) rfl)
    (finrank_dotForm_ker (r := 2) rfl)
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
    (X := StatedSp 2 K) hK' (by norm_num) ⟨MulEquiv.refl _⟩
  let e : N ≃* sympFour := ((eN.trans (oneRestrictEquiv (r := 2) rfl)).trans e₂).trans
    (eProj.symm.trans (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hK))
  set L : Subgroup (MulAut (projectiveSL 5 K)) := ⁅N, N⁆ with hL
  have eL : L ≃* commutator sympFour := commutatorEquivOfMulEquiv e
  have hLsimple : IsSimpleGroup L := by
    have := isSimpleGroup_commutator_sympFour
    exact eL.isSimpleGroup
  have hnc : ¬ ∀ a b : L, a * b = b * a := by
    intro hab
    apply not_isMulCommutative_commutator_sympFour
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eL.symm.injective
    rw [map_mul, map_mul, hab]
  have hLN : L ≤ N := by
    rw [hL, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine ⟨commutator_eq_self_of_isSimpleGroup hLsimple hnc,
    le_inf (hLN.trans hNinn) (hLN.trans hNC), ?_⟩
  intro s hs
  obtain ⟨hsM, hsL⟩ := mem_inf.mp hs
  have hs' : s ∈ (centralizer {dualAut 5 K} : Set (MulAut (projectiveSL 5 K))) := hsM
  rw [hM] at hs'
  obtain ⟨g, hg, φ, ε, -, rfl⟩ := hs'
  rw [ringEquiv_eq_one_of_card_two hK φ, map_one, mul_one] at hsL ⊢
  have hδL : dualAut 5 K ^ ε ∈ centralizer (L : Set (MulAut (projectiveSL 5 K))) := by
    refine pow_mem ?_ ε
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hNC (hLN hy))
  have hgL : conjAut 5 K g ∈ centralizer (L : Set (MulAut (projectiveSL 5 K))) := by
    have := mul_mem hsL (inv_mem hδL)
    rwa [mul_inv_cancel_right] at this
  have hg1 := eq_one_of_mem_centralizer_commutator e centralizer_commutator_sympFour
    (mem_map_of_mem _ hg) hgL
  rw [hg1, one_mul]
  exact pow_mem (mem_zpowers _) ε

theorem involutionCriterion_dualAut_five_two [Finite K] (hK : Nat.card K = 2) :
    InvolutionCriterion (dualAut 5 K) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨-, -, hβ2, -⟩ :=
    even_linear_canonical_graph_symplectic_centralizers le_rfl hK' (n := 5) (by norm_num) 1
      (Or.inl rfl)
  rw [map_one, one_mul] at hβ2
  obtain ⟨hLp, hLX, hC⟩ := commutator_isometry_rigid_five_two hK
  exact involutionCriterion_of_inner_perfect (conj_injective (by norm_num)) hβ2
    (hLX.trans inf_le_left) (hLX.trans inf_le_right) hLp hC

theorem involutionCriterion_canonicalGraph {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (hnf : ¬(n ≤ 4 ∧ f = 1)) (C : GL (Fin n) K)
    (hC : (∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ Odd n)) :
    InvolutionCriterion (conjAut n K C * dualAut n K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  rcases hC with ⟨r, hr, hCJ⟩ | ⟨hC1, ⟨r, hr⟩⟩
  · exact involutionCriterion_symplecticGraph hf hK hn C (r := r) (by omega) (Or.inl ⟨hr, hCJ⟩)
  · by_cases h52 : r = 2 ∧ f = 1
    · obtain ⟨rfl, rfl⟩ := h52
      obtain rfl : n = 5 := by omega
      have hC : C = 1 := Units.ext hC1
      subst hC
      rw [map_one, one_mul]
      exact involutionCriterion_dualAut_five_two (by rw [hK, pow_one])
    · exact involutionCriterion_symplecticGraph hf hK hn C (r := r) (by omega)
        (Or.inr ⟨hC1, hr⟩)

theorem involutionCriterion_conjAut_mul_dualAut_of_alt_or_odd {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hnf : ¬(n ≤ 4 ∧ f = 1)) (A : GL (Fin n) K)
    (hα : (conjAut n K A * dualAut n K) ^ 2 = 1)
    (hcase : Odd n ∨ ∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0) :
    InvolutionCriterion (conjAut n K A * dualAut n K) := by
  obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hα
  rw [hH]
  refine InvolutionCriterion.conj (involutionCriterion_canonicalGraph hf hK hn hnf C ?_) _
  rcases hC with ⟨hC1, hnalt⟩ | ⟨r, hr, hCJ, -⟩
  · rcases hcase with hodd | halt
    · exact Or.inr ⟨hC1, hodd⟩
    · exact absurd halt hnalt
  · exact Or.inl ⟨r, hr, hCJ⟩

end LinearOuter

end CFSG.SeitzReduction
