module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuterBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSULinearRadical
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.SeitzReduction

namespace LinearDelta

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

section Radical

variable [CharP K 2]

theorem isotropic_of_mem_radicalW {i : Fin n} {u : Fin n → K} (hu : u ∈ radicalW i) :
    u ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0 := by
  rw [one_mulVec, dotProduct_self_eq_sq, (mem_radicalW.mp hu).1, zero_pow two_ne_zero]

theorem transvGL_one_mulVec {u : Fin n → K}
    (hu : u ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0) (x : Fin n → K) :
    ((transvGL (1 : Matrix (Fin n) (Fin n) K) hu 1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ x = x + (u ⬝ᵥ x) • u := by
  rw [coe_transvGL, transvMatrix, add_mulVec, one_mulVec, one_smul, vecMulVec_mulVec,
    one_mulVec, op_smul_eq_smul]

theorem coe_commutator_radicalGL_transvGL (hn : Even n) {i : Fin n} {u v : Fin n → K}
    (hu : u ∈ radicalW i) (hv : v ∈ radicalW i) :
    ((⁅radicalGL hn (mem_radicalW.mp hv).1 0,
        transvGL (1 : Matrix (Fin n) (Fin n) K) (isotropic_of_mem_radicalW hu) 1⁆ :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      radicalMatrix ((u ⬝ᵥ v) • u) ((u ⬝ᵥ v) ^ 2) := by
  set a := radicalGL hn (mem_radicalW.mp hv).1 0 with ha
  set b := transvGL (1 : Matrix (Fin n) (Fin n) K) (isotropic_of_mem_radicalW hu) 1 with hb
  have hbO : b ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) :=
    transvGL_mem (transpose_one) _ 1
  have hainv : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_right (Units.ext (radicalMatrix_mul_self hn (mem_radicalW.mp hv).1 0))
  have hbv : (b : Matrix (Fin n) (Fin n) K) *ᵥ v = v + (u ⬝ᵥ v) • u :=
    transvGL_one_mulVec _ v
  have hv1 : (onesVec : Fin n → K) ⬝ᵥ v = 0 := (mem_radicalW.mp hv).1
  have hbv1 : (onesVec : Fin n → K) ⬝ᵥ ((b : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0 := by
    rw [onesVec_dotProduct_mulVec_of_mem hbO, hv1]
  rw [commutatorElement_def, hainv, Units.val_mul, Units.val_mul, Units.val_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (b : Matrix (Fin n) (Fin n) K),
    show (a : Matrix (Fin n) (Fin n) K) = radicalMatrix v 0 from rfl, conj_radicalMatrix hbO,
    radicalMatrix_mul 0 0 (onesVec_dotProduct_onesVec hn) hv1 hbv1, hbv]
  congr 1
  · funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_self_eq_sq, hv1,
      dotProduct_comm v u]
    ring

@[expose] def RadicalIn (S : Subgroup (GL (Fin n) K)) (x : Fin n → K) (c : K) : Prop :=
  ∃ g ∈ S, (g : Matrix (Fin n) (Fin n) K) = radicalMatrix x c

omit [CharP K 2] in
theorem radicalIn_zero (S : Subgroup (GL (Fin n) K)) : RadicalIn S 0 0 :=
  ⟨1, one_mem S, by rw [Units.val_one, radicalMatrix_zero]⟩

theorem RadicalIn.mul (hn : Even n) {S : Subgroup (GL (Fin n) K)} {x y : Fin n → K} {a b : K}
    (hx : RadicalIn S x a) (hy : RadicalIn S y b) (hx1 : (onesVec : Fin n → K) ⬝ᵥ x = 0)
    (hy1 : (onesVec : Fin n → K) ⬝ᵥ y = 0) : RadicalIn S (x + y) (a + b + x ⬝ᵥ y) := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨h, hh, hhy⟩ := hy
  exact ⟨g * h, mul_mem hg hh, by
    rw [Units.val_mul, hgx, hhy, radicalMatrix_mul a b (onesVec_dotProduct_onesVec hn) hx1 hy1]⟩

theorem eq_zero_of_forall_dotProduct_eq_zero (hn : Even n) {i : Fin n} {w : Fin n → K}
    (hw : w ∈ radicalW i) (h : ∀ w' ∈ radicalW i, w ⬝ᵥ w' = 0) : w = 0 := by
  obtain ⟨hw1, hw2⟩ := mem_radicalW.mp hw
  have hx : ∀ x : Fin n → K, w ⬝ᵥ x = 0 := by
    intro x
    conv_lhs => rw [eq_decomp i x]
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_comm _ onesVec, hw1, dotProduct_single_one, hw2, smul_zero, smul_zero,
      add_zero, zero_add]
    exact h _ (decomp_mem_radicalW hn i x)
  funext j
  have := hx (Pi.single j 1)
  rwa [dotProduct_single_one] at this

theorem exists_mem_radicalW_dotProduct_eq_one (hn : Even n) {i : Fin n} {u : Fin n → K}
    (hu : u ∈ radicalW i) (hu0 : u ≠ 0) : ∃ v ∈ radicalW i, u ⬝ᵥ v = 1 := by
  by_contra hcon
  apply hu0
  refine eq_zero_of_forall_dotProduct_eq_zero hn hu fun w hw => ?_
  by_contra hc
  exact hcon ⟨(u ⬝ᵥ w)⁻¹ • w, Submodule.smul_mem _ _ hw, by
    rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hc]⟩

theorem radical_smul_mem (hn : Even n) {i : Fin n} {u : Fin n → K} (hu : u ∈ radicalW i)
    (hu0 : u ≠ 0) (μ : K) :
    RadicalIn ⁅radicalGroup (K := K) i, matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆
      (μ • u) (μ ^ 2) := by
  obtain ⟨v, hv, huv⟩ := exists_mem_radicalW_dotProduct_eq_one hn hu hu0
  have hμv : μ • v ∈ radicalW i := Submodule.smul_mem _ _ hv
  have hμ : u ⬝ᵥ (μ • v) = μ := by rw [dotProduct_smul, smul_eq_mul, huv, mul_one]
  exact ⟨_, commutator_mem_commutator ((mem_radicalGroup hn).mpr ⟨_, hμv, 0, rfl⟩)
    (transvGL_mem transpose_one _ 1), (coe_commutator_radicalGL_transvGL hn hu hμv).trans
      (by rw [hμ])⟩

omit [CharP K 2] in
theorem eq_zero_or_eq_one_of_card_two [Finite K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  classical
  have := Fintype.ofFinite K
  have hu : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK])
  have hx : x ∈ ({0, 1} : Finset K) := hu ▸ Finset.mem_univ x
  simpa using hx

theorem single_add_single_mem_radicalW {a b i : Fin n} (hai : a ≠ i) (hbi : b ≠ i) :
    (Pi.single a 1 + Pi.single b 1 : Fin n → K) ∈ radicalW i := by
  rw [mem_radicalW]
  refine ⟨?_, ?_⟩
  · rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one, onesVec_apply,
      onesVec_apply, CharTwo.add_self_eq_zero]
  · rw [Pi.add_apply, Pi.single_eq_of_ne hai.symm, Pi.single_eq_of_ne hbi.symm, add_zero]

omit [CharP K 2] in
theorem single_add_single_ne_zero {a b : Fin n} (hab : a ≠ b) :
    (Pi.single a 1 + Pi.single b 1 : Fin n → K) ≠ 0 := by
  intro h
  have := congrFun h a
  rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero,
    Pi.zero_apply] at this
  exact one_ne_zero this

theorem radical_sq_mem (hn : Even n) {i : Fin n} {w : Fin n → K} (hw : w ∈ radicalW i)
    (hw0 : w ≠ 0) {l : K} (hl : l ≠ 0) :
    RadicalIn ⁅radicalGroup (K := K) i, matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆
      w (l ^ 2) := by
  have h := radical_smul_mem hn (Submodule.smul_mem _ l⁻¹ hw)
    (smul_ne_zero (inv_ne_zero hl) hw0) l
  rwa [smul_smul, mul_inv_cancel₀ hl, one_smul] at h

theorem radical_zero_mem_of_four_le [Finite K] (hn : Even n) {i : Fin n} {w : Fin n → K}
    (hw : w ∈ radicalW i) (hw0 : w ≠ 0) (h4 : 4 ≤ Nat.card K) (c : K) :
    RadicalIn ⁅radicalGroup (K := K) i, matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆
      0 c := by
  classical
  have hw1 : (onesVec : Fin n → K) ⬝ᵥ w = 0 := (mem_radicalW.mp hw).1
  have hww : w ⬝ᵥ w = 0 := by rw [dotProduct_self_eq_sq, hw1, zero_pow two_ne_zero]
  have hw2 : w + w = 0 := funext fun j => by
    rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  obtain ⟨l, hl0, hls⟩ : ∃ l : K, l ≠ 0 ∧ l ≠ s := by
    by_contra hcon
    push Not at hcon
    have := Fintype.ofFinite K
    have hsub : (Finset.univ : Finset K) ⊆ {0, s} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
    have h2 := Finset.card_le_two (a := (0 : K)) (b := s)
    omega
  have hm0 : l + s ≠ 0 := by
    intro h
    apply hls
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, h]
  have h := (radical_sq_mem hn hw hw0 hl0).mul hn (radical_sq_mem hn hw hw0 hm0) hw1 hw1
  rw [hw2, hww, add_zero] at h
  convert h using 1
  rw [hs]
  linear_combination (-(l ^ 2) - l * s) * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem radical_zero_one_mem (hn : Even n) (hn6 : 6 ≤ n) :
    RadicalIn ⁅radicalGroup (K := K) (⟨0, by omega⟩ : Fin n),
      matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆ 0 1 := by
  set i : Fin n := ⟨0, by omega⟩ with hi
  have h1i : (⟨1, by omega⟩ : Fin n) ≠ i := by simp [hi, Fin.ext_iff]
  have h2i : (⟨2, by omega⟩ : Fin n) ≠ i := by simp [hi, Fin.ext_iff]
  have h3i : (⟨3, by omega⟩ : Fin n) ≠ i := by simp [hi, Fin.ext_iff]
  have h4i : (⟨4, by omega⟩ : Fin n) ≠ i := by simp [hi, Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h34 : (⟨3, by omega⟩ : Fin n) ≠ ⟨4, by omega⟩ := by simp [Fin.ext_iff]
  set w : Fin n → K := Pi.single ⟨1, by omega⟩ 1 + Pi.single ⟨2, by omega⟩ 1 with hw
  set w' : Fin n → K := Pi.single ⟨3, by omega⟩ 1 + Pi.single ⟨4, by omega⟩ 1 with hw'
  have hwW : w ∈ radicalW i := single_add_single_mem_radicalW h1i h2i
  have hw'W : w' ∈ radicalW i := single_add_single_mem_radicalW h3i h4i
  have hww' : w ⬝ᵥ w' = 0 := by
    rw [hw, hw', add_dotProduct, single_one_dotProduct, single_one_dotProduct]
    simp [Fin.ext_iff]
  have hsW : w + w' ∈ radicalW i := add_mem hwW hw'W
  have hs0 : w + w' ≠ 0 := by
    intro h
    have := congrFun h ⟨1, by omega⟩
    simp [hw, hw', Fin.ext_iff] at this
  have hs1 : (onesVec : Fin n → K) ⬝ᵥ (w + w') = 0 := (mem_radicalW.mp hsW).1
  have hone : ∀ {x : Fin n → K}, x ∈ radicalW i → x ≠ 0 →
      RadicalIn ⁅radicalGroup (K := K) i, matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆
        x 1 := by
    intro x hx hx0
    have h := radical_sq_mem hn hx hx0 (one_ne_zero (α := K))
    rwa [one_pow] at h
  have h1 := (hone hwW (single_add_single_ne_zero h12)).mul hn
    (hone hw'W (single_add_single_ne_zero h34)) (mem_radicalW.mp hwW).1 (mem_radicalW.mp hw'W).1
  rw [hww', add_zero, CharTwo.add_self_eq_zero] at h1
  have h2 := (hone hsW hs0).mul hn h1 hs1 hs1
  have hss : (w + w') + (w + w') = 0 := funext fun j => by
    rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
  have hss' : (w + w') ⬝ᵥ (w + w') = 0 := by
    rw [dotProduct_self_eq_sq, hs1, zero_pow two_ne_zero]
  rwa [hss, hss', add_zero, add_zero] at h2

theorem radicalGroup_le_commutator [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : Even n) (hn4 : 4 ≤ n) (hnf : ¬(n = 4 ∧ f = 1)) :
    radicalGroup (K := K) (⟨0, by omega⟩ : Fin n) ≤
      ⁅radicalGroup (K := K) (⟨0, by omega⟩ : Fin n),
        matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆ := by
  set i : Fin n := ⟨0, by omega⟩ with hi
  set S := ⁅radicalGroup (K := K) i, matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆ with hS
  have h1i : (⟨1, by omega⟩ : Fin n) ≠ i := by simp [hi, Fin.ext_iff]
  have h2i : (⟨2, by omega⟩ : Fin n) ≠ i := by simp [hi, Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hzero : ∀ c : K, RadicalIn S 0 c := by
    intro c
    by_cases hf1 : f = 1
    · have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
      rcases eq_zero_or_eq_one_of_card_two hK2 c with rfl | rfl
      · exact radicalIn_zero S
      · exact radical_zero_one_mem hn (by
          obtain ⟨m, hm⟩ := hn
          by_contra h
          exact hnf ⟨by omega, hf1⟩)
    · refine radical_zero_mem_of_four_le hn (single_add_single_mem_radicalW h1i h2i)
        (single_add_single_ne_zero h12) ?_ c
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hall : ∀ w ∈ radicalW i, ∀ c : K, RadicalIn S w c := by
    intro w hw c
    by_cases hw0 : w = 0
    · rw [hw0]
      exact hzero c
    · have h1 := radical_sq_mem hn hw hw0 (one_ne_zero (α := K))
      rw [one_pow] at h1
      have h := h1.mul hn (hzero (c + 1)) (mem_radicalW.mp hw).1 (by rw [dotProduct_zero])
      rw [add_zero, dotProduct_zero, add_zero, ← add_assoc, add_comm (1 : K) c, add_assoc,
        CharTwo.add_self_eq_zero, add_zero] at h
      exact h
  intro g hg
  obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).mp hg
  obtain ⟨h, hhS, hh⟩ := hall v hv c
  have : g = h := Units.ext (hc.trans hh.symm)
  rw [this]
  exact hhS

end Radical

theorem involutionCriterion_dualAut {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (heven : Even n) (hnf : ¬(n = 4 ∧ f = 1)) :
    InvolutionCriterion (dualAut n K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  set i : Fin n := ⟨0, by omega⟩ with hi
  obtain ⟨-, hOinn, -, -, hOC, -, -⟩ :=
    even_linear_canonical_graph_symplectic_centralizers hf hK (n := n) (by omega) 1 (Or.inl rfl)
  rw [map_one, one_mul] at hOC
  rw [Units.val_one] at hOinn hOC
  refine involutionCriterion_of_inner_commutator
    (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by omega))
    (map_mono (radicalGroup_le heven i)) hOinn hOC ?_ fun β hβ =>
      sq_eq_one_of_mem_centralizer_radicalImage heven (by omega) i hβ
  rw [← map_commutator]
  exact map_mono (radicalGroup_le_commutator hf hK heven hn hnf)

theorem involutionCriterion_conjAut_mul_dualAut_of_even {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (heven : Even n) (hnf : ¬(n = 4 ∧ f = 1))
    (A : GL (Fin n) K) (hα : (conjAut n K A * dualAut n K) ^ 2 = 1)
    (hnalt : ¬∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0) :
    InvolutionCriterion (conjAut n K A * dualAut n K) := by
  obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK (by omega) A hα
  rcases hC with ⟨hC1, -⟩ | ⟨r, -, -, halt⟩
  · have hC : C = 1 := Units.ext hC1
    rw [hH, hC, map_one, one_mul]
    exact (involutionCriterion_dualAut hf hK hn heven hnf).conj _
  · exact absurd halt hnalt

end LinearDelta

end CFSG.SeitzReduction
