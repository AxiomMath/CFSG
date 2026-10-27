module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSubspaceCount
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIndexComparison

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem smul_isotropic {h : UnitaryFieldData p f K} (g : hypSU h r ε)
    {W : Submodule K (HypIndex r ε → K)} (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) :
    ∀ x ∈ g • W, ∀ y ∈ g • W, hypForm h r ε x y = 0 := by
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g W).mp hx
  obtain ⟨y', hy', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y g W).mp hy
  rw [hypForm_smul_smul]
  exact hW x' hx' y' hy'

theorem finrank_smul {h : UnitaryFieldData p f K} (g : hypSU h r ε)
    (W : Submodule K (HypIndex r ε → K)) : Module.finrank K ↥(g • W) = Module.finrank K W :=
  LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K _ g) W

theorem hypSU_exists_smul_eq (h : UnitaryFieldData p f K) {W W' : Submodule K (HypIndex r ε → K)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0)
    (hW' : ∀ x ∈ W', ∀ y ∈ W', hypForm h r ε x y = 0)
    (hdim : Module.finrank K W = Module.finrank K W') : ∃ g : hypSU h r ε, g • W = W' := by
  obtain ⟨g', hg', hgW⟩ := (isotropic_flag_extension h (hypForm_isSymm h)
    (hypForm_separatingLeft h) rfl).2.2 W W' hW hW' hdim
  set A := Matrix.GeneralLinearGroup.toLin.symm g' with hAdef
  have hgA : g' = Matrix.GeneralLinearGroup.toLin A := by
    rw [hAdef, MulEquiv.apply_symm_apply]
  have hA : A ∈ hypSU h r ε := by
    rw [hgA] at hg'
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h _ A).mp hg'
  refine ⟨⟨A, hA⟩, ?_⟩
  rw [← hgW, hgA]
  rfl

theorem index_isoStabilizer (h : UnitaryFieldData p f K) {W : Submodule K (HypIndex r ε → K)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) :
    (isoStabilizer h r ε W).index =
      Nat.card (TotIsoSubspaces (hypForm h r ε) (Module.finrank K W)) := by
  rw [isoStabilizer, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun W' => ?_)
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨finrank_smul g W, smul_isotropic g hW⟩
  · rintro ⟨hdim, hW'⟩
    obtain ⟨g, hg⟩ := hypSU_exists_smul_eq h hW hW' hdim.symm
    exact ⟨g, hg⟩

theorem prod_Icc_one_eq_prod_range (g : ℕ → ℚ) (r : ℕ) :
    ∏ j ∈ Finset.Icc 1 r, g j = ∏ i ∈ Finset.range r, g (i + 1) := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem isoIndexCount_eq_prod_odd {q : ℕ} (hq : 2 ≤ q) (m r : ℕ) (hm : m ≤ 1) :
    isoIndexCount q (m + 2 * r) r = ∏ i ∈ Finset.range r, isoTerm q (m + 2 * i + 1 + m) := by
  have hD : ∏ i ∈ Finset.range r, ((q : ℚ) ^ (2 * i + 2) - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (pow_sub_one_pos hq (by omega)).ne'
  rw [isoIndexCount_shift, div_eq_iff hD, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · rw [show 0 + 2 * i + 2 = 2 * (i + 1) by ring, isoTerm_even]
    ring_nf
  · rw [show 1 + 2 * i + 1 = 2 * (i + 1) by ring, isoTerm_even]
    ring_nf

theorem isotropic_stabilizer_index (h : UnitaryFieldData p f K)
    (W : Submodule K (HypIndex r ε → K)) (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) :
    (projIsoStabilizer h r ε W).index = (isoStabilizer h r ε W).index ∧
    ((isoStabilizer h r ε W).index : ℚ) =
      isoIndexCount (p ^ f) (2 * r + ε) (Module.finrank K W) ∧
    0 < (isoStabilizer h r ε W).index ∧
    (∀ n, isoIndexCount (p ^ f) n 0 = 1) ∧
    (∀ n, isoIndexCount (p ^ f) n 1 = (((p ^ f : ℕ) : ℚ) ^ n - (-1) ^ n) *
      (((p ^ f : ℕ) : ℚ) ^ (n - 1) - (-1) ^ (n - 1)) / (((p ^ f : ℕ) : ℚ) ^ 2 - 1)) ∧
    (∀ s, isoIndexCount (p ^ f) (2 * s) s =
      ∏ j ∈ Finset.Icc 1 s, (((p ^ f : ℕ) : ℚ) ^ (2 * j - 1) + 1)) ∧
    (∀ s, isoIndexCount (p ^ f) (2 * s + 1) s =
      ∏ j ∈ Finset.Icc 1 s, (((p ^ f : ℕ) : ℚ) ^ (2 * j + 1) + 1)) := by
  have hq : 2 ≤ p ^ f :=
    h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  have hdim : Module.finrank K (HypIndex r ε → K) = 2 * r + ε := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hk : 2 * Module.finrank K W ≤ 2 * r + ε := by
    obtain ⟨Wc, hWc, -⟩ := exists_isotropicChain_eq W hW
    have := ((isotropic_flag_extension h (hypForm_isSymm (r := r) (ε := ε) h)
      (hypForm_separatingLeft h) hdim).1 _ Wc hWc).1
    omega
  have hcount := (isotropic_subspace_count h (hypForm_isSymm (r := r) (ε := ε) h)
    (hypForm_separatingLeft h) hdim (Module.finrank K W)).2.1 hk
  have hindex : ((isoStabilizer h r ε W).index : ℚ) =
      isoIndexCount (p ^ f) (2 * r + ε) (Module.finrank K W) := by
    rw [index_isoStabilizer h hW, isoIndexCount, eq_div_iff (Finset.prod_ne_zero_iff.mpr
      fun i hi => (pow_sub_one_pos hq (by rw [Finset.mem_Icc] at hi; omega)).ne')]
    exact_mod_cast hcount
  refine ⟨Subgroup.index_map_eq _ (hypProj_surjective h r ε)
      (by rw [ker_hypProj]; exact hypScalars_le_isoStabilizer W), hindex, ?_,
    fun n => by simp [isoIndexCount], fun n => ?_, fun s => ?_, fun s => ?_⟩
  · have := isoIndexCount_pos (q := p ^ f) (n := 2 * r + ε) hq hk
    rw [← hindex] at this
    exact_mod_cast this
  · rw [isoIndexCount_one, isoTerm, isoTerm, mul_comm]
  · rw [show 2 * s = 0 + 2 * s by ring, isoIndexCount_eq_prod_odd hq 0 s zero_le_one,
      prod_Icc_one_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show 0 + 2 * i + 1 + 0 = 2 * i + 1 by ring, isoTerm_odd,
      show 2 * (i + 1) - 1 = 2 * i + 1 by omega]
  · rw [show 2 * s + 1 = 1 + 2 * s by ring, isoIndexCount_eq_prod_odd hq 1 s le_rfl,
      prod_Icc_one_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show 1 + 2 * i + 1 + 1 = 2 * (i + 1) + 1 by ring, isoTerm_odd]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
