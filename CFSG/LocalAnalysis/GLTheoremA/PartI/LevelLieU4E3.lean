module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E2
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3 σ4)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K card_K)
open Matrix

theorem smul_eq_mulVec (x : SU4) (v : Fin 4 → K) : x • v = (mat x).mulVec v := rfl

theorem smul_single_eq (x : SU4) (i : Fin 4) (k : Fin 4) :
    (x • (Pi.single i 1 : Fin 4 → K)) k = mat x k i := by
  rw [smul_eq_mulVec, Matrix.mulVec_single_one]
  rfl

theorem mat_inv (x : SU4) : mat x⁻¹ = (mat x)⁻¹ := by
  unfold mat
  rw [Subgroup.coe_inv]
  exact Matrix.GeneralLinearGroup.coe_inv _

theorem row_of_fix (x : SU4) (i : Fin 4) (hx : x • (Pi.single i 1 : Fin 4 → K) = Pi.single i 1)
    (k : Fin 4) : mat x i k = if i = k then 1 else 0 := by
  have hy : x⁻¹ • (Pi.single i 1 : Fin 4 → K) = Pi.single i 1 := by
    calc x⁻¹ • (Pi.single i 1 : Fin 4 → K) = x⁻¹ • (x • (Pi.single i 1 : Fin 4 → K)) := by rw [hx]
      _ = Pi.single i 1 := inv_smul_smul x _
  have hcol : mat x⁻¹ k i = if k = i then 1 else 0 := by
    have := congrFun hy k
    rw [smul_single_eq] at this
    rw [this, Pi.single_apply]
  have hinv : mat x⁻¹ = LieType.Universal.Unitary.conjTr σ4 (mat x) := by
    rw [mat_inv]
    exact Matrix.inv_eq_left_inv (LieType.Universal.Unitary.mem_SUid.1 x.2).2
  have hconj : σ4 (mat x i k) = σ4 (if i = k then 1 else 0) := by
    have h1 := congrFun (congrFun hinv k) i
    rw [LieType.Universal.Unitary.conjTr, transpose_apply, map_apply] at h1
    rw [hcol] at h1
    rw [← h1]
    by_cases hki : k = i
    · subst hki; simp
    · simp [hki, Ne.symm hki]
  exact σ4.injective hconj

theorem entry_zero_of_mem_centralizer {c : SU4} {d : Fin 4 → K} (hc : mat c = diagonal d)
    {x : SU4} (hx : x ∈ Subgroup.centralizer ({c} : Set SU4)) {i j : Fin 4} (hij : d i ≠ d j) :
    mat x i j = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have h := congrFun (congrFun (congrArg mat hx) i) j
  rw [mat_mul, mat_mul, hc, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : mat x i j * (d j - d i) = 0 := by linear_combination h
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (Ne.symm hij))

theorem diag_entry_ne_zero {c : SU4} {d : Fin 4 → K} (hc : mat c = diagonal d) {k : Fin 4}
    (hk : ∀ j, j ≠ k → d j ≠ d k) {x : SU4} (hx : x ∈ Subgroup.centralizer ({c} : Set SU4)) :
    mat x k k ≠ 0 := by
  intro h0
  have hxi : x⁻¹ ∈ Subgroup.centralizer ({c} : Set SU4) := Subgroup.inv_mem _ hx
  have h1 : (mat x * mat x⁻¹) k k = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k] at h1
  · rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro j _ hjk
    rw [entry_zero_of_mem_centralizer hc hx (hk j hjk).symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

@[expose] noncomputable def diagChar {c : SU4} {d : Fin 4 → K} (hc : mat c = diagonal d)
    {k : Fin 4} (hk : ∀ j, j ≠ k → d j ≠ d k) :
    ↥(Subgroup.centralizer ({c} : Set SU4)) →* Kˣ where
  toFun x := Units.mk0 (mat (x : SU4) k k) (diag_entry_ne_zero hc hk x.2)
  map_one' := by
    apply Units.ext
    simp [mat_one]
  map_mul' x y := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, Subgroup.coe_mul]
    rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single k]
    · intro j _ hjk
      rw [entry_zero_of_mem_centralizer hc x.2 (hk j hjk).symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h

theorem W0_entry (x : SU4) (h2 : x • (Pi.single 2 1 : Fin 4 → K) = Pi.single 2 1)
    (h3 : x • (Pi.single 3 1 : Fin 4 → K) = Pi.single 3 1) (i j : Fin 4)
    (hij : i = 2 ∨ i = 3 ∨ j = 2 ∨ j = 3) : mat x i j = if i = j then 1 else 0 := by
  rcases hij with rfl | rfl | rfl | rfl
  · rw [row_of_fix x 2 h2 j]
  · rw [row_of_fix x 3 h3 j]
  · have := congrFun h2 i
    rw [smul_single_eq] at this
    rw [this, Pi.single_apply]
  · have := congrFun h3 i
    rw [smul_single_eq] at this
    rw [this, Pi.single_apply]

theorem W0_le_centralizer_c211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    W0 ≤ Subgroup.centralizer ({c211 ζ hζ} : Set SU4) := by
  intro x hx
  rw [mem_W0_iff] at hx
  obtain ⟨h2, h3⟩ := hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_eq_of_mat_eq
  rw [mat_mul, mat_mul, mat_c211 ζ hζ]
  have hzero : ∀ i j : Fin 4, (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) i ≠
      (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) j → mat x i j = 0 := by
    intro i j hij
    have hcase : i = 2 ∨ i = 3 ∨ j = 2 ∨ j = 3 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rw [W0_entry x h2 h3 i j hcase, if_neg]
    rintro rfl
    exact hij rfl
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) i = (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) j
  · rw [hij, mul_comm]
  · rw [hzero i j hij]
    simp

theorem c211_eig_ne (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    (∀ j, j ≠ (2 : Fin 4) → (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) j ≠ (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) 2)
      ∧ (∀ j, j ≠ (3 : Fin 4) → (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) j ≠
          (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) 3) := by
  have hne1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hne0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have a1 : (1 : K) ≠ ζ := fun h => hne1 h.symm
  have a2 : ζ ^ 2 ≠ ζ := by
    intro h
    have : ζ * (ζ - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact hne0 h0
    · exact hne1 (sub_eq_zero.1 h0)
  have a3 : (1 : K) ≠ ζ ^ 2 := by
    intro h
    apply hne1
    linear_combination h3 + ζ * h
  have a4 : ζ ≠ ζ ^ 2 := fun h => a2 h.symm
  constructor
  · intro j hj
    fin_cases j
    · exact a1
    · exact a1
    · exact absurd rfl hj
    · exact a2
  · intro j hj
    fin_cases j
    · exact a3
    · exact a3
    · exact a4
    · exact absurd rfl hj

theorem goodCent_c211 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : GoodCent (c211 ζ hζ) := by
  intro I hI
  obtain ⟨hk2, hk3⟩ := c211_eig_ne ζ hζ
  have hd := mat_c211 ζ hζ
  have hperf : ⁅I.subgroupOf (Subgroup.centralizer ({c211 ζ hζ} : Set SU4)),
      I.subgroupOf (Subgroup.centralizer ({c211 ζ hζ} : Set SU4))⁆ =
      I.subgroupOf (Subgroup.centralizer ({c211 ζ hζ} : Set SU4)) := by
    apply Subgroup.map_injective (f := (Subgroup.centralizer ({c211 ζ hζ} : Set SU4)).subtype)
      (Subgroup.centralizer ({c211 ζ hζ} : Set SU4)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hI.1]
    exact glaPComponent_perfect hI
  have hk2' := le_ker_of_perfect (diagChar hd hk2) hperf
  have hk3' := le_ker_of_perfect (diagChar hd hk3) hperf
  have hIW0 : I ≤ W0 := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({c211 ζ hζ} : Set SU4) := hI.1 hx
    have hmem : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({c211 ζ hζ} : Set SU4))) ∈
        I.subgroupOf (Subgroup.centralizer ({c211 ζ hζ} : Set SU4)) :=
      Subgroup.mem_subgroupOf.2 hx
    have e2 : mat x 2 2 = 1 := by
      have h := MonoidHom.mem_ker.1 (hk2' hmem)
      have h' := congrArg Units.val h
      exact h'
    have e3 : mat x 3 3 = 1 := by
      have h := MonoidHom.mem_ker.1 (hk3' hmem)
      have h' := congrArg Units.val h
      exact h'
    rw [mem_W0_iff]
    constructor
    · funext k
      rw [smul_single_eq, Pi.single_apply]
      by_cases hk : k = 2
      · subst hk
        rw [e2, if_pos rfl]
      · rw [entry_zero_of_mem_centralizer hd hxC (hk2 k hk), if_neg hk]
    · funext k
      rw [smul_single_eq, Pi.single_apply]
      by_cases hk : k = 3
      · subst hk
        rw [e3, if_pos rfl]
      · rw [entry_zero_of_mem_centralizer hd hxC (hk3 k hk), if_neg hk]
  have hsub : CFSG.Open.IsSubnormal I W0 := by
    have h := hI.2.1.inf_of_le (W0_le_centralizer_c211 ζ hζ)
    rwa [inf_eq_left.2 hIW0] at h
  haveI := isSimpleGroup_W0
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub isSimpleGroup_W0 with h | h
  · exact absurd h (glaPComponent_ne_bot' hI)
  · rw [h]
    obtain ⟨e⟩ := pSimple_equiv_of_simple W0 not_isMulCommutative_W0 three_dvd_W0
    rw [CFSG.LocalAnalysis.GLTheoremA.kLevel_congr 3 e]
    exact kLevel_W0_le_two

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
