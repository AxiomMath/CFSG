module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotAutUCenter
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {m : ℕ}

section Siegel

theorem transpose_mul_mul_transpose (A : Matrix (Fin m) (Fin m) K) {C : Matrix (Fin m) (Fin m) K}
    (hC : Cᵀ = C) : (A * C * Aᵀ)ᵀ = A * C * Aᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]

theorem upperUnipotentSp_congr {C C' : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C) (hC' : C'ᵀ = C')
    (h : C = C') : upperUnipotentSp m K hC = upperUnipotentSp m K hC' := by
  subst h
  rfl

theorem upperUnipotentSp_inv {C : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C) :
    (upperUnipotentSp m K hC)⁻¹ =
      upperUnipotentSp m K (C := -C) (by rw [transpose_neg, hC]) := by
  rw [inv_eq_iff_mul_eq_one, upperUnipotentSp_mul, ← upperUnipotentSp_zero (m := m) (K := K)]
  exact upperUnipotentSp_congr _ _ (add_neg_cancel C)

theorem upperUnipotentSp_commute {C C' : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C)
    (hC' : C'ᵀ = C') :
    upperUnipotentSp m K hC * upperUnipotentSp m K hC' =
      upperUnipotentSp m K hC' * upperUnipotentSp m K hC := by
  rw [upperUnipotentSp_mul, upperUnipotentSp_mul]
  exact upperUnipotentSp_congr _ _ (add_comm C C')

theorem leviEmbedGL_conj_upperUnipotentSp (A : GL (Fin m) K) {C : Matrix (Fin m) (Fin m) K}
    (hC : Cᵀ = C) :
    leviEmbedGL K m A * upperUnipotentSp m K hC * (leviEmbedGL K m A)⁻¹ =
      upperUnipotentSp m K (transpose_mul_mul_transpose (A : Matrix (Fin m) (Fin m) K) hC) := by
  apply mat_injective
  rw [← map_inv (leviEmbedGL K m) A, map_mul, map_mul, mat_leviEmbedGL, mat_leviEmbedGL,
    mat_upperUnipotentSp, mat_upperUnipotentSp, fromBlocks_multiply, fromBlocks_multiply, inv_inv]
  have h1 : (A : Matrix (Fin m) (Fin m) K) * ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      1 := Units.mul_inv A
  have h2 : ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ *
      (A : Matrix (Fin m) (Fin m) K)ᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2]

theorem commutatorElement_leviEmbedGL_upperUnipotentSp (A : GL (Fin m) K)
    {C : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C) :
    ⁅leviEmbedGL K m A, upperUnipotentSp m K hC⁆ =
      upperUnipotentSp m K (C := (A : Matrix (Fin m) (Fin m) K) * C *
        (A : Matrix (Fin m) (Fin m) K)ᵀ - C)
        (by rw [transpose_sub, transpose_mul_mul_transpose _ hC, hC]) := by
  rw [commutatorElement_def, leviEmbedGL_conj_upperUnipotentSp, upperUnipotentSp_inv,
    upperUnipotentSp_mul]
  exact upperUnipotentSp_congr _ _ (sub_eq_add_neg _ _).symm

end Siegel

section Families

variable (K) in
@[expose] noncomputable def siegPair (i j : Fin m) (c : K) : StatedSp m K :=
  upperUnipotentSp m K (C := single i j c + single j i c)
    (by rw [transpose_add, transpose_single, transpose_single, add_comm])

variable (K) in
@[expose] noncomputable def siegDiag (i : Fin m) (c : K) : StatedSp m K :=
  upperUnipotentSp m K (C := single i i c) (transpose_single i i c)

variable (K) in
@[expose] noncomputable def leviTv {i j : Fin m} (hij : i ≠ j) (c : K) : StatedSp m K :=
  leviEmbedGL K m (TauCeti.transvectionUnit hij c)

theorem siegDiag_mem_longRootSp2 (i : Fin m) (c : K) : siegDiag K i c ∈ longRootSp2 K m i := by
  rw [siegDiag, ← elt_positiveLong_eq_upperUnipotentSp, longRootSp2_eq_suppGroup, mem_suppGroup]
  intro r t hrt
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt, Matrix.add_apply, Matrix.smul_apply]
  have h0 : CFSG.LieType.Universal.Symplectic.SpExtras.E K (.positiveLong i) r t = 0 := by
    simp only [CFSG.LieType.Universal.Symplectic.SpExtras.E, Matrix.single_apply]
    rw [ite_eq_right_iff.2]
    rintro ⟨rfl, rfl⟩
    exact (hrt ⟨inl_mem_coords i, inr_mem_coords i⟩).elim
  rw [h0, smul_zero, add_zero]

theorem rootTorusHom_eq_leviEmbedGL (k : Fin m) (κ : Kˣ) :
    rootTorusHom K m k κ = leviEmbedGL K m (TauCeti.diagGL (Pi.mulSingle k κ)) := rfl

theorem commutatorElement_rootTorusHom_siegPair {k i : Fin m} (hik : i ≠ k) (κ : Kˣ) (c : K) :
    ⁅rootTorusHom K m k κ, siegPair K k i c⁆ = siegPair K k i (((κ : K) - 1) * c) := by
  rw [rootTorusHom_eq_leviEmbedGL, siegPair, commutatorElement_leviEmbedGL_upperUnipotentSp,
    siegPair]
  refine upperUnipotentSp_congr _ _ ?_
  rw [TauCeti.diagGL_coe, diagonal_transpose]
  ext x y
  simp only [Matrix.sub_apply, Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.single_apply]
  by_cases hx : k = x <;> by_cases hy : i = y <;> by_cases hx' : i = x <;> by_cases hy' : k = y <;>
    subst_vars <;> simp_all <;> ring

theorem commutatorElement_rootTorusHom_leviTv {k i : Fin m} (hik : i ≠ k) (κ : Kˣ) (c : K) :
    ⁅rootTorusHom K m k κ, leviTv K hik c⁆ = leviTv K hik ((((κ⁻¹ : Kˣ) : K) - 1) * c) := by
  rw [rootTorusHom_eq_leviEmbedGL, leviTv, leviTv, commutatorElement_def,
    ← map_inv (leviEmbedGL K m) (TauCeti.diagGL _),
    ← map_inv (leviEmbedGL K m) (TauCeti.transvectionUnit hik c),
    ← map_mul, ← map_mul, ← map_mul, TauCeti.diagGL_mul_transvectionUnit_mul_inv,
    TauCeti.transvectionUnit_inv, ← TauCeti.transvectionUnit_add]
  congr 2
  simp [hik]
  ring

end Families

section Transvection

variable {i k : Fin m}

theorem transvection_mul_mul_transpose_of_forall_eq_zero (c : K)
    {Q : Matrix (Fin m) (Fin m) K} (hrow : ∀ y, Q k y = 0) (hcol : ∀ x, Q x k = 0) :
    transvection i k c * Q * (transvection i k c)ᵀ = Q := by
  have h1 : transvection i k c * Q = Q := by
    rw [transvection, Matrix.add_mul, Matrix.one_mul, add_eq_left]
    ext x y
    by_cases hx : x = i
    · subst hx
      rw [Matrix.single_mul_apply_same, hrow, mul_zero, Matrix.zero_apply]
    · rw [Matrix.single_mul_apply_of_ne (h := hx), Matrix.zero_apply]
  have h2 : Q * (transvection i k c)ᵀ = Q := by
    rw [transvection, transpose_add, transpose_one, transpose_single, Matrix.mul_add,
      Matrix.mul_one, add_eq_left]
    ext x y
    by_cases hy : y = i
    · subst hy
      rw [Matrix.mul_single_apply_same, hcol, zero_mul, Matrix.zero_apply]
    · rw [Matrix.mul_single_apply_of_ne (hbj := hy), Matrix.zero_apply]
  rw [h1, h2]

theorem transvection_mul_pair_mul_transpose {j : Fin m} (hjk : j ≠ k) (c b : K) :
    transvection i k c * (single k j b + single j k b) * (transvection i k c)ᵀ =
      single i j (c * b) + single j i (c * b) + (single k j b + single j k b) := by
  rw [transvection, transpose_add, transpose_one, transpose_single]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same, ne_eq, hjk, hjk.symm, not_false_eq_true, single_mul_single_of_ne,
    add_zero, zero_add]
  rw [mul_comm b c]
  abel

theorem transvection_mul_diag_mul_transpose (c b : K) :
    transvection i k c * single k k b * (transvection i k c)ᵀ =
      single i k (c * b) + single k i (c * b) + single i i (c * c * b) + single k k b := by
  rw [transvection, transpose_add, transpose_one, transpose_single]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same]
  rw [mul_comm b c, mul_assoc c b c, mul_comm b c, ← mul_assoc]
  abel

theorem leviTv_commute_upperUnipotentSp (hik : i ≠ k) (c : K) {Q : Matrix (Fin m) (Fin m) K}
    (hQ : Qᵀ = Q) (hrow : ∀ y, Q k y = 0) (hcol : ∀ x, Q x k = 0) :
    leviTv K hik c * upperUnipotentSp m K hQ = upperUnipotentSp m K hQ * leviTv K hik c := by
  have h := leviEmbedGL_conj_upperUnipotentSp (TauCeti.transvectionUnit hik c) hQ
  rw [TauCeti.coe_transvectionUnit] at h
  have h' : upperUnipotentSp m K (transpose_mul_mul_transpose (transvection i k c) hQ) =
      upperUnipotentSp m K hQ :=
    upperUnipotentSp_congr _ _ (transvection_mul_mul_transpose_of_forall_eq_zero c hrow hcol)
  rw [← mul_inv_eq_iff_eq_mul, leviTv, h, h']

theorem commutatorElement_leviTv_siegPair (hik : i ≠ k) {j : Fin m} (hjk : j ≠ k) (c b : K) :
    ⁅leviTv K hik c, siegPair K k j b⁆ = siegPair K i j (c * b) := by
  rw [leviTv, siegPair, commutatorElement_leviEmbedGL_upperUnipotentSp, siegPair]
  refine upperUnipotentSp_congr _ _ ?_
  rw [TauCeti.coe_transvectionUnit, transvection_mul_pair_mul_transpose hjk, add_sub_cancel_right]

theorem commutatorElement_leviTv_siegDiag (hik : i ≠ k) (c b : K) :
    ⁅leviTv K hik c, siegDiag K k b⁆ = siegPair K i k (c * b) * siegDiag K i (c * c * b) := by
  rw [leviTv, siegDiag, commutatorElement_leviEmbedGL_upperUnipotentSp, siegPair, siegDiag,
    upperUnipotentSp_mul]
  refine upperUnipotentSp_congr _ _ ?_
  rw [TauCeti.coe_transvectionUnit, transvection_mul_diag_mul_transpose, add_sub_cancel_right]

end Transvection

section Reps

theorem twoCentralElt_eq_siegDiag_mul_siegPair (p q : Fin m) (a b : K) :
    twoCentralElt m p q a b = siegDiag K p a * siegPair K p q b := by
  rw [twoCentralElt, siegDiag, siegPair, upperUnipotentSp_mul]
  exact upperUnipotentSp_congr _ _ (by rw [twoCentralMat, add_assoc])

theorem siegPair_comm (i j : Fin m) (c : K) : siegPair K i j c = siegPair K j i c :=
  upperUnipotentSp_congr _ _ (add_comm _ _)

theorem twoCentralMat_row_eq_zero {p q k : Fin m} (hpk : p ≠ k) (hqk : q ≠ k) (a b : K)
    (y : Fin m) : twoCentralMat p q a b k y = 0 := by
  rw [twoCentralMat_apply]
  simp [hpk, hqk]

theorem twoCentralMat_col_eq_zero {p q k : Fin m} (hpk : p ≠ k) (hqk : q ≠ k) (a b : K)
    (x : Fin m) : twoCentralMat p q a b x k = 0 := by
  rw [twoCentralMat_apply]
  simp [hpk, hqk]

theorem twoCentralElt_mem_complSp {p q k : Fin m} (hpk : p ≠ k) (hqk : q ≠ k) (a b : K) :
    twoCentralElt m p q a b ∈ complSp K k := by
  rw [mem_complSp]
  intro r t hrt
  rw [mat_twoCentralElt]
  rcases r with x | x <;> rcases t with y | y
  · simp [Matrix.one_apply]
  · rw [fromBlocks_apply₁₂, Matrix.one_apply_ne Sum.inl_ne_inr]
    have hxy : x = k ∨ y = k := by
      by_contra h
      push Not at h
      exact hrt ⟨fun hx => h.1 (by simpa [coords] using hx),
        fun hy => h.2 (by simpa [coords] using hy)⟩
    rcases hxy with rfl | rfl
    · exact twoCentralMat_row_eq_zero hpk hqk a b y
    · exact twoCentralMat_col_eq_zero hpk hqk a b x
  · simp
  · simp [Matrix.one_apply]

end Reps

section Perfect

theorem commutator_longRootSp2 [Finite K] (hK : 4 ≤ Nat.card K) (k : Fin m) :
    ⁅longRootSp2 K m k, longRootSp2 K m k⁆ = longRootSp2 K m k := by
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
    exact ⟨s, hs⟩
  have : Group.IsPerfect (StatedSp 1 K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 1 K (Or.inl h4)
  have : Group.IsPerfect SL(2, K) :=
    Group.IsPerfect.ofSurjective (f := (longBlockEquivOne K).symm.toMonoidHom)
      (MulEquiv.surjective _)
  rw [longRootSp2, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem exists_units_ne_one [Finite K] (hK : 4 ≤ Nat.card K) : ∃ κ : Kˣ, κ ≠ 1 := by
  have h : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  have := (Finite.one_lt_card_iff_nontrivial).1 h
  exact exists_ne 1

variable (K) in
@[expose] def centPerfGen {p q k : Fin m} (hpk : p ≠ k) (hqk : q ≠ k) : Set (StatedSp m K) :=
  (longRootSp2 K m k : Set (StatedSp m K)) ∪ Set.range (siegPair K k p) ∪
    Set.range (siegPair K k q) ∪ Set.range (siegPair K p q) ∪ Set.range (siegDiag K p) ∪
    Set.range (siegDiag K q) ∪ Set.range (leviTv K hpk) ∪ Set.range (leviTv K hqk)

variable (K) in
@[expose] def centPerf {p q k : Fin m} (hpk : p ≠ k) (hqk : q ≠ k) : Subgroup (StatedSp m K) :=
  closure (centPerfGen K hpk hqk)

variable {p q k : Fin m} (hpk : p ≠ k) (hqk : q ≠ k)

include hpk hqk in
theorem longRootSp2_le_centPerf : longRootSp2 K m k ≤ centPerf K hpk hqk := fun _ hx =>
  subset_closure (by simp only [centPerfGen, Set.mem_union]; tauto)

include hqk in
theorem siegPair_kp_mem_centPerf (c : K) : siegPair K k p c ∈ centPerf K hpk hqk :=
  subset_closure (by simp only [centPerfGen, Set.mem_union, Set.mem_range]; tauto)

include hpk in
theorem siegPair_kq_mem_centPerf (c : K) : siegPair K k q c ∈ centPerf K hpk hqk :=
  subset_closure (by simp only [centPerfGen, Set.mem_union, Set.mem_range]; tauto)

include hpk hqk in
theorem siegPair_pq_mem_centPerf (c : K) : siegPair K p q c ∈ centPerf K hpk hqk :=
  subset_closure (by simp only [centPerfGen, Set.mem_union, Set.mem_range]; tauto)

include hpk hqk in
theorem siegDiag_p_mem_centPerf (c : K) : siegDiag K p c ∈ centPerf K hpk hqk :=
  subset_closure (by simp only [centPerfGen, Set.mem_union, Set.mem_range]; tauto)

include hpk hqk in
theorem siegDiag_q_mem_centPerf (c : K) : siegDiag K q c ∈ centPerf K hpk hqk :=
  subset_closure (by simp only [centPerfGen, Set.mem_union, Set.mem_range]; tauto)

include hqk in
theorem leviTv_p_mem_centPerf (c : K) : leviTv K hpk c ∈ centPerf K hpk hqk :=
  subset_closure (by simp only [centPerfGen, Set.mem_union, Set.mem_range]; tauto)

include hpk in
theorem leviTv_q_mem_centPerf (c : K) : leviTv K hqk c ∈ centPerf K hpk hqk :=
  subset_closure (by simp only [centPerfGen, Set.mem_union, Set.mem_range]; tauto)

theorem centPerf_le_centralizer (a b : K) :
    centPerf K hpk hqk ≤ centralizer ({twoCentralElt m p q a b} : Set (StatedSp m K)) := by
  have hz : twoCentralElt m p q a b ∈ complSp K k := twoCentralElt_mem_complSp hpk hqk a b
  have hS : ∀ {C : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C),
      upperUnipotentSp m K hC ∈ centralizer ({twoCentralElt m p q a b} : Set (StatedSp m K)) :=
    fun hC => mem_centralizer_singleton_iff.2 (upperUnipotentSp_commute _ _)
  have hL : ∀ {i : Fin m} (hik : i ≠ k) (c : K),
      leviTv K hik c ∈ centralizer ({twoCentralElt m p q a b} : Set (StatedSp m K)) :=
    fun hik c => mem_centralizer_singleton_iff.2 (leviTv_commute_upperUnipotentSp hik c _
      (twoCentralMat_row_eq_zero hpk hqk a b) (twoCentralMat_col_eq_zero hpk hqk a b))
  refine closure_le _ |>.2 fun x hx => ?_
  simp only [centPerfGen, Set.mem_union, Set.mem_range, SetLike.mem_coe] at hx
  rcases hx with ((((((hx | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) |
    ⟨c, rfl⟩
  · exact mem_centralizer_singleton_iff.2 (commute_of_mem_longRootSp2_of_mem_complSp hx hz).eq
  · exact hS _
  · exact hS _
  · exact hS _
  · exact hS _
  · exact hS _
  · exact hL hpk c
  · exact hL hqk c

theorem commutator_centPerf [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅centPerf K hpk hqk, centPerf K hpk hqk⁆ = centPerf K hpk hqk := by
  set P := centPerf K hpk hqk with hP
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK
  have hκ1 : (κ : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hκ (Units.ext h)
  have hκ2 : ((κ⁻¹ : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hκ (inv_eq_one.1 (Units.ext h))
  have hh : rootTorusHom K m k κ ∈ P :=
    longRootSp2_le_centPerf hpk hqk (rootTorusSp_le_longRootSp2 k ⟨κ, rfl⟩)
  have hLR : longRootSp2 K m k ≤ ⁅P, P⁆ := by
    rw [← commutator_longRootSp2 hK k]
    exact commutator_mono (longRootSp2_le_centPerf hpk hqk) (longRootSp2_le_centPerf hpk hqk)
  have hpair : ∀ {i : Fin m} (hik : i ≠ k), (∀ c : K, siegPair K k i c ∈ P) →
      ∀ d : K, siegPair K k i d ∈ ⁅P, P⁆ := by
    intro i hik hmem d
    have e := commutatorElement_rootTorusHom_siegPair hik κ (((κ : K) - 1)⁻¹ * d)
    rw [← mul_assoc, mul_inv_cancel₀ hκ1, one_mul] at e
    rw [← e]
    exact commutator_mem_commutator hh (hmem _)
  have hkp := hpair hpk (siegPair_kp_mem_centPerf hpk hqk)
  have hkq := hpair hqk (siegPair_kq_mem_centPerf hpk hqk)
  have htv : ∀ {i : Fin m} (hik : i ≠ k), (∀ c : K, leviTv K hik c ∈ P) →
      ∀ d : K, leviTv K hik d ∈ ⁅P, P⁆ := by
    intro i hik hmem d
    have e := commutatorElement_rootTorusHom_leviTv hik κ ((((κ⁻¹ : Kˣ) : K) - 1)⁻¹ * d)
    rw [← mul_assoc, mul_inv_cancel₀ hκ2, one_mul] at e
    rw [← e]
    exact commutator_mem_commutator hh (hmem _)
  have hdiag : ∀ {i : Fin m} (hik : i ≠ k), (∀ c : K, leviTv K hik c ∈ P) →
      (∀ d : K, siegPair K k i d ∈ ⁅P, P⁆) → ∀ d : K, siegDiag K i d ∈ ⁅P, P⁆ := by
    intro i hik hmem hpr d
    have e := commutatorElement_leviTv_siegDiag hik 1 d
    rw [one_mul, one_mul, one_mul, siegPair_comm] at e
    have h1 : ⁅leviTv K hik 1, siegDiag K k d⁆ ∈ ⁅P, P⁆ :=
      commutator_mem_commutator (hmem 1)
        (longRootSp2_le_centPerf hpk hqk (siegDiag_mem_longRootSp2 k d))
    rw [e] at h1
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hpr d)) h1
    rwa [inv_mul_cancel_left] at h2
  refine le_antisymm (Subgroup.commutator_le_self _) (closure_le _ |>.2 fun x hx => ?_)
  simp only [centPerfGen, Set.mem_union, Set.mem_range, SetLike.mem_coe] at hx
  rcases hx with ((((((hx | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) |
    ⟨c, rfl⟩
  · exact hLR hx
  · exact hkp c
  · exact hkq c
  · have e := commutatorElement_leviTv_siegPair hpk hqk 1 c
    rw [one_mul] at e
    rw [← e]
    exact commutator_mem_commutator (leviTv_p_mem_centPerf hpk hqk 1)
      (siegPair_kq_mem_centPerf hpk hqk c)
  · exact hdiag hpk (leviTv_p_mem_centPerf hpk hqk) hkp c
  · exact hdiag hqk (leviTv_q_mem_centPerf hpk hqk) hkq c
  · exact htv hpk (leviTv_p_mem_centPerf hpk hqk) c
  · exact htv hqk (leviTv_q_mem_centPerf hpk hqk) c

include hpk hqk in
theorem twoCentralElt_mem_perfectCore_centralizer [Finite K] (hK : 4 ≤ Nat.card K) (a b : K) :
    twoCentralElt m p q a b ∈
      perfectCore (centralizer ({twoCentralElt m p q a b} : Set (StatedSp m K))) := by
  refine le_perfectCore_of_perfect (centPerf_le_centralizer hpk hqk a b)
    (commutator_centPerf hpk hqk hK) ?_
  rw [twoCentralElt_eq_siegDiag_mul_siegPair]
  exact Subgroup.mul_mem _ (siegDiag_p_mem_centPerf hpk hqk a) (siegPair_pq_mem_centPerf hpk hqk b)

end Perfect

theorem spRep_mem_perfectCore_centralizer [Finite K] (hK : 4 ≤ Nat.card K) (n : ℕ)
    (κ : SpTwoCentral) :
    spRep (K := K) n κ ∈
      perfectCore (centralizer ({spRep (K := K) n κ} : Set (StatedSp (n + 3) K))) := by
  have h10 : (1 : Fin (n + 3)) ≠ 0 := by simp
  have h20 : (2 : Fin (n + 3)) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_two, Fin.val_zero] at h'
    omega
  exact twoCentralElt_mem_perfectCore_centralizer h10 h20 hK _ _

end CFSG.SeitzReduction.SymplecticPilot
