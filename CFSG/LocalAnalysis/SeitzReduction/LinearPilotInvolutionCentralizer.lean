module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerLevi
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.Quasithin (perfectCore)

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

theorem isPerfect_specialLinearGroup_of_four_le [Finite K] (hK : 4 ≤ Nat.card K) (ι : Type*)
    [Fintype ι] [DecidableEq ι] : Group.IsPerfect (SpecialLinearGroup ι K) := by
  set m := Fintype.card ι
  have hFin : Group.IsPerfect (SpecialLinearGroup (Fin m) K) := by
    rcases (by omega : m ≤ 1 ∨ m = 2 ∨ 3 ≤ m) with h | h | h
    · have : Subsingleton (SpecialLinearGroup (Fin m) K) := by
        refine ⟨fun A B => Matrix.SpecialLinearGroup.ext A B fun i j => ?_⟩
        have hm : m = 1 := by have := i.2; omega
        have hij : i = j := Fin.ext (by have := i.2; have := j.2; omega)
        subst hij
        have hA := A.2
        have hB := B.2
        have : Unique (Fin m) := hm ▸ inferInstance
        rw [det_unique] at hA hB
        rw [Subsingleton.elim i default, hA, hB]
      infer_instance
    · rw [h]
      exact CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
    · exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le h
  exact Group.IsPerfect.ofSurjective
    (f := (reindexSpecialLinear (K := K) (Fintype.equivFin ι).symm).toMonoidHom)
    (MulEquiv.surjective _)

theorem eq_one_of_mem_scalars_of_mul_self [CharP K 2] {z : SpecialLinearGroup (Fin n) K}
    (hz : z ∈ LinearFlag.scalars n K) (h2 : z * z = 1) : z = 1 := by
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hz
  ext i j
  have hii := congrFun (congrFun (congrArg (fun X : SpecialLinearGroup (Fin n) K =>
    (X : Matrix (Fin n) (Fin n) K)) h2) i) i
  simp only [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_one,
    scalar_apply, diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at hii
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : ((c : K) + 1) * ((c : K) + 1) = 0 := by linear_combination hii + ((c : K) + 1) * h2K
  have h4 : (c : K) + 1 = 0 := mul_self_eq_zero.1 h3
  have hc1 : (c : K) = 1 := by linear_combination h4 - h2K
  rw [hc, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem commute_of_proj_commute [CharP K 2] {A B : SpecialLinearGroup (Fin n) K}
    (hA : A * A = 1)
    (h : LinearFlag.proj n K B * LinearFlag.proj n K A =
      LinearFlag.proj n K A * LinearFlag.proj n K B) : B * A = A * B := by
  have h1 : LinearFlag.proj n K (B * A) = LinearFlag.proj n K (A * B) := by
    rw [map_mul, map_mul, h]
  rw [LinearFlag.proj_eq_proj_iff] at h1
  set z := (B * A)⁻¹ * (A * B) with hzdef
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    LinearFlag.scalars_le_center n K h1
  have hcomm : ∀ x, z * x = x * z := fun x => (Subgroup.mem_center_iff.1 hzc x).symm
  have hAB : A * B = B * A * z := by rw [hzdef, mul_inv_cancel_left]
  have hzz : z * z = 1 := by
    have e1 : B = A * (A * B) := by rw [← mul_assoc, hA, one_mul]
    have e2 : A * (A * B) = B * (z * z) := by
      calc A * (A * B) = A * (B * A * z) := by rw [hAB]
        _ = (A * B) * A * z := by simp only [mul_assoc]
        _ = B * A * z * A * z := by rw [hAB]
        _ = B * A * (z * A) * z := by simp only [mul_assoc]
        _ = B * A * (A * z) * z := by rw [hcomm A]
        _ = B * (A * A) * (z * z) := by simp only [mul_assoc]
        _ = B * (z * z) := by rw [hA, mul_one]
    have e3 : B * (z * z) = B * 1 := by rw [mul_one, ← e2, ← e1]
    exact mul_left_cancel e3
  have hz1 : z = 1 := eq_one_of_mem_scalars_of_mul_self h1 hzz
  rw [hAB, hz1, mul_one]

theorem centralizer_proj_eq_map [CharP K 2] {A : SpecialLinearGroup (Fin n) K} (hA : A * A = 1) :
    Subgroup.centralizer {LinearFlag.proj n K A} =
      (Subgroup.centralizer {A}).map (LinearFlag.proj n K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨B, rfl⟩ := LinearFlag.proj_surjective n K x
    refine ⟨B, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    exact commute_of_proj_commute hA (Subgroup.mem_centralizer_singleton_iff.1 hx)
  · rintro _ ⟨B, hB, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hB]

theorem transvection_mul_self [CharP K 2] {i j : Fin n} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hij c = 1 := by
  rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

variable (K) in
@[expose] def elt : LinearFlag.projectiveSL n K :=
  LinearFlag.proj n K (P.mat K)

variable (K) in
@[expose] def radicalP : Subgroup (LinearFlag.projectiveSL n K) :=
  (P.radical K).map (LinearFlag.proj n K)

variable (K) in
@[expose] noncomputable def leviOneP : Subgroup (LinearFlag.projectiveSL n K) :=
  (P.leviOne K).map (LinearFlag.proj n K)

theorem mat_mem_blockSpecialLinear_outer : P.mat K ∈ blockSpecialLinear P.outer := by
  intro i j hij
  rw [coe_mat, Matrix.add_apply]
  have : P.nil K i j = 0 := by
    rcases hij with h | h
    · by_cases hi : P.level i = 0
      · exact absurd (P.mem_outer.2 ⟨Sum.inl (P.level_eq_zero_iff.1 hi).choose,
          (P.level_eq_zero_iff.1 hi).choose_spec⟩) h
      · exact P.nil_apply_of_ne_zero hi
    · by_cases hj : P.level j = 2
      · exact absurd (P.mem_outer.2 ⟨Sum.inr (P.level_eq_two_iff.1 hj).choose,
          (P.level_eq_two_iff.1 hj).choose_spec⟩) h
      · exact P.nil_apply_of_ne_two hj
  rw [this, add_zero]

theorem elt_mem_blockSL {I : Finset (Fin n)} (h : P.outer ⊆ I) : P.elt K ∈ blockSL I :=
  proj_mem_blockSL (blockSpecialLinear_mono h P.mat_mem_blockSpecialLinear_outer)

theorem centralizer_elt [CharP K 2] : Subgroup.centralizer {P.elt K} =
    (Subgroup.centralizer {P.mat K}).map (LinearFlag.proj n K) :=
  centralizer_proj_eq_map P.mat_mul_self

theorem levi_le_blockDiag : P.leviOne K ⊔ blockSpecialLinear P.free ≤ P.blockDiag K :=
  sup_le P.leviOne_le_blockDiag P.blockSpecialLinear_free_le_blockDiag

theorem map_levi_eq : (P.leviOne K ⊔ blockSpecialLinear P.free).map (LinearFlag.proj n K) =
    P.leviOneP K ⊔ blockSL P.free := by
  rw [Subgroup.map_sup]
  rfl

theorem map_core_eq : (P.core K).map (LinearFlag.proj n K) =
    P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) := by
  rw [core, Subgroup.map_sup, map_levi_eq]
  rfl

theorem perfectCore_centralizer_elt [CharP K 2] [Group.IsPerfect (SpecialLinearGroup (Fin k) K)]
    [Group.IsPerfect (SpecialLinearGroup P.free K)] (hJ : 2 ≤ P.free.card) :
    perfectCore (Subgroup.centralizer {P.elt K}) =
      P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) := by
  rw [P.centralizer_elt, ← map_core_eq]
  refine perfectCore_eq_of_perfect_of_commutator_le (Subgroup.map_mono P.core_le_centralizer) ?_ ?_
  · rw [← Subgroup.map_commutator, P.commutator_core hJ]
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono P.commutator_centralizer_le_core

theorem perfectCore_centralizer_elt_eq_commutator [CharP K 2]
    [Group.IsPerfect (SpecialLinearGroup (Fin k) K)] [Group.IsPerfect (SpecialLinearGroup P.free K)]
    (hJ : 2 ≤ P.free.card) :
    perfectCore (Subgroup.centralizer {P.elt K}) =
      ⁅Subgroup.centralizer {P.elt K}, Subgroup.centralizer {P.elt K}⁆ := by
  refine le_antisymm ?_ ?_
  · calc perfectCore (Subgroup.centralizer {P.elt K})
        ≤ CFSG.Quasithin.derivedSeriesOf (Subgroup.centralizer {P.elt K}) 1 :=
          CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1
      _ = _ := by rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero]
  · rw [P.perfectCore_centralizer_elt hJ, ← map_core_eq, P.centralizer_elt,
      ← Subgroup.map_commutator]
    exact Subgroup.map_mono P.commutator_centralizer_le_core

theorem radical_pow_four [CharP K 2] {r : SpecialLinearGroup (Fin n) K} (hr : r ∈ P.radical K) :
    r ^ 4 = 1 := by
  set X := (r : Matrix (Fin n) (Fin n) K) - 1 with hX
  have hX0 : ∀ i j, P.level j ≤ P.level i → X i j = 0 := fun i j h => by
    rw [hX, Matrix.sub_apply, hr i j h, sub_self]
  have hXX : ∀ i j, ¬ (P.level i = 0 ∧ P.level j = 2) → (X * X) i j = 0 := by
    intro i j hij
    rw [mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : P.level l ≤ P.level i
    · rw [hX0 i l h1, zero_mul]
    · by_cases h2 : P.level j ≤ P.level l
      · rw [hX0 l j h2, mul_zero]
      · exfalso
        have := P.level_le_two j
        omega
  have hX4 : X * X * (X * X) = 0 := by
    ext i j
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : P.level i = 0 ∧ P.level l = 2
    · rw [hXX l j (fun h' => by omega), mul_zero]
    · rw [hXX i l h, zero_mul]
  have hsq : ∀ Y : Matrix (Fin n) (Fin n) K, (1 + Y) * (1 + Y) = 1 + Y * Y := by
    intro Y
    rw [show (1 + Y) * (1 + Y) = 1 + (Y + Y) + Y * Y by noncomm_ring,
      show Y + Y = 0 by ext i j; rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply],
      add_zero]
  have hr' : (r : Matrix (Fin n) (Fin n) K) = 1 + X := by
    rw [hX]
    abel
  have h2 : (1 + X) ^ 2 = 1 + X * X := by rw [sq, hsq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hr',
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq, hsq, hX4, add_zero]

theorem isPGroup_radical [CharP K 2] : IsPGroup 2 (P.radical K) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact P.radical_pow_four g.2

theorem isPGroup_radicalP [CharP K 2] : IsPGroup 2 (P.radicalP K) :=
  P.isPGroup_radical.map _

theorem disjoint_radicalP : Disjoint (P.radicalP K) (P.leviOneP K ⊔ blockSL P.free) := by
  rw [← map_levi_eq, Subgroup.disjoint_def]
  rintro x ⟨r, hr, rfl⟩ ⟨m, hm, hrm⟩
  rw [LinearFlag.proj_eq_proj_iff] at hrm
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hrm
  have hr' : r = m * (m⁻¹ * r) := (mul_inv_cancel_left m r).symm
  have hrD : r ∈ P.blockDiag K := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [hr', Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, mul_diagonal,
        P.levi_le_blockDiag hm i j hij, zero_mul]
    · rw [hr i j h.le, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
  rw [P.eq_one_of_mem_radical_of_mem_blockDiag hr hrD, map_one]

theorem levi_le_normalizer_radicalP :
    P.leviOneP K ⊔ blockSL P.free ≤
      Subgroup.normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) := by
  rw [← map_levi_eq]
  exact (Subgroup.map_mono ((P.levi_le_blockDiag.trans P.blockDiag_le_parabolic).trans
    P.parabolic_le_normalizer_radical)).trans (Subgroup.le_normalizer_map _)

theorem commute_leviOneP_blockSL :
    ∀ x ∈ P.leviOneP K, ∀ y ∈ blockSL (K := K) P.free, Commute x y := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨d, hd, rfl⟩
  exact (P.commute_leviOne_free ha hd).map _

theorem regionPart_mul_radical {r r' : SpecialLinearGroup (Fin n) K} (hr : r ∈ P.radical K)
    (hr' : r' ∈ P.radical K) (α : ℕ) :
    P.regionPart K α (α + 1) ((r * r' : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      P.regionPart K α (α + 1) r + P.regionPart K α (α + 1) r' := by
  ext i j
  rw [Matrix.add_apply, regionPart_apply, regionPart_apply, regionPart_apply]
  split_ifs with h
  · have hij : i ≠ j := by
      rintro rfl
      omega
    rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Finset.sum_eq_add i j hij]
    · rw [hr i i le_rfl, hr' j j le_rfl, one_apply_eq, one_apply_eq, one_mul, mul_one, add_comm]
    · intro l _ hl
      by_cases h1 : P.level l ≤ P.level i
      · rw [hr i l h1, one_apply_ne (Ne.symm hl.1), zero_mul]
      · rw [hr' l j (by omega), one_apply_ne hl.2, mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
    · intro h'
      exact absurd (Finset.mem_univ j) h'
  · rw [add_zero]

variable (K) in
@[expose] def radicalAb : P.radical K →* Multiplicative (Matrix (Fin n) (Fin n) K) where
  toFun r := Multiplicative.ofAdd (P.regionPart K 0 1 r + P.regionPart K 1 2 r)
  map_one' := by
    rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, P.regionPart_one (by norm_num),
      P.regionPart_one (by norm_num), add_zero, ofAdd_zero]
  map_mul' r r' := by
    rw [Subgroup.coe_mul, ← ofAdd_add, P.regionPart_mul_radical r.2 r'.2 0,
      P.regionPart_mul_radical r.2 r'.2 1]
    congr 1
    abel

theorem commutator_radical_le :
    ⁅P.radical K, P.radical K⁆ ≤ blockSpecialLinear P.outer := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have hg : ⁅g₁, g₂⁆ ∈ P.radical K := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hφ : P.radicalAb K ⁅(⟨g₁, h₁⟩ : P.radical K), ⟨g₂, h₂⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have hsum : P.regionPart K 0 1 (⁅g₁, g₂⁆ : SpecialLinearGroup (Fin n) K) +
      P.regionPart K 1 2 (⁅g₁, g₂⁆ : SpecialLinearGroup (Fin n) K) = 0 := hφ
  intro i j hij
  have hi' : P.level i = 1 ∨ P.level j = 1 := by
    rcases hij with h | h
    · exact Or.inl (P.mem_free.1 (by
        rw [free_eq_compl, Finset.mem_compl]
        exact h))
    · exact Or.inr (P.mem_free.1 (by
        rw [free_eq_compl, Finset.mem_compl]
        exact h))
  by_cases hle : P.level j ≤ P.level i
  · exact hg i j hle
  · have hne : i ≠ j := by
      rintro rfl
      exact hle le_rfl
    rw [one_apply_ne hne]
    have := congrFun (congrFun hsum i) j
    rw [Matrix.add_apply, regionPart_apply, regionPart_apply, Matrix.zero_apply] at this
    have hj2 := P.level_le_two j
    rcases hi' with h | h
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), zero_add] at this
      exact this
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), add_zero] at this
      exact this

theorem transvection_u_w_mem_commutator (hJ : P.free.Nonempty) (a b : Fin k) (c : K) :
    SpecialLinearGroup.transvection (P.u_ne_w a b) c ∈ ⁅P.radical K, P.radical K⁆ := by
  obtain ⟨l, hl⟩ := hJ
  have hl1 := P.mem_free.1 hl
  have hul : P.u a ≠ l := fun h => P.u_not_mem_free a (h ▸ hl)
  have hlw : l ≠ P.w b := fun h => P.w_not_mem_free b (h ▸ hl)
  have hcomm :=
    Matrix.SpecialLinearGroup.commutatorElement_transvection hul hlw (P.u_ne_w a b) c (1 : K)
  rw [mul_one] at hcomm
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator
    (P.transvection_mem_radical hul (by rw [level_u, hl1]; omega) c)
    (P.transvection_mem_radical hlw (by rw [level_w, hl1]; omega) 1)

theorem commute_submatrix_u_of_commute {m : SpecialLinearGroup (Fin n) K}
    (hm : ∀ a b, m * SpecialLinearGroup.transvection (P.u_ne_w a b) 1 =
      SpecialLinearGroup.transvection (P.u_ne_w a b) 1 * m) (Y : Matrix (Fin k) (Fin k) K) :
    Commute ((m : Matrix (Fin n) (Fin n) K).submatrix P.u P.u) Y := by
  have hent : ∀ a a' b, (m : Matrix (Fin n) (Fin n) K) (P.u a') (P.u a) =
      if a' = a then (m : Matrix (Fin n) (Fin n) K) (P.w b) (P.w b) else 0 := by
    intro a a' b
    have h := congrFun (congrFun (congrArg (fun X : SpecialLinearGroup (Fin n) K =>
      (X : Matrix (Fin n) (Fin n) K)) (hm a b)) (P.u a')) (P.w b)
    simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
      add_right_inj, mul_single_apply_same, mul_one] at h
    rw [h]
    by_cases ha : a' = a
    · subst ha
      rw [single_mul_apply_same, one_mul, ite_eq_left rfl]
    · rw [single_mul_apply_of_ne (h := fun h' => ha (P.u_injective h')), ite_eq_right ha]
  have hdiag : ∀ x z : Fin k, (m : Matrix (Fin n) (Fin n) K) (P.u x) (P.u x) =
      (m : Matrix (Fin n) (Fin n) K) (P.u z) (P.u z) := by
    intro x z
    rw [hent x x z, hent z z z, ite_eq_left rfl, ite_eq_left rfl]
  ext x z
  simp only [mul_apply, submatrix_apply]
  rw [Finset.sum_eq_single x, Finset.sum_eq_single z]
  · rw [hdiag x z, mul_comm]
  · intro y _ hyz
    rw [hent z y z, ite_eq_right hyz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ z) h
  · intro y _ hyx
    rw [hent y x x, ite_eq_right (Ne.symm hyx), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ x) h

variable (K) in
@[expose] noncomputable def blockU : P.parabolic K →* Matrix (Fin k) (Fin k) K where
  toFun B := ((B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u
  map_one' := by
    show ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = 1
    rw [Matrix.SpecialLinearGroup.coe_one, submatrix_one _ P.u_injective]
  map_mul' B B' := by
    show (((B : SpecialLinearGroup (Fin n) K) * B' : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).submatrix P.u P.u = _
    rw [Matrix.SpecialLinearGroup.coe_mul,
      P.submatrix_mul_u (P.mem_parabolic.1 B.2) (P.mem_parabolic.1 B'.2)]

theorem map_commutatorElement_eq_one_of_commute {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {x y : G} (h : Commute (f x) (f y)) : f ⁅x, y⁆ = 1 := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, h.eq, mul_assoc (f y) (f x),
    ← map_mul, mul_inv_cancel, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

variable (K) in
@[expose] noncomputable def leviHom :
    SpecialLinearGroup (Fin k) K × SpecialLinearGroup P.free K →* SpecialLinearGroup (Fin n) K :=
  (P.leviOneHom K).noncommCoprod (blockEmbed P.free)
    fun a d => P.commute_leviOne_free ⟨a, rfl⟩ (P.blockEmbed_free_mem d)

theorem range_leviHom : (P.leviHom K).range = P.leviOne K ⊔ blockSpecialLinear P.free := by
  rw [leviHom, MonoidHom.noncommCoprod_range, range_blockEmbed]
  rfl

theorem blockU_leviHom (a : SpecialLinearGroup (Fin k) K) (d : SpecialLinearGroup P.free K) :
    ((P.leviHom K (a, d) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
      P.u P.u = a := by
  rw [leviHom, MonoidHom.noncommCoprod_apply, Matrix.SpecialLinearGroup.coe_mul,
    P.submatrix_mul_u (P.mem_parabolic.1 (P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag a)))
      (P.mem_parabolic.1 (P.blockDiag_le_parabolic
        (P.blockSpecialLinear_free_le_blockDiag (P.blockEmbed_free_mem d)))),
    submatrix_u_leviOneHom, submatrix_u_blockEmbed_free, Matrix.mul_one]

theorem blockSL_free_eq_perfectCore [CharP K 2] [Group.IsPerfect (SpecialLinearGroup P.free K)]
    (hJ : P.free.Nonempty) :
    blockSL P.free = perfectCore ((P.leviOneP K ⊔ blockSL P.free) ⊓
      Subgroup.centralizer ((⁅P.radicalP K, P.radicalP K⁆ :
        Subgroup (LinearFlag.projectiveSL n K)) : Set (LinearFlag.projectiveSL n K))) := by
  symm
  refine perfectCore_eq_of_perfect_of_commutator_le ?_ ?_ ?_
  · refine le_inf le_sup_right ?_
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [radicalP, ← Subgroup.map_commutator] at hz
    obtain ⟨g, hg, rfl⟩ := hz
    have := commute_blockSpecialLinear_of_disjoint P.disjoint_outer_free
      (P.commutator_radical_le hg) hd
    rw [← map_mul, ← map_mul, this.eq]
  · have : Group.IsPerfect (blockSpecialLinear (K := K) P.free) := by
      rw [← range_blockEmbed]
      exact Group.IsPerfect.range _
    rw [blockSL, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  · rw [Subgroup.commutator_le]
    have key : ∀ x ∈ (P.leviOneP K ⊔ blockSL P.free) ⊓ Subgroup.centralizer
        ((⁅P.radicalP K, P.radicalP K⁆ : Subgroup (LinearFlag.projectiveSL n K)) :
          Set (LinearFlag.projectiveSL n K)),
        ∃ m ∈ P.leviOne K ⊔ blockSpecialLinear P.free, LinearFlag.proj n K m = x ∧
          ∀ Y, Commute ((m : Matrix (Fin n) (Fin n) K).submatrix P.u P.u) Y := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [← map_levi_eq] at hx1
      obtain ⟨m, hm, rfl⟩ := hx1
      refine ⟨m, hm, rfl, P.commute_submatrix_u_of_commute (fun a b => ?_)⟩
      have ht : LinearFlag.proj n K (SpecialLinearGroup.transvection (P.u_ne_w a b) (1 : K)) ∈
          ⁅P.radicalP K, P.radicalP K⁆ := by
        rw [radicalP, ← Subgroup.map_commutator]
        exact Subgroup.mem_map_of_mem _ (P.transvection_u_w_mem_commutator hJ a b 1)
      have := (Subgroup.mem_centralizer_iff.1 hx2) _ ht
      exact commute_of_proj_commute (transvection_mul_self _ _) this.symm
    intro x hx x' hx'
    obtain ⟨m, hm, rfl, hmY⟩ := key x hx
    obtain ⟨m', hm', rfl, -⟩ := key x' hx'
    have hmP : m ∈ P.parabolic K :=
      P.blockDiag_le_parabolic (P.levi_le_blockDiag hm)
    have hmP' : m' ∈ P.parabolic K :=
      P.blockDiag_le_parabolic (P.levi_le_blockDiag hm')
    have hU : P.blockU K ⁅(⟨m, hmP⟩ : P.parabolic K), ⟨m', hmP'⟩⁆ = 1 :=
      map_commutatorElement_eq_one_of_commute _ (hmY _)
    have hc : ⁅m, m'⁆ ∈ P.leviOne K ⊔ blockSpecialLinear P.free := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hm hm') (inv_mem hm)) (inv_mem hm')
    rw [← P.range_leviHom] at hc
    obtain ⟨⟨a, d⟩, had⟩ := hc
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← P.blockU_leviHom a d, had, Matrix.SpecialLinearGroup.coe_one]
      exact hU
    rw [← map_commutatorElement, ← had, ha]
    refine proj_mem_blockSL ?_
    rw [leviHom, MonoidHom.noncommCoprod_apply, map_one, one_mul]
    exact P.blockEmbed_free_mem d

theorem centralizer_inv_perfectCore [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hJ : 2 ≤ n - 2 * k) :
    IsPGroup 2 (P.radicalP K) ∧
      perfectCore (Subgroup.centralizer {P.elt K}) =
        P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) ∧
      Disjoint (P.radicalP K) (P.leviOneP K ⊔ blockSL P.free) ∧
      P.leviOneP K ⊔ blockSL P.free ≤
        Subgroup.normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) ∧
      blockSL P.free = perfectCore ((P.leviOneP K ⊔ blockSL P.free) ⊓
        Subgroup.centralizer ((⁅P.radicalP K, P.radicalP K⁆ :
          Subgroup (LinearFlag.projectiveSL n K)) : Set (LinearFlag.projectiveSL n K))) := by
  have := isPerfect_specialLinearGroup_of_four_le hq (Fin k)
  have := isPerfect_specialLinearGroup_of_four_le hq P.free
  have hJ' : 2 ≤ P.free.card := by rw [card_free]; exact hJ
  exact ⟨P.isPGroup_radicalP, P.perfectCore_centralizer_elt hJ', P.disjoint_radicalP,
    P.levi_le_normalizer_radicalP,
    P.blockSL_free_eq_perfectCore (Finset.card_pos.1 (by omega))⟩

end InvPlacement

theorem centralizer_inv_perfectCore_exists {n k : ℕ} {K : Type*} [Field K] [Finite K]
    [CharP K 2] (hq : 4 ≤ Nat.card K) (P : InvPlacement n k) (hJ : 2 ≤ n - 2 * k) :
    ∃ (Q M₁ : Subgroup (LinearFlag.projectiveSL n K)) (J : Finset (Fin n)),
      J.card = n - 2 * k ∧ IsPGroup 2 Q ∧
      perfectCore (Subgroup.centralizer {P.elt K}) = Q ⊔ (M₁ ⊔ blockSL J) ∧
      Disjoint Q (M₁ ⊔ blockSL J) ∧
      M₁ ⊔ blockSL J ≤ Subgroup.normalizer (Q : Set (LinearFlag.projectiveSL n K)) ∧
      blockSL J = perfectCore ((M₁ ⊔ blockSL J) ⊓
        Subgroup.centralizer ((⁅Q, Q⁆ : Subgroup (LinearFlag.projectiveSL n K)) :
          Set (LinearFlag.projectiveSL n K))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := P.centralizer_inv_perfectCore hq hJ
  exact ⟨P.radicalP K, P.leviOneP K, P.free, P.card_free, h1, h2, h3, h4, h5⟩

end CFSG.SeitzReduction.LinearPilot
