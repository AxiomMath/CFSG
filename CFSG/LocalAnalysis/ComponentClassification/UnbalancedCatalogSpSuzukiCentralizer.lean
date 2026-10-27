module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Ree.SuzukiOrder

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Blueprint CFSG.LieType.Ree CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

namespace SpChain

variable {K : Type} [Field K]

theorem minorMap_map (σ : K →+* K) (g : Matrix (Fin 4) (Fin 4) K) :
    minorMap (g.map σ) = (minorMap g).map σ := by
  ext A B
  simp only [minorMap_apply, Matrix.map_apply, map_sub, map_mul]

theorem minorMap_map_pow [CharP K 2] (n : ℕ) (g : Matrix (Fin 4) (Fin 4) K) :
    minorMap (g.map (· ^ 2 ^ n)) = (minorMap g).map (· ^ 2 ^ n) := by
  have h : (fun x : K => x ^ 2 ^ n) = iterateFrobenius K 2 n :=
    funext fun x => (iterateFrobenius_def (p := 2) n x).symm
  rw [h, minorMap_map]

variable {m : ℕ} [CharP K 2] [Finite K]

theorem suzukiGroup_le_antiSp (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    suzukiGroup m K ≤ antiSp K :=
  fun _ hg => (mem_minorFixGroup.mp (suzukiGroup_le_minorFixGroup m hK hg)).1

omit [CharP K 2] [Finite K] in
theorem mem_suzukiGroup_iff_minorMap (hK : Nat.card K = 2 ^ (2 * m + 1)) (g : antiSp K) :
    (g : GL (Fin 4) K) ∈ suzukiGroup m K ↔
      minorMap (glMat (g : GL (Fin 4) K)) = (glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ (m + 1)) := by
  obtain ⟨-, hchar⟩ := suzuki_exterior_square_matrix_characterization m hK
  rw [← SetLike.mem_coe, hchar]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem eta_apply_eq_iff (hK : Nat.card K = 2 ^ (2 * m + 1)) (g : antiSp K) :
    (minorAut K ^ (2 * m + 1)) g = g ↔ (g : GL (Fin 4) K) ∈ suzukiGroup m K := by
  have hq := pow_card_suzuki m hK
  have hη : glMat ((minorAut K ^ (2 * m + 1)) g : GL (Fin 4) K) =
      (minorMap (glMat (g : GL (Fin 4) K))).map (· ^ 2 ^ m) := by
    rw [glMat_eta, minorMap_map_pow]
  rw [mem_suzukiGroup_iff_minorMap hK]
  constructor
  · intro h
    have h1 := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h
    simp only [hη] at h1
    have h2 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map (· ^ 2 ^ (m + 1))) h1
    simp only [Matrix.map_map] at h2
    rw [← h2]
    ext i j
    simp only [Matrix.map_apply, Function.comp_apply]
    rw [← pow_mul, ← pow_add, show m + (m + 1) = 2 * m + 1 by ring, hq]
  · intro h
    apply antiSp_ext
    rw [hη, h, Matrix.map_map]
    ext i j
    simp only [Matrix.map_apply, Function.comp_apply]
    rw [← pow_mul, ← pow_add, show m + 1 + m = 2 * m + 1 by ring, hq]

theorem glMat_minorAut_pow_of_mem (hK : Nat.card K = 2 ^ (2 * m + 1)) (j : ℕ) {g : antiSp K}
    (hg : (g : GL (Fin 4) K) ∈ suzukiGroup m K) :
    glMat ((minorAut K ^ j) g : GL (Fin 4) K) =
      (glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ ((m + 1) * j)) := by
  induction j with
  | zero =>
    ext i j
    simp
  | succ j ih =>
    have hfix : ((minorAut K ^ j) g : GL (Fin 4) K) ∈ suzukiGroup m K := by
      rw [← eta_apply_eq_iff hK] at hg ⊢
      rw [← MulAut.mul_apply, ← pow_add, add_comm, pow_add, MulAut.mul_apply, hg]
    rw [pow_succ', MulAut.mul_apply, glMat_minorAut, (mem_suzukiGroup_iff_minorMap hK _).mp hfix,
      ih, Matrix.map_map]
    ext i j
    simp only [Matrix.map_apply, Function.comp_apply]
    rw [← pow_mul, ← pow_add]
    congr 2

theorem exceptionalSpAut_eq_congr :
    exceptionalSpAut K = MulAut.congr (antiSpEquiv K) (minorAut K) :=
  MulEquiv.ext fun _ => rfl

theorem exceptionalSpAut_pow_apply (j : ℕ) (g : antiSp K) :
    (exceptionalSpAut K ^ j) (antiSpEquiv K g) = antiSpEquiv K ((minorAut K ^ j) g) := by
  rw [exceptionalSpAut_eq_congr, ← map_pow]
  change antiSpEquiv K ((minorAut K ^ j) ((antiSpEquiv K).symm (antiSpEquiv K g))) = _
  rw [MulEquiv.symm_apply_apply]

theorem exceptionalAut_pow_mul_spInner (j : ℕ) (s : StatedSp 2 K) :
    exceptionalAut K ^ j * spInner 2 K s =
      spInner 2 K ((exceptionalSpAut K ^ j) s) * exceptionalAut K ^ j := by
  induction j generalizing s with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, exceptionalAut_mul_spInner, mul_assoc,
      pow_succ' (exceptionalSpAut K), MulAut.mul_apply]

theorem spInner_mem_centralizer_eta_iff (hK : Nat.card K = 2 ^ (2 * m + 1))
    (s : StatedSp 2 K) :
    spInner 2 K s ∈ Subgroup.centralizer {exceptionalAut K ^ (2 * m + 1)} ↔
      (((antiSpEquiv K).symm s : antiSp K) : GL (Fin 4) K) ∈ suzukiGroup m K := by
  have key : spInner 2 K s * exceptionalAut K ^ (2 * m + 1) =
      exceptionalAut K ^ (2 * m + 1) * spInner 2 K s ↔
        (exceptionalSpAut K ^ (2 * m + 1)) s = s := by
    rw [exceptionalAut_pow_mul_spInner]
    constructor
    · intro h
      exact (spInner_injective (mul_right_cancel h)).symm
    · intro h
      rw [h]
  rw [Subgroup.mem_centralizer_singleton_iff, key, ← eta_apply_eq_iff hK]
  conv_lhs => rw [← (antiSpEquiv K).apply_symm_apply s]
  rw [exceptionalSpAut_pow_apply, (antiSpEquiv K).injective.eq_iff]

variable (K m) in
@[expose] def suzukiInner (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    suzukiGroup m K →* MulAut (StatedProj (StatedSp 2 K)) :=
  (spInner 2 K).comp
    ((antiSpEquiv K).toMonoidHom.comp (Subgroup.inclusion (suzukiGroup_le_antiSp hK)))

theorem suzukiInner_apply (hK : Nat.card K = 2 ^ (2 * m + 1)) (g : suzukiGroup m K) :
    suzukiInner K m hK g = spInner 2 K (antiSpEquiv K ⟨g, suzukiGroup_le_antiSp hK g.2⟩) :=
  rfl

theorem suzukiInner_injective (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Function.Injective (suzukiInner K m hK) :=
  spInner_injective.comp ((antiSpEquiv K).injective.comp (Subgroup.inclusion_injective _))

theorem spInner_mem_range_suzukiInner_iff (hK : Nat.card K = 2 ^ (2 * m + 1))
    (s : StatedSp 2 K) :
    spInner 2 K s ∈ (suzukiInner K m hK).range ↔
      (((antiSpEquiv K).symm s : antiSp K) : GL (Fin 4) K) ∈ suzukiGroup m K := by
  constructor
  · rintro ⟨g, hg⟩
    rw [suzukiInner_apply] at hg
    rw [← spInner_injective hg, MulEquiv.symm_apply_apply]
    exact g.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [suzukiInner_apply]
    congr 1
    exact (antiSpEquiv K).apply_symm_apply s

theorem inner_inf_centralizer_eta (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    inner (StatedProj (StatedSp 2 K)) ⊓ Subgroup.centralizer {exceptionalAut K ^ (2 * m + 1)} =
      (suzukiInner K m hK).range := by
  ext α
  constructor
  · rintro ⟨hαI, hαC⟩
    rw [← range_spInner] at hαI
    obtain ⟨s, rfl⟩ := hαI
    exact (spInner_mem_range_suzukiInner_iff hK s).mpr
      ((spInner_mem_centralizer_eta_iff hK s).mp hαC)
  · rintro ⟨g, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨spInner_mem_inner _, ?_⟩
    rw [suzukiInner_apply, spInner_mem_centralizer_eta_iff hK, MulEquiv.symm_apply_apply]
    exact g.2

theorem exceptionalAut_mem_centralizer_eta :
    exceptionalAut K ∈ Subgroup.centralizer {exceptionalAut K ^ (2 * m + 1)} := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← pow_succ, ← pow_succ']

theorem centralizer_eta (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Subgroup.centralizer {exceptionalAut K ^ (2 * m + 1)} =
      (suzukiInner K m hK).range ⊔ Subgroup.zpowers (exceptionalAut K) := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨-, hfac, -⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  apply le_antisymm
  · intro α hα
    obtain ⟨⟨s, j⟩, hsj, -⟩ := hfac α
    have hγj : exceptionalAut K ^ (j : ℕ) ∈
        Subgroup.centralizer {exceptionalAut K ^ (2 * m + 1)} :=
      Subgroup.pow_mem _ exceptionalAut_mem_centralizer_eta _
    have hs : spInner 2 K s ∈ Subgroup.centralizer {exceptionalAut K ^ (2 * m + 1)} := by
      have h : spInner 2 K s = α * (exceptionalAut K ^ (j : ℕ))⁻¹ := by
        rw [hsj]
        group
      rw [h]
      exact mul_mem hα (inv_mem hγj)
    rw [hsj]
    refine mul_mem (Subgroup.mem_sup_left ?_)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
    exact (spInner_mem_range_suzukiInner_iff hK s).mpr
      ((spInner_mem_centralizer_eta_iff hK s).mp hs)
  · refine sup_le ?_ (Subgroup.zpowers_le.mpr exceptionalAut_mem_centralizer_eta)
    rw [← inner_inf_centralizer_eta hK]
    exact inf_le_right

theorem exceptionalAut_conj_mem_range (hK : Nat.card K = 2 ^ (2 * m + 1))
    {n : MulAut (StatedProj (StatedSp 2 K))} (hn : n ∈ (suzukiInner K m hK).range) :
    exceptionalAut K * n * (exceptionalAut K)⁻¹ ∈ (suzukiInner K m hK).range := by
  rw [← inner_inf_centralizer_eta hK] at hn ⊢
  obtain ⟨hnI, hnC⟩ := Subgroup.mem_inf.mp hn
  exact Subgroup.mem_inf.mpr ⟨(inner_normal _).conj_mem n hnI _,
    mul_mem (mul_mem exceptionalAut_mem_centralizer_eta hnC)
      (inv_mem exceptionalAut_mem_centralizer_eta)⟩

omit [CharP K 2] [Finite K] in
theorem eq_scalar_of_commute {M : Matrix (Fin 4) (Fin 4) K}
    (hA : M * !![1, 0, 0, 0; 1, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 1] =
      !![1, 0, 0, 0; 1, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 1] * M)
    (hW : M * suzukiW K = suzukiW K * M) : M = Matrix.scalar (Fin 4) (M 0 0) := by
  have e := fun i j => congrFun (congrFun hA i) j
  have w := fun i j => congrFun (congrFun hW i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_four, suzukiW_eq] at e w
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  have e32 := e 3 2
  have w13 := w 1 3
  have w23 := w 2 3
  have w33 := w 3 3
  have w32 := w 3 2
  have w31 := w 3 1
  simp at e00 e01 e02 e10 e11 e12 e20 e21 e22 e32 w13 w23 w33 w32 w31
  have h03 : M 0 3 = 0 := e02
  have h02 : M 0 2 = 0 := by linear_combination e01 - h03
  have h01 : M 0 1 = 0 := by linear_combination e00 - h03
  have h13 : M 1 3 = 0 := by linear_combination e12 + h02
  have h12 : M 1 2 = 0 := by linear_combination e11 + h01 - h13
  have h11 : M 1 1 = M 0 0 := by linear_combination e10 - h13
  have h23 : M 2 3 = 0 := by linear_combination e22 + h12
  have h22 : M 2 2 = M 0 0 := by linear_combination e21 - h23 + h11
  have h33 : M 3 3 = M 0 0 := by linear_combination e32 + h02 + h12 + h22
  have h10 : M 1 0 = 0 := by linear_combination w13 + h23
  have h21 : M 2 1 = 0 := by linear_combination e20 - h23 + h10
  have h20 : M 2 0 = 0 := by linear_combination w23 + h13
  have h30 : M 3 0 = 0 := by linear_combination w33 + h03
  have h31 : M 3 1 = 0 := by linear_combination w32 + h02
  have h32 : M 3 2 = 0 := by linear_combination w31 + h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31,
      h32, h33]

omit [Finite K] in
theorem eq_one_of_scalar {g : antiSp K} {c : K}
    (hc : glMat (g : GL (Fin 4) K) = Matrix.scalar (Fin 4) c) : g = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hJ := congrFun (congrFun (mem_antiSp.mp g.2) 0) 3
  rw [hc, transpose_mul_minorJ_mul_apply] at hJ
  simp [minorJ_apply] at hJ
  have hc1 : (c - 1) ^ 2 = 0 := by linear_combination hJ - (c - 1) * h2
  have hc' : c = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc1
    linear_combination this
  apply antiSp_ext
  rw [hc, hc']
  ext i j
  simp [Matrix.one_apply]

variable (m) in
abbrev suzukiAG (hK : Nat.card K = 2 ^ (2 * m + 1)) : antiSp K :=
  ⟨(suzukiSElt m K 1 0 : GL (Fin 4) K), suzukiGroup_le_antiSp hK (suzukiSElt m K 1 0).2⟩

variable (m) in
abbrev suzukiWG (hK : Nat.card K = 2 ^ (2 * m + 1)) : antiSp K :=
  ⟨(suzukiWElt m K : GL (Fin 4) K), suzukiGroup_le_antiSp hK (suzukiWElt m K).2⟩

omit [CharP K 2] [Finite K] in
theorem suzukiS_one_zero :
    suzukiS m (1 : K) 0 = !![1, 0, 0, 0; 1, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 1] := by
  have hθ0 : (2 ^ (m + 1) : ℕ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN, zero_pow hθ0]

theorem minorAut_suzukiAG (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    minorAut K (suzukiAG m hK) = suzukiAG m hK := by
  apply antiSp_ext
  rw [glMat_minorAut]
  change minorMap (suzukiS m 1 0) = suzukiS m 1 0
  obtain ⟨-, -, hθθ, -⟩ := suzuki_frobenius_exponents m K hK
  rw [minorMap_suzukiS m hθθ, suzukiS_one_zero]
  have hθ0 : (2 ^ (m + 1) : ℕ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zero_pow hθ0]

theorem minorAut_suzukiWG (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    minorAut K (suzukiWG m hK) = suzukiWG m hK := by
  apply antiSp_ext
  rw [glMat_minorAut]
  change minorMap (suzukiW K) = suzukiW K
  rw [minorMap_suzukiW m]
  have hθ0 : (2 ^ (m + 1) : ℕ) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, zero_pow hθ0]

theorem minorAut_pow_apply_of_fixed {g : antiSp K} (hg : minorAut K g = g) (j : ℕ) :
    (minorAut K ^ j) g = g := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, MulAut.mul_apply, hg, ih]

theorem exceptionalAut_pow_commute {g : antiSp K} (hg : minorAut K g = g) (j : ℕ) :
    exceptionalAut K ^ j * spInner 2 K (antiSpEquiv K g) =
      spInner 2 K (antiSpEquiv K g) * exceptionalAut K ^ j := by
  rw [exceptionalAut_pow_mul_spInner, exceptionalSpAut_pow_apply, minorAut_pow_apply_of_fixed hg]

theorem commute_of_mul_pow_commute {g : antiSp K} (hg : minorAut K g = g) {s : StatedSp 2 K}
    {j : ℕ} (h : spInner 2 K (antiSpEquiv K g) * (spInner 2 K s * exceptionalAut K ^ j) =
      spInner 2 K s * exceptionalAut K ^ j * spInner 2 K (antiSpEquiv K g)) :
    glMat (g : GL (Fin 4) K) * glMat (((antiSpEquiv K).symm s : antiSp K) : GL (Fin 4) K) =
      glMat (((antiSpEquiv K).symm s : antiSp K) : GL (Fin 4) K) * glMat (g : GL (Fin 4) K) := by
  have h1 : spInner 2 K (antiSpEquiv K g) * spInner 2 K s =
      spInner 2 K s * spInner 2 K (antiSpEquiv K g) := by
    have h' : spInner 2 K (antiSpEquiv K g) * spInner 2 K s * exceptionalAut K ^ j =
        spInner 2 K s * spInner 2 K (antiSpEquiv K g) * exceptionalAut K ^ j :=
      calc spInner 2 K (antiSpEquiv K g) * spInner 2 K s * exceptionalAut K ^ j
          _ = spInner 2 K (antiSpEquiv K g) * (spInner 2 K s * exceptionalAut K ^ j) :=
            mul_assoc _ _ _
          _ = spInner 2 K s * (exceptionalAut K ^ j * spInner 2 K (antiSpEquiv K g)) := by
            rw [h, mul_assoc]
          _ = spInner 2 K s * spInner 2 K (antiSpEquiv K g) * exceptionalAut K ^ j := by
            rw [exceptionalAut_pow_commute hg j, mul_assoc]
    exact mul_right_cancel h'
  rw [← map_mul, ← map_mul] at h1
  have h3 := congrArg (antiSpEquiv K).symm (spInner_injective h1)
  rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h3
  have h4 := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h3
  simpa only [Subgroup.coe_mul, Units.val_mul] using h4

theorem centralizer_range_suzukiInner (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Subgroup.centralizer ((suzukiInner K m hK).range :
      Set (MulAut (StatedProj (StatedSp 2 K)))) =
        Subgroup.zpowers (exceptionalAut K ^ (2 * m + 1)) := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨-, hfac, -⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  apply le_antisymm
  · intro α hα
    rw [Subgroup.mem_centralizer_iff] at hα
    obtain ⟨⟨s, j⟩, hsj, -⟩ := hfac α
    have hA := hα _ ⟨suzukiSElt m K 1 0, rfl⟩
    have hW := hα _ ⟨suzukiWElt m K, rfl⟩
    rw [suzukiInner_apply, hsj] at hA hW
    have hA' := commute_of_mul_pow_commute (minorAut_suzukiAG hK) hA
    have hW' := commute_of_mul_pow_commute (minorAut_suzukiWG hK) hW
    have ht : (antiSpEquiv K).symm s = 1 := by
      refine eq_one_of_scalar (eq_scalar_of_commute ?_ ?_)
      · rw [← suzukiS_one_zero (m := m)]
        exact hA'.symm
      · exact hW'.symm
    have hs : s = 1 := by
      rw [← (antiSpEquiv K).apply_symm_apply s, ht, map_one]
    rw [hs, map_one, one_mul] at hsj
    subst hsj
    have hfixu : ∀ u : K, u ^ 2 ^ ((m + 1) * (j : ℕ)) = u := by
      intro u
      have h1 := hα _ ⟨suzukiSElt m K u 0, rfl⟩
      rw [suzukiInner_apply, exceptionalAut_pow_mul_spInner, exceptionalSpAut_pow_apply] at h1
      have h3 := (antiSpEquiv K).injective (spInner_injective (mul_right_cancel h1))
      have h4 := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K) 1 0) h3
      simp only at h4
      rw [glMat_minorAut_pow_of_mem hK _ (suzukiSElt m K u 0).2] at h4
      simpa [coe_suzukiSElt, suzukiS] using h4.symm
    have hFrpow : Fr ^ ((m + 1) * (j : ℕ)) = 1 :=
      RingEquiv.ext fun u => by rw [SpChain.ringAut_pow_apply_of_sq hFr, hfixu]; rfl
    have hdvd := orderOf_dvd_of_pow_eq_one hFrpow
    rw [hord] at hdvd
    have hcop : Nat.Coprime (2 * m + 1) (m + 1) := by
      rw [show 2 * m + 1 = m + (m + 1) by ring, Nat.coprime_add_self_left,
        Nat.coprime_self_add_right]
      exact Nat.coprime_one_right m
    obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
    rw [hk, pow_mul]
    exact Subgroup.npow_mem_zpowers _ k
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro n hn
    rw [← inner_inf_centralizer_eta hK] at hn
    exact Subgroup.mem_centralizer_singleton_iff.mp hn.2

theorem mulAut_mul_conj_mul_inv {P : Type*} [Group P] (α : MulAut P) (x : P) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

variable (K m) in
@[expose] def etaProductHom : etaProduct K m →* MulAut (StatedProj (StatedSp 2 K)) :=
  SemidirectProduct.lift ((spInner 2 K).comp (antiSpEquiv K).toMonoidHom)
    ((MulAut.congr ((antiSpEquiv K).trans (projSpEquiv K))).toMonoidHom.comp
      (Subgroup.zpowers (minorAut K ^ (2 * m + 1))).subtype)
    fun ε => by
      refine MonoidHom.ext fun g => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [MulAut.conj_apply, spInner_eq_conj, spInner_eq_conj, mulAut_mul_conj_mul_inv]
      change MulAut.conj (proj 2 K (antiSpEquiv K ((ε : MulAut (antiSp K)) g))) =
        MulAut.conj (((antiSpEquiv K).trans (projSpEquiv K)) ((ε : MulAut (antiSp K))
          (((antiSpEquiv K).trans (projSpEquiv K)).symm
            (((antiSpEquiv K).trans (projSpEquiv K)) g))))
      rw [MulEquiv.symm_apply_apply]
      rfl

theorem etaProductHom_inl (g : antiSp K) :
    etaProductHom K m (SemidirectProduct.inl g) = spInner 2 K (antiSpEquiv K g) := by
  rw [etaProductHom, SemidirectProduct.lift_inl]
  rfl

theorem etaProductHom_inr_eta :
    etaProductHom K m (SemidirectProduct.inr ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩) =
      exceptionalAut K ^ (2 * m + 1) := by
  rw [etaProductHom, SemidirectProduct.lift_inr, MonoidHom.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, map_pow, ← exceptionalAut_eq_congr]

theorem oddCore_inf_centralizer_eta (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {H : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hIH : inner (StatedProj (StatedSp 2 K)) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {exceptionalAut K ^ (2 * m + 1)}) = ⊥ := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨hγord, -⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  set N := (suzukiInner K m hK).range with hNdef
  have hNIC := inner_inf_centralizer_eta hK
  rw [← hNdef] at hNIC
  refine oddCore_eq_bot_of_centralizer (N := N)
    (le_inf ((hNIC ▸ inf_le_left).trans hIH) (hNIC ▸ inf_le_right)) ?_ ?_ ?_
  · intro c hc n hn
    rw [← hNIC] at hn ⊢
    obtain ⟨hnI, hnC⟩ := Subgroup.mem_inf.mp hn
    have hcC := (Subgroup.mem_inf.mp hc).2
    exact Subgroup.mem_inf.mpr ⟨(inner_normal _).conj_mem n hnI c,
      mul_mem (mul_mem hcC hnC) (inv_mem hcC)⟩
  · intro X hXN hXn hodd
    obtain ⟨-, -, hsimple⟩ := suzuki_simple hm hK
    set Y := X.comap (suzukiInner K m hK) with hYdef
    have hYn : Y.Normal := ⟨fun y hy g => by
      change suzukiInner K m hK (g * y * g⁻¹) ∈ X
      rw [map_mul, map_mul, map_inv]
      exact hXn _ ⟨g, rfl⟩ _ hy⟩
    have := hsimple
    have := hYn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with hY | hY
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨g, rfl⟩ := hXN hx
      have hg : g ∈ Y := hx
      rw [hY, Subgroup.mem_bot] at hg
      rw [hg, map_one]
      exact one_mem _
    · exfalso
      have hXeq : X = N := le_antisymm hXN fun n ⟨g, hg⟩ => hg ▸ (show g ∈ Y from hY ▸ trivial)
      have hcard : Nat.card X = Nat.card (suzukiGroup m K) := by
        rw [hXeq, hNdef]
        exact Nat.card_congr (MonoidHom.ofInjective (suzukiInner_injective hK)).toEquiv.symm
      rw [hcard, suzuki_order hK] at hodd
      have heven : Even ((2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) *
          ((2 ^ (2 * m + 1)) ^ 2 + 1)) := by
        refine Even.mul_right (Even.mul_right ?_ _) _
        exact Even.pow_of_ne_zero (Even.pow_of_ne_zero even_two (by omega)) (by norm_num)
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  · intro c hc hcN
    have hcC : c ∈ Subgroup.centralizer (N : Set (MulAut (StatedProj (StatedSp 2 K)))) :=
      Subgroup.mem_centralizer_iff.mpr fun n hn => (hcN n hn).symm
    rw [centralizer_range_suzukiInner hK] at hcC
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcC
    refine ⟨1, ?_⟩
    have hη2 : (exceptionalAut K ^ (2 * m + 1)) ^ 2 = 1 := by
      rw [← pow_mul, show (2 * m + 1) * 2 = 2 * (2 * m + 1) by ring, ← hγord, pow_orderOf_eq_one]
    have hcomm : ((exceptionalAut K ^ (2 * m + 1)) ^ k) ^ 2 =
        ((exceptionalAut K ^ (2 * m + 1)) ^ 2) ^ k := by
      rw [← zpow_natCast ((exceptionalAut K ^ (2 * m + 1)) ^ k) 2,
        ← zpow_natCast (exceptionalAut K ^ (2 * m + 1)) 2, ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm k]
    rw [pow_one, hcomm, hη2, _root_.one_zpow]

theorem oddCore_inf_centralizer_eq_bot (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {H : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hIH : inner (StatedProj (StatedSp 2 K)) ≤ H) {a : MulAut (StatedProj (StatedSp 2 K))}
    (ha : orderOf a = 2) (haI : a ∉ inner (StatedProj (StatedSp 2 K))) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {a}) = ⊥ := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨hγord, -, -, -, -, -, -, -, -, hinvol⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  obtain ⟨s, j, hj, hsj⟩ := hinvol a ha
  have hjf : j = 2 * m + 1 := hj.resolve_left fun h => haI (by
    rw [hsj, h, pow_zero, mul_one]
    exact spInner_mem_inner s)
  subst hjf
  set ηG : Subgroup.zpowers (minorAut K ^ (2 * m + 1)) :=
    ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩ with hηG
  set u := (antiSpEquiv K).symm s with hu
  set x : etaProduct K m := SemidirectProduct.inl u * SemidirectProduct.inr ηG with hx
  have hΘx : etaProductHom K m x = a := by
    rw [hx, map_mul, etaProductHom_inl, hηG, etaProductHom_inr_eta, hu,
      MulEquiv.apply_symm_apply, hsj]
  have hxr : x.right = ηG := by
    rw [hx, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      one_mul]
  have hγ2f : exceptionalAut K ^ (2 * (2 * m + 1)) = 1 := by rw [← hγord, pow_orderOf_eq_one]
  have hu1 : u * (minorAut K ^ (2 * m + 1)) u = 1 := by
    have hsq := pow_orderOf_eq_one a
    rw [ha] at hsq
    have hγ2 : exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1) = 1 := by
      rw [← pow_add, ← two_mul, hγ2f]
    have key : a * a = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) :=
      calc a * a = spInner 2 K s * (exceptionalAut K ^ (2 * m + 1) * spInner 2 K s) *
            exceptionalAut K ^ (2 * m + 1) := by rw [hsj]; simp only [mul_assoc]
        _ = spInner 2 K s * spInner 2 K ((exceptionalSpAut K ^ (2 * m + 1)) s) *
            (exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1)) := by
          rw [exceptionalAut_pow_mul_spInner]
          simp only [mul_assoc]
        _ = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) := by
          rw [hγ2, mul_one, map_mul]
    have h1 : s * (exceptionalSpAut K ^ (2 * m + 1)) s = 1 :=
      spInner_injective (by rw [← key, ← sq, hsq, map_one])
    have hs : s = antiSpEquiv K u := by rw [hu, MulEquiv.apply_symm_apply]
    rw [hs, exceptionalSpAut_pow_apply, ← map_mul] at h1
    exact (antiSpEquiv K).injective (h1.trans (map_one _).symm)
  have hxl : x.left = u := by
    simp only [hx, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inl, map_one, mul_one]
  have hx2 : x ^ 2 = 1 := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [sq, SemidirectProduct.mul_left, hxr, hxl, SemidirectProduct.one_left]
      exact hu1
    · rw [sq, SemidirectProduct.mul_right, hxr, SemidirectProduct.one_right]
      have h := pow_orderOf_eq_one (minorAut K ^ (2 * m + 1))
      rw [orderOf_eta m hK] at h
      exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, h]; rfl)
  obtain ⟨h, hh⟩ := eta_involution_conj m hK x hxr hx2
  have hconj := congrArg (etaProductHom K m) hh
  rw [map_mul, map_mul, map_inv, hΘx, etaProductHom_inl, etaProductHom_inr_eta] at hconj
  set b := spInner 2 K (antiSpEquiv K h)
  have hbH : b ∈ H := hIH (spInner_mem_inner _)
  have ha' : a = b⁻¹ * exceptionalAut K ^ (2 * m + 1) * b⁻¹⁻¹ := by
    rw [← hconj]
    group
  rw [ha']
  exact oddCore_centralizer_conj_eq_bot (inv_mem hbH) (oddCore_inf_centralizer_eta hm hK hIH)

end SpChain

open SpChain

theorem even_symplectic_two_suzuki_full_centralizer_odd_core {m : ℕ} (hm : 1 ≤ m) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1))
    (γ : MulAut (StatedProj (StatedSp 2 K)))
    (hγ : ∀ g : StatedSp 2 K, γ (proj 2 K g) = proj 2 K (exceptionalSpAut K g)) :
    ∃ φ : suzukiGroup m K →* MulAut (StatedProj (StatedSp 2 K)),
      (∀ g : suzukiGroup m K, ∃ s : StatedSp 2 K,
        spMat s = Matrix.reindex stdIdx.symm stdIdx.symm
          (swapC K * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (swapC K)⁻¹) ∧
        φ g = spInner 2 K s) ∧
      Function.Injective φ ∧
      orderOf (γ ^ (2 * m + 1)) = 2 ∧
      φ.range = inner (StatedProj (StatedSp 2 K)) ⊓ Subgroup.centralizer {γ ^ (2 * m + 1)} ∧
      Subgroup.centralizer {γ ^ (2 * m + 1)} = φ.range ⊔ Subgroup.zpowers γ ∧
      φ.range ⊓ Subgroup.zpowers γ = ⊥ ∧
      (∀ n ∈ φ.range, γ * n * γ⁻¹ ∈ φ.range) ∧
      Subgroup.centralizer (φ.range : Set (MulAut (StatedProj (StatedSp 2 K)))) =
        Subgroup.zpowers (γ ^ (2 * m + 1)) ∧
      ∀ H : Subgroup (MulAut (StatedProj (StatedSp 2 K))),
        inner (StatedProj (StatedSp 2 K)) ≤ H → ∀ a ∈ H, orderOf a = 2 →
          a ∉ inner (StatedProj (StatedSp 2 K)) →
            CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {a}) = ⊥ := by
  obtain rfl := eq_exceptionalAut hγ
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨hγord, -, hinf, -⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  refine ⟨suzukiInner K m hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact ⟨antiSpEquiv K ⟨g, suzukiGroup_le_antiSp hK g.2⟩, spMat_antiSpEquiv_eq_conj _,
      suzukiInner_apply hK g⟩
  · exact suzukiInner_injective hK
  · rw [orderOf_pow' _ (by omega), hγord, Nat.gcd_eq_right (Dvd.intro_left 2 rfl)]
    exact Nat.mul_div_cancel 2 (by omega)
  · exact (inner_inf_centralizer_eta hK).symm
  · exact centralizer_eta hK
  · rw [eq_bot_iff, ← hinf]
    refine inf_le_inf_right _ ?_
    rw [← inner_inf_centralizer_eta hK]
    exact inf_le_left
  · exact fun n hn => exceptionalAut_conj_mem_range hK hn
  · exact centralizer_range_suzukiInner hK
  · exact fun H hIH a _ ha haI => oddCore_inf_centralizer_eq_bot hm hK hIH ha haI

end CFSG.ComponentClassification.UnbalancedCatalog
