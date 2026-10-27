module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisUnitaryArith
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.AGLEmbeddingD2.HeisUnitary

open CFSG.SectionRank CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank

section Rank

variable {K Y : Type*} [Group K] [Group Y]

theorem three_le_pRank_of_indep_five [Finite Y] {π : K →* Y} {J : Subgroup Y} {x y z : K}
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hx5 : x ^ 5 = 1)
    (hy5 : y ^ 5 = 1) (hz5 : z ^ 5 = 1) (hxJ : π x ∈ J) (hyJ : π y ∈ J) (hzJ : π z ∈ J)
    (hind : ∀ a b c : ℕ, x ^ a * y ^ b * z ^ c ∈ π.ker → 5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c) :
    3 ≤ CFSG.Open.pRank 5 J := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set x' : ↥J := ⟨π x, hxJ⟩
  set y' : ↥J := ⟨π y, hyJ⟩
  set z' : ↥J := ⟨π z, hzJ⟩
  have hker : ∀ a b c : ℕ, π x ^ a * π y ^ b * π z ^ c = 1 → 5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c :=
    fun a b c h => hind a b c (by rw [MonoidHom.mem_ker, map_mul, map_mul, map_pow, map_pow,
      map_pow, h])
  have hπ5 : ∀ w : K, w ^ 5 = 1 → π w ^ 5 = 1 := fun w hw => by rw [← map_pow, hw, map_one]
  refine (three_le_pRank_of_gens (G := ↥J) (p := 5) (x := x') (y := y') (z := z')
    (Subtype.ext (hπ5 x hx5)) (Subtype.ext (hπ5 y hy5)) (Subtype.ext (hπ5 z hz5))
    (Subtype.ext (by simp [x', y', ← map_mul, hxy.eq])) (Subtype.ext (by
      simp [x', z', ← map_mul, hxz.eq])) (Subtype.ext (by simp [y', z', ← map_mul, hyz.eq]))
    ?_ ?_ ?_).trans (RealThreeRank.pRank_top_subtype_le 5 (by norm_num) J)
  · intro h
    have h1 : π x = 1 := congrArg Subtype.val h
    have := (hker 1 0 0 (by simp [h1])).1
    omega
  · intro n h
    have h1 : π x ^ n = π y := congrArg Subtype.val h
    have h2 : π x ^ n * π y ^ 4 * π z ^ 0 = 1 := by
      rw [h1, pow_zero, mul_one, ← pow_succ', hπ5 y hy5]
    have := (hker n 4 0 h2).2.1
    omega
  · intro n m h
    have h1 : π x ^ n * π y ^ m = π z := congrArg Subtype.val h
    have h2 : π x ^ n * π y ^ m * π z ^ 4 = 1 := by
      rw [h1, ← pow_succ', hπ5 z hz5]
    have := (hker n m 4 h2).2.2
    omega

end Rank

theorem five_dvd_of_torus_eqs {K : Type*} [Field K] {ω : Kˣ} (hω : orderOf ω = 5) {p q r : ℕ}
    (h1 : ω ^ p = ω⁻¹ ^ p * ω ^ q) (h2 : ω⁻¹ ^ p * ω ^ q = ω⁻¹ ^ q * ω ^ r)
    (h3 : ω⁻¹ ^ q * ω ^ r = ω⁻¹ ^ r) : 5 ∣ p ∧ 5 ∣ q ∧ 5 ∣ r := by
  have hω5 : ω ^ 5 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hi : ω⁻¹ = ω ^ 4 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hω5
  simp only [hi, ← pow_mul, ← pow_add] at h1 h2 h3
  have e1 := pow_eq_pow_iff_modEq.1 h1
  have e2 := pow_eq_pow_iff_modEq.1 h2
  have e3 := pow_eq_pow_iff_modEq.1 h3
  rw [hω] at e1 e2 e3
  simp only [Nat.ModEq] at e1 e2 e3
  omega

section SU

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbeddingD2.SquareGeneric CFSG.LieType.BorelTits
  CFSG.AGLEmbedding.ToralCensus CFSG.AGLEmbeddingD2.ParabRealThree
  CFSG.AGLEmbeddingD2.SquareUnitary Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem exists_levelTorus_pow (a : Fin (n / 2)) {m : ℕ} (ω : Fˣ) (hωm : ω ^ m = 1)
    (hω1 : ω ≠ 1)
    (hc : ¬ a.val + 1 < n / 2 → Even n → unitaryInvolution F 2 f (ω : F) = ω) :
    ∃ x ∈ levelTorus (unitaryInvolution F 2 f) a,
      mat (unitaryInvolution F 2 f) n x = diagonal (tFun (unitaryInvolution F 2 f) a (ω : F)) ∧
        x ^ m = 1 ∧ x ≠ 1 := by
  obtain ⟨x, hxH, hxm⟩ := exists_mem_levelTorus hF a ω hc
  refine ⟨x, hxH, hxm, mat_injective ?_, fun h => hω1 ?_⟩
  · rw [map_pow, hxm, diagonal_pow, tFun_pow a ω.ne_zero, map_one, ← Units.val_pow_eq_pow_val,
      hωm, Units.val_one, tFun_one]
    exact diagonal_one
  · have := congrArg (fun y => mat (unitaryInvolution F 2 f) n y (lowIdx a) (lowIdx a)) h
    simp only [hxm, diagonal_apply_eq, tFun_lowIdx, map_one, one_apply_eq] at this
    exact Units.ext this

include hF in
theorem realOver_torus_su {Y : Type*} [Group Y] {π : SU (unitaryInvolution F 2 f) n →* Y}
    {J : Subgroup Y}
    (hBJ : borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 f)) ≤ J.comap π)
    {a : Fin (n / 2)} (ha : a.val + 1 < n / 2) {ω : Fˣ} (hω5 : ω ^ 5 = 1) (hω1 : ω ≠ 1) :
    HeisEngine.RealOver 5 π (rankOne (rootDatum hF n).rootGroup a) J := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  obtain ⟨x, hxH, hxm, hx5, hx1⟩ :=
    exists_levelTorus_pow hF a ω hω5 hω1 (fun h => absurd ha h)
  have hxL : x ∈ rankOne (rootDatum hF n).rootGroup a :=
    levelTorus_le_rankOne hσ hζ (exists_norm_eq_of_fixed' hF) a hxH
  have hperf : ⁅rankOne (rootDatum hF n).rootGroup a, rankOne (rootDatum hF n).rootGroup a⁆ =
      rankOne (rootDatum hF n).rootGroup a := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      sl2_isPerfect (four_le_card hF)
    have hperfL : Group.IsPerfect ↥(rankOne (rootDatum hF n).rootGroup a) :=
      Group.IsPerfect.ofSurjective
        (f := (rankOneShortEquiv (hσ := hσ) ha).symm.toMonoidHom)
        (rankOneShortEquiv (hσ := hσ) ha).symm.surjective
    exact commutator_eq_self_of_isPerfect hperfL
  refine ⟨x, by rw [hperf]; exact hxL,
    hBJ (le_sup_left (a := ⨆ k, levelTorus (unitaryInvolution F 2 f) k)
      (le_iSup (levelTorus (unitaryInvolution F 2 f)) a hxH)), hx5, ?_, levelWeyl hσ ζ a,
    levelWeyl_mem_rankOne hσ ζ a, levelWeyl_conj_short_torus hσ hζ ha hxm⟩
  intro hz
  have hpq : lowIdx a ≠ lowIdx (n := n) ⟨a.val + 1, ha⟩ := lowIdx_ne_succ ha
  have hqp : lowIdx (n := n) ⟨a.val + 1, ha⟩ ≠ Fin.rev (lowIdx a) := lowIdx_ne_rev _ _
  have hc := Subgroup.mem_center_iff.mp hz
    (rootHom _ hσ hpq (lowIdx_ne_rev a a) (lowIdx_ne_rev _ _) (Multiplicative.ofAdd (1 : F)))
  have h1 := congrArg (fun z => mat (unitaryInvolution F 2 f) n z (lowIdx a)
    (lowIdx (n := n) ⟨a.val + 1, ha⟩)) hc
  simp only [map_mul, hxm, mat_apply, coe_rootHom, toAdd_ofAdd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, rootMatrix_apply_pq hpq hqp, tFun_lowIdx, tFun_succ_idx ha, mul_one,
    one_mul] at h1
  have h2 : ω * ω = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_one]
    nth_rewrite 1 [← h1]
    exact inv_mul_cancel₀ ω.ne_zero)
  apply hω1
  calc ω = ω ^ 5 * ((ω * ω)⁻¹) ^ 2 := by group
    _ = 1 := by rw [hω5, h2, inv_one, one_pow, one_mul]

omit [Finite F] [CharP F 2] in
theorem exists_involutions_sl2 [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ X Y : SpecialLinearGroup (Fin 2) F, X ^ 2 = 1 ∧ Y ^ 2 = 1 ∧ (X * Y) ^ 5 = 1 ∧
      X * Y ≠ 1 := by
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  let X : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let Y : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; ω, 1], by simp [Matrix.det_fin_two_of]⟩
  have hM : (X * Y).val = !![1 + ω, 1; ω, 1] := by
    show X.val * Y.val = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨X, Y, ?_, ?_, ?_, ?_⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (X.val ^ 2) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j
    rw [pow_two]
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h2
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (Y.val ^ 2) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j
    rw [pow_two]
    fin_cases i <;> fin_cases j <;> simp [Y, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination ω * h2
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    show ((X * Y).val ^ 5) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j
    rw [hM]
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (ω ^ 3 + 8 * ω ^ 2 + 19 * ω + 8) * hω + (-6 * ω - 4) * h2
    · linear_combination (ω ^ 2 + 7 * ω + 13) * hω + (-4 : F) * h2
    · linear_combination (ω ^ 3 + 7 * ω ^ 2 + 13 * ω) * hω + (-4 * ω) * h2
    · linear_combination (ω ^ 2 + 6 * ω + 8) * hω + (-2 * ω - 4) * h2
  · intro h
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 0 1) h
    simp only [hM] at this
    simp at this

include hF in
theorem realOver_interior_su {Y : Type*} [Group Y] {π : SU (unitaryInvolution F 2 f) n →* Y}
    {J : Subgroup Y} {a : Fin (n / 2)} (ha : a.val + 1 < n / 2)
    (hI : ∀ g ∈ rankOne (rootDatum hF n).rootGroup a, π g ∈ J) :
    HeisEngine.RealOver 5 π (rankOne (rootDatum hF n).rootGroup a) J := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ω, hω3, hω1⟩ := exists_order_three hF
  have hω : (ω : F) ^ 2 + ω + 1 = 0 := by
    have h1 : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = 0 := by
      have : ((ω ^ 3 : Fˣ) : F) = 1 := by rw [hω3, Units.val_one]
      rw [Units.val_pow_eq_pow_val] at this
      linear_combination this
    have h2 : (ω : F) - 1 ≠ 0 := fun h =>
      hω1 (Units.ext (by rw [Units.val_one]; linear_combination h))
    exact (mul_eq_zero.1 h1).resolve_left h2
  obtain ⟨X, Y', hX2, hY2, hXY5, hXY⟩ := exists_involutions_sl2 hω
  set e := rankOneShortEquiv (hσ := hσ) ha with he
  set L := rankOne (rootDatum hF n).rootGroup a with hL
  have hx2 : ((e.symm X : ↥L) : SU (unitaryInvolution F 2 f) n) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hX2, map_one, Subgroup.coe_one]
  have hy2 : ((e.symm Y' : ↥L) : SU (unitaryInvolution F 2 f) n) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hY2, map_one, Subgroup.coe_one]
  have hxy5 : (((e.symm X : ↥L) : SU (unitaryInvolution F 2 f) n) *
      ((e.symm Y' : ↥L) : SU (unitaryInvolution F 2 f) n)) ^ 5 = 1 := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, hXY5, map_one,
      Subgroup.coe_one]
  have hxy1 : ((e.symm X : ↥L) : SU (unitaryInvolution F 2 f) n) *
      ((e.symm Y' : ↥L) : SU (unitaryInvolution F 2 f) n) ≠ 1 := by
    intro h
    apply hXY
    have : e.symm (X * Y') = e.symm 1 := by
      rw [map_mul, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_mul, h, Subgroup.coe_one])
    exact e.symm.injective this
  exact HeisEngine.RealOver.of_involutions' (by decide : Odd 5) (e.symm X).2 (e.symm Y').2 hx2
    hy2 hxy5 hxy1 (hI _ (mul_mem (e.symm X).2 (e.symm Y').2))

include hF in
theorem torus_triple_dvd_of_central_five {ζ : traceZero (unitaryInvolution F 2 f)}
    (hζ : (ζ : F) ≠ 0) {a b c : Fin (n / 2)} (ha : a.val = 0) (hb : b.val = 1)
    (hc : c.val = 2) (h3 : 3 < n / 2) {ω : Fˣ} (hω : orderOf ω = 5)
    {x y z : SU (unitaryInvolution F 2 f) n}
    (hxm : mat (unitaryInvolution F 2 f) n x =
      diagonal (tFun (unitaryInvolution F 2 f) a (ω : F)))
    (hym : mat (unitaryInvolution F 2 f) n y =
      diagonal (tFun (unitaryInvolution F 2 f) b (ω : F)))
    (hzm : mat (unitaryInvolution F 2 f) n z =
      diagonal (tFun (unitaryInvolution F 2 f) c (ω : F))) {p q r : ℕ}
    (hw : x ^ p * y ^ q * z ^ r ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    5 ∣ p ∧ 5 ∣ q ∧ 5 ∣ r := by
  have hσ := unitaryInvolution_involutive hF
  have ha1 : a.val + 1 < n / 2 := by omega
  have hb1 : b.val + 1 < n / 2 := by omega
  have hc1 : c.val + 1 < n / 2 := by omega
  set e : Fin (n / 2) := ⟨3, h3⟩ with he
  have hd : mat (unitaryInvolution F 2 f) n (x ^ p * y ^ q * z ^ r) =
      diagonal (fun s => tFun (unitaryInvolution F 2 f) a (ω : F) s ^ p *
        tFun (unitaryInvolution F 2 f) b (ω : F) s ^ q *
        tFun (unitaryInvolution F 2 f) c (ω : F) s ^ r) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hxm, hym, hzm, diagonal_pow, diagonal_pow,
      diagonal_pow, diagonal_mul_diagonal, diagonal_mul_diagonal]
    rfl
  have key := diag_levelPerm_of_central hσ hζ hw hd
  have eab : (⟨a.val + 1, ha1⟩ : Fin (n / 2)) = b := Fin.ext (by simp [ha, hb])
  have ebc : (⟨b.val + 1, hb1⟩ : Fin (n / 2)) = c := Fin.ext (by simp [hb, hc])
  have ecd : (⟨c.val + 1, hc1⟩ : Fin (n / 2)) = e := Fin.ext (by simp [hc, he])
  have k1 := key a (lowIdx a)
  have k2 := key b (lowIdx b)
  have k3 := key c (lowIdx c)
  rw [levelPerm_lowIdx ha1, eab] at k1
  rw [levelPerm_lowIdx hb1, ebc] at k2
  rw [levelPerm_lowIdx hc1, ecd] at k3
  simp only [tFun_apply_lowIdx_short ha1, tFun_apply_lowIdx_short hb1,
    tFun_apply_lowIdx_short hc1, ha, hb, hc, he] at k1 k2 k3
  norm_num at k1 k2 k3
  refine five_dvd_of_torus_eqs hω ?_ ?_ ?_
  · apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow] using k1.symm
  · apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow] using k2.symm
  · apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow] using k3.symm

end SU

end CFSG.AGLEmbeddingD2.HeisUnitary
