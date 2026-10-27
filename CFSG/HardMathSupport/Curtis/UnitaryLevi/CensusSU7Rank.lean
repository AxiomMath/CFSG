module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlocks
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

include h in
theorem units_pow_three (x : Kˣ) : x ^ 3 = 1 := by
  have := h.finite
  have h4 : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  rw [← h4]
  exact pow_card_eq_one'

theorem bar_eq_sq (x : Kˣ) : h.bar (x : K) = (x : K) ^ 2 := by
  rw [h.bar_apply]
  simp

theorem bar_inv_eq (x : Kˣ) : (h.bar (x : K))⁻¹ = (x : K) := by
  rw [bar_eq_sq h, inv_eq_iff_eq_inv]
  have := units_pow_three h x
  have h3 : (x : K) ^ 3 = 1 := by simpa using congrArg Units.val this
  have hx : (x : K) ≠ 0 := x.ne_zero
  field_simp
  linear_combination h3

include h in
theorem two_eq_zero : (2 : K) = 0 := by
  have := h.charP
  exact_mod_cast CharP.cast_eq_zero K 2

@[expose] def hypTwoEquiv : HypIndex 1 0 ≃ Fin 2 where
  toFun
    | .inl _ => 0
    | .inr (.inl k) => k.elim0
    | .inr (.inr _) => 1
  invFun i := if i = 0 then .inl 0 else .inr (.inr 0)
  left_inv := by
    rintro (i | k | i)
    · simp [Subsingleton.elim i 0]
    · exact k.elim0
    · simp [Subsingleton.elim i 0]
  right_inv := by
    intro i
    fin_cases i <;> simp

@[expose] def g0Mat : Matrix (HypIndex 1 0) (HypIndex 1 0) K :=
  (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).submatrix hypTwoEquiv hypTwoEquiv

include h in
theorem det_g0Mat : (g0Mat (K := K)).det = 1 := by
  rw [g0Mat, det_submatrix_equiv_self]
  have h2 := two_eq_zero h
  simp [det_fin_two]
  linear_combination (-1 : K) * h2

theorem g0Mat_isometry : ((g0Mat (K := K)).map h.bar)ᵀ * hypGram 1 0 K * g0Mat = hypGram 1 0 K := by
  have h2 := two_eq_zero h
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  all_goals first | exact Fin.elim0 ‹Fin 0› | skip
  all_goals simp [Matrix.mul_apply, Fintype.sum_sum_type, g0Mat, hypTwoEquiv, hypGram_apply, hypPartner]
  all_goals first | exact Subsingleton.elim _ _ | linear_combination h2

@[expose] noncomputable def g0 : hypSU h 1 0 :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨g0Mat, det_g0Mat h⟩,
    mem_hypSU.mpr ⟨g0Mat_isometry h, det_g0Mat h⟩⟩

theorem coe_g0 : (((g0 h : hypSU h 1 0) : GL (HypIndex 1 0) K) : Matrix (HypIndex 1 0) (HypIndex 1 0) K) =
    g0Mat := rfl

theorem coe_g0_pow (n : ℕ) :
    (((g0 h ^ n : hypSU h 1 0) : GL (HypIndex 1 0) K) : Matrix (HypIndex 1 0) (HypIndex 1 0) K) =
      g0Mat ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_g0]

include h in
theorem g0_pow_three : g0 h ^ 3 = 1 := by
  have h2 := two_eq_zero h
  apply Subtype.ext
  apply Units.ext
  rw [coe_g0_pow]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j
  all_goals first | exact Fin.elim0 ‹Fin 0› | skip
  all_goals simp [pow_succ, Matrix.mul_apply, Fintype.sum_sum_type, g0Mat, hypTwoEquiv, one_apply]
  all_goals first
    | exact Subsingleton.elim _ _
    | (rw [Subsingleton.elim i j]; simp only [↓reduceIte]; linear_combination h2)
    | linear_combination h2

@[expose] def thetaThree : HypIndex 1 0 → HypIndex 3 1 :=
  hypMap (fun _ : Fin 1 => (2 : Fin 3)) (fun k : Fin 0 => k.elim0)

theorem thetaThree_injective : Function.Injective thetaThree :=
  hypMap_injective (fun i j _ => Subsingleton.elim i j) (fun k => k.elim0)

theorem thetaThree_partner (x : HypIndex 1 0) :
    thetaThree (hypPartner x) = hypPartner (thetaThree x) :=
  hypMap_partner _ _ x

@[expose] noncomputable def gThree : hypSU h 3 1 :=
  extHyp h thetaThree thetaThree_injective thetaThree_partner (g0 h)

theorem coe_gThree_pow (n : ℕ) :
    (((gThree h ^ n : hypSU h 3 1) : GL (HypIndex 3 1) K) : Matrix (HypIndex 3 1) (HypIndex 3 1) K) =
      extId thetaThree thetaThree_injective (g0Mat ^ n) := by
  rw [gThree, ← map_pow, coe_extHyp, coe_g0_pow]

include h in
theorem gThree_pow_three : gThree h ^ 3 = 1 := by
  rw [gThree, ← map_pow, g0_pow_three h, map_one]

theorem gThree_pow_apply_ef (n : ℕ) :
    (((gThree h ^ n : hypSU h 3 1) : GL (HypIndex 3 1) K) : Matrix (HypIndex 3 1) (HypIndex 3 1) K)
      (Sum.inl (2 : Fin 3)) (Sum.inr (Sum.inr (2 : Fin 3))) =
      (g0Mat ^ n : Matrix (HypIndex 1 0) (HypIndex 1 0) K) (Sum.inl 0) (Sum.inr (Sum.inr 0)) := by
  rw [coe_gThree_pow]
  exact extId_apply_map thetaThree thetaThree_injective _ (Sum.inl 0) (Sum.inr (Sum.inr 0))

theorem g0Mat_pow_one_apply_ef :
    (g0Mat ^ 1 : Matrix (HypIndex 1 0) (HypIndex 1 0) K) (Sum.inl 0) (Sum.inr (Sum.inr 0)) = 1 := by
  simp [g0Mat, hypTwoEquiv]

theorem g0Mat_pow_two_apply_ef :
    (g0Mat ^ 2 : Matrix (HypIndex 1 0) (HypIndex 1 0) K) (Sum.inl 0) (Sum.inr (Sum.inr 0)) = 1 := by
  simp [pow_succ, Matrix.mul_apply, Fintype.sum_sum_type, g0Mat, hypTwoEquiv]

@[expose] noncomputable def torMat (a : Fin 3 → Kˣ) : Matrix (HypIndex 3 1) (HypIndex 3 1) K :=
  diagonal (torusEntries h a (fun _ => ∏ i, a i))

theorem torMat_one : torMat h (1 : Fin 3 → Kˣ) = 1 := by
  rw [torMat, ← diagonal_one]
  congr 1
  funext x
  rcases x with i | k | i <;> simp [torusEntries]

theorem torMat_mul (a a' : Fin 3 → Kˣ) : torMat h (a * a') = torMat h a * torMat h a' := by
  rw [torMat, torMat, torMat, diagonal_mul_diagonal]
  congr 1
  funext x
  rcases x with i | k | i <;> simp [torusEntries, Finset.prod_mul_distrib, mul_comm]

@[expose] noncomputable def torMulHom :
    (Fin 3 → Kˣ) →* Matrix (HypIndex 3 1) (HypIndex 3 1) K where
  toFun := torMat h
  map_one' := torMat_one h
  map_mul' := torMat_mul h

include h in
theorem torMat_isometry (a : Fin 3 → Kˣ) :
    ((torMat h a).map h.bar)ᵀ * hypGram 3 1 K * torMat h a = hypGram 3 1 K := by
  refine diagonal_torusEntries_isometry h a (fun k => ?_)
  have := units_pow_three h (∏ i, a i)
  have h3 : ((∏ i, a i : Kˣ) : K) ^ 3 = 1 := by simpa using congrArg Units.val this
  simp only [UnitaryFieldData.norm, bar_eq_sq h]
  linear_combination h3

include h in
theorem det_torMat (a : Fin 3 → Kˣ) : (torMat h a).det = 1 := by
  rw [torMat, det_diagonal_torusEntries, torusRatio]
  simp only [bar_eq_sq h, Finset.univ_unique, Finset.prod_singleton, Units.coe_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have := (a i).ne_zero
  field_simp

@[expose] noncomputable def torHom : (Fin 3 → Kˣ) →* hypSU h 3 1 :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits (torMulHom h)) (hypSU h 3 1) fun a =>
    mem_hypSU.mpr ⟨torMat_isometry h a, det_torMat h a⟩

theorem coe_torHom (a : Fin 3 → Kˣ) :
    (((torHom h a : hypSU h 3 1) : GL (HypIndex 3 1) K) : Matrix (HypIndex 3 1) (HypIndex 3 1) K) =
      torMat h a := rfl

theorem torMat_inl (a : Fin 3 → Kˣ) (i : Fin 3) :
    torMat h a (Sum.inl i) (Sum.inl i) = a i := by
  simp [torMat, torusEntries]

theorem torMat_apply_ne (a : Fin 3 → Kˣ) {x y : HypIndex 3 1} (hxy : x ≠ y) :
    torMat h a x y = 0 := by
  simp [torMat, diagonal_apply_ne _ hxy]

theorem torHom_injective : Function.Injective (torHom h) := by
  intro a a' haa'
  have h1 := congrArg (fun x : hypSU h 3 1 => ((x : GL (HypIndex 3 1) K) :
    Matrix (HypIndex 3 1) (HypIndex 3 1) K)) haa'
  funext i
  have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i)
  simp only [coe_torHom, torMat_inl] at this
  exact Units.ext this

theorem torusEntries_theta (a : Fin 3 → Kˣ) (x : HypIndex 1 0) :
    torusEntries h a (fun _ => ∏ i, a i) (thetaThree x) = (a 2 : K) := by
  rcases x with i | k | i
  · rw [Subsingleton.elim i 0]
    rfl
  · exact k.elim0
  · rw [Subsingleton.elim i 0]
    exact bar_inv_eq h (a 2)

theorem torMat_mul_extId (a : Fin 3 → Kˣ) (M : Matrix (HypIndex 1 0) (HypIndex 1 0) K) :
    torMat h a * extId thetaThree thetaThree_injective M =
      extId thetaThree thetaThree_injective M * torMat h a := by
  ext x y
  rw [torMat, diagonal_mul, mul_diagonal]
  by_cases hx : x ∈ Set.range thetaThree <;> by_cases hy : y ∈ Set.range thetaThree
  · obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    rw [torusEntries_theta, torusEntries_theta, mul_comm]
  · rw [extId_apply_of_not_right _ _ _ _ hy]
    by_cases hxy : x = y
    · subst hxy
      rw [mul_comm]
    · simp [one_apply_ne hxy]
  · rw [extId_apply_of_not_left _ _ _ hx]
    by_cases hxy : x = y
    · subst hxy
      rw [mul_comm]
    · simp [one_apply_ne hxy]
  · rw [extId_apply_of_not_left _ _ _ hx]
    by_cases hxy : x = y
    · subst hxy
      rw [mul_comm]
    · simp [one_apply_ne hxy]

theorem commute_torHom_gThree (a : Fin 3 → Kˣ) : Commute (torHom h a) (gThree h) := by
  show _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_torHom, gThree, coe_extHyp, coe_g0]
  exact torMat_mul_extId h a _

theorem commute_torHom_zpowers (a : Fin 3 → Kˣ) (z : Subgroup.zpowers (gThree h)) :
    Commute (torHom h a) (z : hypSU h 3 1) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
  rw [← hk]
  exact (commute_torHom_gThree h a).zpow_right k

theorem torHom_mem_stab (a : Fin 3 → Kˣ) : torHom h a ∈ flagStabilizer h 3 1 {2} := by
  rw [mem_flagStabilizer]
  intro i hi
  rw [Set.mem_singleton_iff] at hi
  subst hi
  refine hom_smul_hypFlag h (torHom h) (by norm_num) (fun a x y hx hy => ?_) a
  rw [coe_torHom]
  exact torMat_apply_ne h a (by rintro rfl; omega)

theorem gThree_mem_stab : gThree h ∈ flagStabilizer h 3 1 {2} := by
  rw [mem_flagStabilizer]
  intro i hi
  rw [Set.mem_singleton_iff] at hi
  subst hi
  refine hom_smul_hypFlag h (extHyp h thetaThree thetaThree_injective thetaThree_partner)
    (by norm_num) (fun g x y hx hy => ?_) (g0 h)
  rw [coe_extHyp]
  refine extId_cut _ _ _ fullPos ?_ x y hx hy
  intro x' y' hx' hy'
  exfalso
  rcases y' with d | l | d
  · simp [thetaThree, hypMap] at hy'
  · exact l.elim0
  · simp [thetaThree, hypMap] at hy'

theorem gThree_pow_apply_ef_eq_one {n : ℕ} (hn : n = 1 ∨ n = 2) :
    (((gThree h ^ n : hypSU h 3 1) : GL (HypIndex 3 1) K) : Matrix (HypIndex 3 1) (HypIndex 3 1) K)
      (Sum.inl (2 : Fin 3)) (Sum.inr (Sum.inr (2 : Fin 3))) = 1 := by
  rw [gThree_pow_apply_ef]
  rcases hn with rfl | rfl
  · exact g0Mat_pow_one_apply_ef
  · exact g0Mat_pow_two_apply_ef

include h in
theorem gThree_ne_one : gThree h ≠ 1 := by
  intro e
  have := gThree_pow_apply_ef_eq_one h (n := 1) (Or.inl rfl)
  rw [pow_one, e] at this
  simp at this

include h in
theorem orderOf_gThree : orderOf (gThree h) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (gThree_pow_three h) (gThree_ne_one h)

include h in
theorem eq_one_of_torHom_eq_zpow (a : Fin 3 → Kˣ) (k : ℤ) (hk : torHom h a = gThree h ^ k) :
    gThree h ^ k = 1 := by
  have hk3 : gThree h ^ k = gThree h ^ (k % (3 : ℕ)) := zpow_eq_zpow_emod' k (gThree_pow_three h)
  have h0 : 0 ≤ k % (3 : ℕ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % (3 : ℕ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hne : (Sum.inl (2 : Fin 3) : HypIndex 3 1) ≠ Sum.inr (Sum.inr 2) := by simp
  have key : ∀ n : ℕ, (n = 1 ∨ n = 2) → torHom h a ≠ gThree h ^ n := by
    intro n hn e
    have := congrArg (fun x : hypSU h 3 1 => ((x : GL (HypIndex 3 1) K) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) K) (Sum.inl (2 : Fin 3)) (Sum.inr (Sum.inr (2 : Fin 3)))) e
    simp only [coe_torHom] at this
    rw [torMat_apply_ne h a hne, gThree_pow_apply_ef_eq_one h hn] at this
    exact zero_ne_one this
  generalize hm : k % (3 : ℕ) = m at hk3 h0 h3
  interval_cases m
  · rw [hk3]
    simp
  · exfalso
    rw [hk3, zpow_one] at hk
    exact key 1 (Or.inl rfl) (by simpa using hk)
  · exfalso
    rw [hk3] at hk
    exact key 2 (Or.inr rfl) (by simpa using hk)

@[expose] noncomputable def psiHom :
    ((Fin 3 → Kˣ) × Subgroup.zpowers (gThree h)) →* hypSU h 3 1 :=
  (torHom h).noncommCoprod (Subgroup.zpowers (gThree h)).subtype (commute_torHom_zpowers h)

theorem psiHom_apply (u : (Fin 3 → Kˣ) × Subgroup.zpowers (gThree h)) :
    psiHom h u = torHom h u.1 * (u.2 : hypSU h 3 1) := rfl

include h in
theorem psiHom_injective : Function.Injective (psiHom h) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, z⟩ hz
  rw [psiHom_apply] at hz
  have hz' : torHom h a = (z : hypSU h 3 1)⁻¹ := eq_inv_of_mul_eq_one_left hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (inv_mem z.2)
  have h1 := eq_one_of_torHom_eq_zpow h a k (by rw [hk]; exact hz')
  rw [hk] at h1
  have hz1 : (z : hypSU h 3 1) = 1 := inv_eq_one.mp h1
  rw [hz1, inv_one] at hz'
  rw [← map_one (torHom h)] at hz'
  have := torHom_injective h hz'
  exact Prod.ext this (Subtype.ext hz1)

include h in
theorem psiHom_pow_three (u : (Fin 3 → Kˣ) × Subgroup.zpowers (gThree h)) :
    psiHom h u ^ 3 = 1 := by
  have hz : u.2 ^ 3 = 1 := by
    have : Nat.card (Subgroup.zpowers (gThree h)) = 3 := by
      rw [Nat.card_zpowers, orderOf_gThree h]
    have := pow_card_eq_one' (G := Subgroup.zpowers (gThree h)) (x := u.2)
    rwa [‹Nat.card (Subgroup.zpowers (gThree h)) = 3›] at this
  rw [← map_pow]
  have : u ^ 3 = 1 := by
    refine Prod.ext ?_ hz
    funext i
    exact units_pow_three h (u.1 i)
  rw [this, map_one]

theorem psiHom_mem_stab (u : (Fin 3 → Kˣ) × Subgroup.zpowers (gThree h)) :
    psiHom h u ∈ flagStabilizer h 3 1 {2} := by
  rw [psiHom_apply]
  refine mul_mem (torHom_mem_stab h _) ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2.2
  rw [← hk]
  exact zpow_mem (gThree_mem_stab h) k

theorem eq_one_of_mem_scalars_pow_three_su7 (g : hypSU h 3 1) (hg : g ∈ hypScalars h 3 1)
    (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨c, -, hcn, hgc⟩ := hg
  have hc3 : c ^ 3 = 1 := by
    have h1 : ((g : GL (HypIndex 3 1) K)) ^ 3 = 1 := by
      have := congrArg (fun x : hypSU h 3 1 => (x : GL (HypIndex 3 1) K)) h3
      simpa using this
    rw [hgc, ← map_pow] at h1
    have h2 := congrArg (fun x : GL (HypIndex 3 1) K =>
      (x : Matrix (HypIndex 3 1) (HypIndex 3 1) K) (.inl 0) (.inl 0)) h1
    simp only [scalar_entry, ite_true] at h2
    apply Units.ext
    simpa using h2
  have hc1 : c = 1 := by
    have hn : c ^ 7 = 1 := hcn
    calc c = c ^ 7 * (c ^ 3)⁻¹ * (c ^ 3)⁻¹ := by group
      _ = 1 := by rw [hc3, hn]; simp
  apply Subtype.ext
  rw [hgc, hc1, map_one]
  rfl

include h in
theorem exists_elemAbelian_rank_four :
    ∃ A : Subgroup (hypSU h 3 1), A ≤ flagStabilizer h 3 1 {2} ∧ CFSG.Open.IsElemAbelian 3 A ∧
      Nat.card A = 3 ^ 4 ∧ A ⊓ hypScalars h 3 1 = ⊥ := by
  have := h.finite
  have hK3 : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  refine ⟨(psiHom h).range, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact psiHom_mem_stab h u
  · refine isMulCommutative_iff.mpr fun x y => ?_
    obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    apply Subtype.ext
    show (x : hypSU h 3 1) * y = y * x
    have huv : u * v = v * u := by
      refine Prod.ext (mul_comm _ _) (Subtype.ext ?_)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2.2
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp v.2.2
      show (u.2 : hypSU h 3 1) * v.2 = v.2 * u.2
      rw [← hk, ← hl]
      exact (Commute.refl (gThree h)).zpow_zpow k l |>.eq
    rw [← hu, ← hv, ← map_mul, ← map_mul, huv]
  · rintro _ ⟨u, rfl⟩
    exact psiHom_pow_three h u
  · rw [Nat.card_congr (MonoidHom.ofInjective (psiHom_injective h)).symm.toEquiv]
    rw [Nat.card_prod, Nat.card_pi, Nat.card_zpowers, orderOf_gThree h]
    simp [hK3]
  · rw [eq_bot_iff]
    rintro g ⟨⟨u, rfl⟩, hg⟩
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_scalars_pow_three_su7 h _ hg (psiHom_pow_three h u)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
