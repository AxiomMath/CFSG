module

public import CFSG.CharacterTheory.Semidihedral.GL2ThreeStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicMultiplicity
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.Blocks.CharacterCriterion

public section

namespace CFSG.Semidihedral.Principal

namespace GL2ThreeCharacters

open Matrix CFSG.TwoRankLowerBound.Helpers
open CFSG.Semidihedral.FourPointMatrices (normalUnit normalMatrix normalUnit_surjective
  normalUnit_injective normalUnit_matrix)

abbrev G23 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

abbrev Coord := GL2ThreeStructure.Coordinates

@[expose] def classOfTraceDet (t d : ZMod 3) : Fin 8 :=
  if d = 1 then (if t = 0 then 2 else if t = 2 then 3 else 4)
  else (if t = 0 then 5 else if t = 1 then 6 else 7)

@[expose] def classOf (g : G23) : Fin 8 :=
  if g = 1 then 0 else if g = -1 then 1 else
    classOfTraceDet (Matrix.trace (g : Matrix (Fin 2) (Fin 2) (ZMod 3)))
      (Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod 3)))

@[expose] def a0 : G23 := ⟨!![0, 1; 1, 1], !![2, 1; 1, 0], by decide, by decide⟩

@[expose] def c0 : G23 := -1 * GL2ThreeStructure.U

@[expose] def reference : Fin 8 → G23 :=
  ![1, -1, a0 ^ 2, GL2ThreeStructure.U, -1 * GL2ThreeStructure.U, FourPointMatrices.C, a0,
    a0⁻¹]

@[expose] def classSize : Fin 8 → ℕ := ![1, 1, 6, 8, 8, 12, 6, 6]

@[expose] def invClass : Fin 8 → Fin 8 := ![0, 1, 2, 3, 4, 5, 7, 6]

set_option maxRecDepth 20000 in
theorem classOf_reference : ∀ j : Fin 8, classOf (reference j) = j := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem exists_conj_reference_coord : ∀ i : Coord, ∃ k : Coord,
    normalUnit k * reference (classOf (normalUnit i)) = normalUnit i * normalUnit k := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem card_classOf_coord : ∀ j : Fin 8,
    (Finset.univ.filter fun i : Coord => classOf (normalUnit i) = j).card = classSize j := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem classOf_inv_coord : ∀ i : Coord,
    classOf (normalUnit i)⁻¹ = invClass (classOf (normalUnit i)) := by
  decide

theorem card_filter_eq_coord (P : G23 → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun i : Coord => P (normalUnit i)).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact (Fintype.card_congr (GL2ThreeStructure.normalEquiv.subtypeEquiv fun _ => Iff.rfl)).symm

theorem classOf_conj (c g : G23) : classOf (c * g * c⁻¹) = classOf g := by
  have h1 : c * g * c⁻¹ = 1 ↔ g = 1 := by
    constructor
    · intro h
      calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hneg : ∀ x : G23, x * -1 = -1 * x := fun x => by rw [mul_neg_one, neg_one_mul]
  have h2 : c * g * c⁻¹ = -1 ↔ g = -1 := by
    constructor
    · intro h
      calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
        _ = -1 := by rw [h, hneg, mul_assoc, inv_mul_cancel, mul_one]
    · intro h
      rw [h, hneg, mul_inv_cancel_right]
  have hval : ((c * g * c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g * ((c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
    by simp only [Units.val_mul]
  have hinv : ((c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * c = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv' : (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have htr : Matrix.trace ((c * g * c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    rw [hval, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hdet : Matrix.det ((c * g * c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    have hc : Matrix.det (c : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        Matrix.det ((c⁻¹ : G23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
      rw [← Matrix.det_mul, hinv', Matrix.det_one]
    rw [hval, Matrix.det_mul, Matrix.det_mul]
    linear_combination (Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod 3))) * hc
  unfold classOf
  by_cases hg1 : g = 1
  · rw [ite_eq_left (h1.mpr hg1), ite_eq_left hg1]
  rw [ite_eq_right (fun h => hg1 (h1.mp h)), ite_eq_right hg1]
  by_cases hg2 : g = -1
  · rw [ite_eq_left (h2.mpr hg2), ite_eq_left hg2]
  rw [ite_eq_right (fun h => hg2 (h2.mp h)), ite_eq_right hg2, htr, hdet]

theorem isConj_reference (g : G23) : IsConj (reference (classOf g)) g := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  obtain ⟨k, hk⟩ := exists_conj_reference_coord i
  refine isConj_iff.mpr ⟨normalUnit k, ?_⟩
  rw [hk, mul_inv_cancel_right]

theorem isConj_iff_classOf (g h : G23) : IsConj g h ↔ classOf g = classOf h := by
  constructor
  · intro hgh
    obtain ⟨c, rfl⟩ := isConj_iff.mp hgh
    exact (classOf_conj c g).symm
  · intro hgh
    have h1 := isConj_reference g
    have h2 := isConj_reference h
    rw [hgh] at h1
    exact h1.symm.trans h2

theorem classOf_inv (g : G23) : classOf g⁻¹ = invClass (classOf g) := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  exact classOf_inv_coord i

theorem card_filter_classOf (j : Fin 8) :
    (Finset.univ.filter fun g : G23 => classOf g = j).card = classSize j := by
  rw [card_filter_eq_coord]
  exact card_classOf_coord j

theorem sum_classOf (F : Fin 8 → ℂ) :
    ∑ g : G23, F (classOf g) = ∑ j : Fin 8, (classSize j : ℂ) * F j := by
  rw [← Finset.sum_fiberwise' Finset.univ classOf F]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, card_filter_classOf, nsmul_eq_mul]

theorem classFunction_eq_reference (f : G23 → ℂ) (hf : ∀ c g : G23, f (c * g * c⁻¹) = f g)
    (g : G23) : f g = f (reference (classOf g)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_reference g)
  have h := hf c (reference (classOf g))
  rw [hc] at h
  exact h


@[expose] noncomputable def cyclicLinearHom {G : Type*} [Group G] (u : G) (M : ℕ)
    (hu : orderOf u = M) (k : ℤ) : Subgroup.zpowers u →* ℂ where
  toFun := cyclicLinearCharacter u M k
  map_one' := by
    have h0 : (1 : Subgroup.zpowers u) = ⟨u ^ (0 : ℤ), Subgroup.zpow_mem_zpowers u 0⟩ :=
      Subtype.ext (zpow_zero u).symm
    show cyclicLinearCharacter u M k 1 = 1
    rw [h0, cyclicLinearCharacter_zpow hu, mul_zero, zpow_zero]
  map_mul' := cyclicLinearCharacter_mul hu k

theorem cyclicLinearCharacter_mem_virtualCharacters {G : Type} [Group G] (u : G) (M : ℕ)
    (hu : orderOf u = M) (k : ℤ) :
    cyclicLinearCharacter u M k ∈ virtualCharacters (Subgroup.zpowers u) := by
  let data : FiniteComplexRepresentation (Subgroup.zpowers u) :=
    { vector := ℂ, representation := scalarHomRepresentation (cyclicLinearHom u M hu k) }
  have hchar : data.character = cyclicLinearCharacter u M k := by
    show (scalarHomRepresentation (cyclicLinearHom u M hu k)).character = _
    rw [scalarHomRepresentation_character]
    rfl
  rw [← hchar]
  exact character_mem_virtualCharacters data

theorem inducedFunction_cyclicLinearCharacter_eq {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (u : G)
    (M : ℕ) (hu : orderOf u = M) (k : ℕ) (g : G) :
    inducedFunction (Subgroup.zpowers u) (cyclicLinearCharacter u M k) g =
      (M : ℂ)⁻¹ * ∑ m : Fin M,
        ((Finset.univ.filter fun c : G => c⁻¹ * g * c = u ^ (m : ℕ)).card : ℂ) *
          cyclicRoot M ^ (k * (m : ℕ)) := by
  classical
  subst hu
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  unfold inducedFunction
  rw [Nat.card_zpowers]
  congr 1
  have hterm : ∀ c : G, (if hmember : c⁻¹ * g * c ∈ Subgroup.zpowers u then
      cyclicLinearCharacter u (orderOf u) k ⟨c⁻¹ * g * c, hmember⟩ else 0) =
      ∑ m : Fin (orderOf u), if c⁻¹ * g * c = u ^ (m : ℕ) then
        cyclicRoot (orderOf u) ^ (k * (m : ℕ)) else 0 := by
    intro c
    by_cases hmem : c⁻¹ * g * c ∈ Subgroup.zpowers u
    · rw [dite_eq_left hmem]
      set m₀ := (finEquivZPowers hfin).symm ⟨_, hmem⟩ with hm₀def
      have hm₀ : u ^ (m₀ : ℕ) = c⁻¹ * g * c :=
        pow_finEquivZPowers_symm_apply hfin ⟨_, hmem⟩
      rw [Finset.sum_eq_single m₀]
      · rw [ite_eq_left hm₀.symm]
        have hx : (⟨c⁻¹ * g * c, hmem⟩ : Subgroup.zpowers u) =
            ⟨u ^ ((m₀ : ℕ) : ℤ), Subgroup.zpow_mem_zpowers u _⟩ :=
          Subtype.ext (by
            show c⁻¹ * g * c = u ^ ((m₀ : ℕ) : ℤ)
            rw [zpow_natCast, hm₀])
        rw [hx, cyclicLinearCharacter_zpow rfl, ← Nat.cast_mul, zpow_natCast]
      · intro m _ hm
        rw [ite_eq_right]
        intro h
        apply hm
        apply (finEquivZPowers hfin).injective
        rw [finEquivZPowers_apply, finEquivZPowers_apply]
        exact Subtype.ext (h.symm.trans hm₀.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right hmem]
      symm
      apply Finset.sum_eq_zero
      intro m _
      rw [ite_eq_right]
      intro h
      exact hmem (h ▸ Subgroup.npow_mem_zpowers u _)
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem orderOf_a0 : orderOf a0 = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := a0) (by decide) (by decide)
  norm_num at h
  exact h

theorem orderOf_c0 : orderOf c0 = 6 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

@[expose] def countEight : Fin 8 → Fin 8 → ℕ :=
  ![![48, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 48, 0, 0, 0], ![0, 0, 8, 0, 0, 0, 8, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 8, 0, 8, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 8, 0, 8]]

@[expose] def countSix : Fin 8 → Fin 6 → ℕ :=
  ![![48, 0, 0, 0, 0, 0], ![0, 0, 0, 48, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 6, 0, 6, 0],
    ![0, 6, 0, 0, 0, 6], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem countEight_coord : ∀ j m : Fin 8,
    (Finset.univ.filter fun i : Coord =>
      (normalUnit i)⁻¹ * reference j * normalUnit i = a0 ^ (m : ℕ)).card = countEight j m := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem countSix_coord : ∀ (j : Fin 8) (m : Fin 6),
    (Finset.univ.filter fun i : Coord =>
      (normalUnit i)⁻¹ * reference j * normalUnit i = c0 ^ (m : ℕ)).card = countSix j m := by
  decide

noncomputable abbrev xi : ℂ := cyclicRoot 8

noncomputable abbrev zeta : ℂ := cyclicRoot 6

theorem xi_pow_eight : xi ^ 8 = 1 := cyclicRoot_pow_self 8

theorem xi_pow_four : xi ^ 4 = -1 := by
  have h := cyclicRoot_pow_half (M := 8) (by norm_num) (by decide)
  norm_num at h
  exact h

theorem xi_pow_sub (n : ℕ) (hn : 8 ≤ n) : xi ^ n = xi ^ (n - 8) := by
  rw [show n = (n - 8) + 8 by omega, pow_add, xi_pow_eight, mul_one, Nat.add_sub_cancel]

theorem xi_pow_five : xi ^ 5 = -xi := by rw [pow_succ, xi_pow_four, neg_one_mul]

theorem xi_pow_six : xi ^ 6 = -xi ^ 2 := by
  rw [show 6 = 4 + 2 by norm_num, pow_add, xi_pow_four, neg_one_mul]

theorem xi_pow_seven : xi ^ 7 = -xi ^ 3 := by
  rw [show 7 = 4 + 3 by norm_num, pow_add, xi_pow_four, neg_one_mul]

theorem zeta_pow_six : zeta ^ 6 = 1 := cyclicRoot_pow_self 6

theorem zeta_pow_three : zeta ^ 3 = -1 := by
  have h := cyclicRoot_pow_half (M := 6) (by norm_num) (by decide)
  norm_num at h
  exact h

theorem zeta_sq : zeta ^ 2 = zeta - 1 := by
  have hprim := cyclicRoot_isPrimitiveRoot (M := 6) (by norm_num)
  have hne : zeta ≠ -1 := by
    intro h
    have h2 : zeta ^ 2 = 1 := by rw [h]; norm_num
    exact hprim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h2
  have hfac : (zeta + 1) * (zeta ^ 2 - zeta + 1) = 0 := by
    linear_combination zeta_pow_three
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (eq_neg_of_add_eq_zero_left h) hne
  · linear_combination h

theorem zeta_pow_sub (n : ℕ) (hn : 6 ≤ n) : zeta ^ n = zeta ^ (n - 6) := by
  rw [show n = (n - 6) + 6 by omega, pow_add, zeta_pow_six, mul_one, Nat.add_sub_cancel]

theorem zeta_pow_four : zeta ^ 4 = -zeta := by
  rw [show 4 = 3 + 1 by norm_num, pow_add, zeta_pow_three, pow_one, neg_one_mul]

theorem zeta_pow_five : zeta ^ 5 = 1 - zeta := by
  rw [show 5 = 3 + 2 by norm_num, pow_add, zeta_pow_three, zeta_sq]
  ring

noncomputable abbrev omega8 : ℂ := xi + xi ^ 3

theorem omega8_sq : omega8 ^ 2 = -2 := by
  have h : omega8 ^ 2 = xi ^ 2 + 2 * xi ^ 4 + xi ^ 6 := by ring
  rw [h, xi_pow_four, xi_pow_six]
  ring

@[expose] noncomputable def indEight (k : ℕ) : G23 → ℂ :=
  inducedFunction (Subgroup.zpowers a0) (cyclicLinearCharacter a0 8 k)

@[expose] noncomputable def indSix (k : ℕ) : G23 → ℂ :=
  inducedFunction (Subgroup.zpowers c0) (cyclicLinearCharacter c0 6 k)

theorem indEight_reference (k : ℕ) (j : Fin 8) : indEight k (reference j) =
    ![6, 6 * xi ^ (4 * k), xi ^ (2 * k) + xi ^ (6 * k), 0, 0, 0, xi ^ k + xi ^ (3 * k),
      xi ^ (5 * k) + xi ^ (7 * k)] j := by
  rw [indEight, inducedFunction_cyclicLinearCharacter_eq a0 8 orderOf_a0 k]
  have hcount : ∀ m : Fin 8, ((Finset.univ.filter fun c : G23 =>
      c⁻¹ * reference j * c = a0 ^ (m : ℕ)).card : ℂ) = countEight j m := by
    intro m
    rw [card_filter_eq_coord, countEight_coord]
  simp only [hcount]
  fin_cases j <;> simp [Fin.sum_univ_eight, countEight] <;> ring

theorem indSix_reference (k : ℕ) (j : Fin 8) : indSix k (reference j) =
    ![8, 8 * zeta ^ (3 * k), 0, zeta ^ (2 * k) + zeta ^ (4 * k), zeta ^ k + zeta ^ (5 * k), 0, 0,
      0] j := by
  rw [indSix, inducedFunction_cyclicLinearCharacter_eq c0 6 orderOf_c0 k]
  have hcount : ∀ m : Fin 6, ((Finset.univ.filter fun c : G23 =>
      c⁻¹ * reference j * c = c0 ^ (m : ℕ)).card : ℂ) = countSix j m := by
    intro m
    rw [card_filter_eq_coord, countSix_coord]
  simp only [hcount]
  fin_cases j <;> simp [Fin.sum_univ_six, countSix] <;> ring

@[expose] noncomputable def indFun : Fin 9 → G23 → ℂ :=
  ![1, indEight 0, indEight 1, indEight 2, indEight 4, indEight 7, indSix 0, indSix 1, indSix 2]

@[expose] def indA : Fin 9 → Fin 8 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1], ![6, 6, 2, 0, 0, 0, 2, 2], ![6, -6, 0, 0, 0, 0, 0, 0],
    ![6, 6, -2, 0, 0, 0, 0, 0], ![6, 6, 2, 0, 0, 0, -2, -2], ![6, -6, 0, 0, 0, 0, 0, 0],
    ![8, 8, 0, 2, 2, 0, 0, 0], ![8, -8, 0, -1, 1, 0, 0, 0], ![8, 8, 0, -1, -1, 0, 0, 0]]

@[expose] def indB : Fin 9 → Fin 8 → ℤ :=
  ![0, 0, ![0, 0, 0, 0, 0, 0, 1, -1], 0, 0, ![0, 0, 0, 0, 0, 0, -1, 1], 0, 0, 0]

theorem indFun_reference (r : Fin 9) (j : Fin 8) :
    indFun r (reference j) = (indA r j : ℂ) + (indB r j : ℂ) * omega8 := by
  fin_cases r <;> fin_cases j <;>
    simp [indFun, indA, indB, indEight_reference, indSix_reference, xi_pow_four, xi_pow_five,
      xi_pow_six, xi_pow_seven, xi_pow_sub, zeta_pow_three, zeta_pow_four, zeta_pow_five,
      zeta_sq, zeta_pow_sub] <;> ring

@[expose] def coef : Fin 8 → Fin 9 → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, -1, 0, 0, 1, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0, 1], ![-1, 1, 0, 1, 0, 0, 0, 0, -1],
    ![1, 0, 0, 2, 1, 0, -1, 0, -1], ![0, 0, 1, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, -1, 0, 1, 0], ![0, 0, -1, 0, 0, 0, 0, 1, 0]]

@[expose] def tableA : Fin 8 → Fin 8 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, -1, -1, -1], ![2, 2, 2, -1, -1, 0, 0, 0],
    ![3, 3, -1, 0, 0, -1, 1, 1], ![3, 3, -1, 0, 0, 1, -1, -1], ![4, -4, 0, 1, -1, 0, 0, 0],
    ![2, -2, 0, -1, 1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, 0, 0]]

@[expose] def tableB : Fin 8 → Fin 8 → ℤ :=
  ![0, 0, 0, 0, 0, 0, ![0, 0, 0, 0, 0, 0, 1, -1], ![0, 0, 0, 0, 0, 0, -1, 1]]

theorem tableA_eq : ∀ i j : Fin 8, tableA i j = ∑ r, coef i r * indA r j := by decide

theorem tableB_eq : ∀ i j : Fin 8, tableB i j = ∑ r, coef i r * indB r j := by decide

@[expose] noncomputable def psi (i : Fin 8) : G23 → ℂ := ∑ r, coef i r • indFun r

theorem psi_apply (i : Fin 8) (g : G23) : psi i g = ∑ r, (coef i r : ℂ) * indFun r g := by
  simp [psi, Finset.sum_apply, zsmul_eq_mul]

theorem psi_reference (i j : Fin 8) :
    psi i (reference j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8 := by
  rw [psi_apply, tableA_eq, tableB_eq]
  simp only [indFun_reference, mul_add, Finset.sum_add_distrib, Int.cast_sum, Int.cast_mul,
    Finset.sum_mul, mul_assoc]

theorem indFun_conj (r : Fin 9) (c g : G23) : indFun r (c * g * c⁻¹) = indFun r g := by
  fin_cases r
  · rfl
  all_goals exact inducedFunction_conjugate _ _ g c

theorem psi_conj (i : Fin 8) (c g : G23) : psi i (c * g * c⁻¹) = psi i g := by
  rw [psi_apply, psi_apply]
  simp only [indFun_conj]

theorem psi_eq_table (i : Fin 8) (g : G23) :
    psi i g = (tableA i (classOf g) : ℂ) + (tableB i (classOf g) : ℂ) * omega8 := by
  rw [classFunction_eq_reference (psi i) (psi_conj i) g, psi_reference]

theorem indFun_mem_virtualCharacters (r : Fin 9) : indFun r ∈ virtualCharacters G23 := by
  fin_cases r
  · let data : FiniteComplexRepresentation G23 :=
      { vector := ℂ, representation := scalarHomRepresentation (1 : G23 →* ℂ) }
    have hchar : data.character = 1 := by
      show (scalarHomRepresentation (1 : G23 →* ℂ)).character = 1
      rw [scalarHomRepresentation_character]
      rfl
    show (1 : G23 → ℂ) ∈ virtualCharacters G23
    rw [← hchar]
    exact character_mem_virtualCharacters data
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters a0 8 orderOf_a0 _)
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters a0 8 orderOf_a0 _)
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters a0 8 orderOf_a0 _)
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters a0 8 orderOf_a0 _)
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters a0 8 orderOf_a0 _)
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters c0 6 orderOf_c0 _)
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters c0 6 orderOf_c0 _)
  · exact inducedFunction_mem_virtualCharacters _
      (cyclicLinearCharacter_mem_virtualCharacters c0 6 orderOf_c0 _)

theorem psi_mem_virtualCharacters (i : Fin 8) : psi i ∈ virtualCharacters G23 :=
  Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (indFun_mem_virtualCharacters r)

theorem sum_classSize_mul_pair (A B A' B' : Fin 8 → ℤ) :
    ∑ j : Fin 8, (classSize j : ℂ) * (((A j : ℂ) + B j * omega8) * ((A' j : ℂ) + B' j * omega8)) =
      ((∑ j, (classSize j : ℤ) * (A j * A' j - 2 * B j * B' j) : ℤ) : ℂ) +
        ((∑ j, (classSize j : ℤ) * (A j * B' j + B j * A' j) : ℤ) : ℂ) * omega8 := by
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  linear_combination ((classSize j : ℂ) * B j * B' j) * omega8_sq

theorem table_norm_rational : ∀ i : Fin 8, ∑ j, (classSize j : ℤ) *
    (tableA i j * tableA i (invClass j) - 2 * tableB i j * tableB i (invClass j)) = 48 := by
  decide

theorem table_norm_omega : ∀ i : Fin 8, ∑ j, (classSize j : ℤ) *
    (tableA i j * tableB i (invClass j) + tableB i j * tableA i (invClass j)) = 0 := by
  decide

theorem card_G23 : Nat.card G23 = 48 := GL2ThreeStructure.card48

theorem psi_norm (i : Fin 8) : characterPairing (psi i) (psi i) = 1 := by
  unfold characterPairing
  set F : Fin 8 → ℂ := fun j => ((tableA i j : ℂ) + (tableB i j : ℂ) * omega8) *
    ((tableA i (invClass j) : ℂ) + (tableB i (invClass j) : ℂ) * omega8) with hF
  have hval : ∀ g : G23, psi i g * psi i g⁻¹ = F (classOf g) := by
    intro g
    rw [psi_eq_table, psi_eq_table, classOf_inv]
  rw [Finset.sum_congr rfl fun g _ => hval g, sum_classOf F, hF,
    sum_classSize_mul_pair (tableA i) (tableB i) (fun j => tableA i (invClass j))
      (fun j => tableB i (invClass j)), table_norm_rational, table_norm_omega, card_G23]
  norm_num

theorem psi_one (i : Fin 8) : psi i 1 = tableA i 0 := by
  have h := psi_reference i 0
  have hB : tableB i 0 = 0 := by fin_cases i <;> rfl
  simpa [reference, hB] using h

theorem tableA_degree_pos : ∀ i : Fin 8, 0 < tableA i 0 := by decide

theorem exists_label (basis : FiniteIrreducibleCharacterBasis G23) (i : Fin 8) :
    ∃ ℓ : basis.index, (basis.representation ℓ).character = psi i := by
  obtain ⟨ℓ, h | h⟩ := virtual_norm_one_signed_basis_character basis (psi i)
    (psi_mem_virtualCharacters i) (psi_norm i)
  · exact ⟨ℓ, h.symm⟩
  · exfalso
    have h1 := congrArg Complex.re (congrFun h 1)
    rw [psi_one] at h1
    simp only [Pi.neg_apply, FiniteComplexRepresentation.character, Representation.char_one,
      Complex.neg_re, Complex.natCast_re, Complex.intCast_re] at h1
    have hpos := tableA_degree_pos i
    have hnn : (0 : ℝ) ≤ Module.finrank ℂ (basis.representation ℓ).vector := Nat.cast_nonneg _
    have : (0 : ℝ) < (tableA i 0 : ℝ) := by exact_mod_cast hpos
    linarith

theorem int_add_mul_omega8_eq_zero {a b : ℤ} (h : (a : ℂ) + b * omega8 = 0) : a = 0 ∧ b = 0 := by
  have h2 : (a : ℂ) ^ 2 = -2 * (b : ℂ) ^ 2 := by
    have h1 : (a : ℂ) = -(b * omega8) := by linear_combination h
    rw [h1]
    linear_combination (b : ℂ) ^ 2 * omega8_sq
  have h3 : a ^ 2 = -2 * b ^ 2 := by exact_mod_cast h2
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem table_rows_injective : ∀ i j : Fin 8,
    (∀ k, tableA i k = tableA j k ∧ tableB i k = tableB j k) → i = j := by
  decide

theorem psi_injective : Function.Injective psi := by
  intro i j h
  apply table_rows_injective
  intro k
  have hk := congrFun h (reference k)
  rw [psi_reference, psi_reference] at hk
  have hz := int_add_mul_omega8_eq_zero (a := tableA i k - tableA j k)
    (b := tableB i k - tableB j k) (by push_cast; linear_combination hk)
  constructor <;> omega

theorem card_basis_index_le (basis : FiniteIrreducibleCharacterBasis G23) :
    Fintype.card basis.index ≤ 8 := by
  have hli : LinearIndependent ℂ (fun ℓ : basis.index => fun j : Fin 8 =>
      (basis.representation ℓ).character (reference j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc ℓ
    have hzero : ∀ g : G23, ∑ m, c m * (basis.representation m).character g = 0 := by
      intro g
      have hclass : ∀ x y : G23, (fun w => ∑ m, c m * (basis.representation m).character w)
          (x * y * x⁻¹) = (fun w => ∑ m, c m * (basis.representation m).character w) y := by
        intro x y
        simp only [FiniteComplexRepresentation.character, Representation.char_conj]
      rw [classFunction_eq_reference (fun w => ∑ m, c m * (basis.representation m).character w)
        hclass g]
      have h := congrFun hc (classOf g)
      simpa [Finset.sum_apply] using h
    have hpair := characterPairing_expansion_left (basis.representation ℓ).character
      (fun m => (basis.representation m).character) c
    have hleft : (fun element => ∑ m, c m * (basis.representation m).character element) = 0 :=
      funext hzero
    rw [hleft] at hpair
    have hzpair : characterPairing (0 : G23 → ℂ) (basis.representation ℓ).character = 0 := by
      unfold characterPairing
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]
    rw [hzpair] at hpair
    rw [Finset.sum_eq_single ℓ] at hpair
    · rw [characterPairing_irreducible _ _ (basis.irreducible ℓ) (basis.irreducible ℓ),
        ite_eq_left rfl, mul_one] at hpair
      exact hpair.symm
    · intro m _ hm
      rw [characterPairing_irreducible _ _ (basis.irreducible m) (basis.irreducible ℓ),
        ite_eq_right (fun h => hm (basis.distinct h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ ℓ) h
  have h := hli.fintype_card_le_finrank
  simpa using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem classOf_order_coord : ∀ i : Coord,
    (GL2ThreeStructure.coordinateOrder i = 8 →
      (classOf (normalUnit i) = 6 ∨ classOf (normalUnit i) = 7) ∧
        classOf (normalUnit i ^ 2) = 2) ∧
    (GL2ThreeStructure.coordinateOrder i = 3 →
      classOf (normalUnit i) = 3 ∧ classOf (-1 * normalUnit i) = 4) ∧
    (GL2ThreeStructure.coordinateOrder i = 2 → normalUnit i ≠ -1 →
      classOf (normalUnit i) = 5) := by
  decide

theorem classOf_of_orderOf_eight {g : G23} (hg : orderOf g = 8) :
    (classOf g = 6 ∨ classOf g = 7) ∧ classOf (g ^ 2) = 2 := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  rw [GL2ThreeStructure.normalUnit_order] at hg
  exact (classOf_order_coord i).1 hg

theorem classOf_of_orderOf_three {g : G23} (hg : orderOf g = 3) :
    classOf g = 3 ∧ classOf (-1 * g) = 4 := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  rw [GL2ThreeStructure.normalUnit_order] at hg
  exact (classOf_order_coord i).2.1 hg

theorem classOf_of_orderOf_two {g : G23} (hg : orderOf g = 2) (hgz : g ≠ -1) :
    classOf g = 5 := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  rw [GL2ThreeStructure.normalUnit_order] at hg
  exact (classOf_order_coord i).2.2 hg hgz

theorem classOf_one : classOf 1 = 0 := by decide

theorem classOf_neg_one : classOf (-1) = 1 := by decide

theorem table_swap : ∀ i j : Fin 8,
    tableA (Equiv.swap (6 : Fin 8) 7 i) (Equiv.swap (6 : Fin 8) 7 j) = tableA i j ∧
      tableB (Equiv.swap (6 : Fin 8) 7 i) (Equiv.swap (6 : Fin 8) 7 j) = tableB i j := by
  decide

theorem classSize_swap : ∀ j : Fin 8, classSize (Equiv.swap (6 : Fin 8) 7 j) = classSize j := by
  decide

theorem nat_card_classOf (k : Fin 8) : Nat.card {g : G23 // classOf g = k} = classSize k := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter_classOf]

theorem blocksIrr_eq_range_basis (basis : FiniteIrreducibleCharacterBasis G23) :
    CFSG.BlocksIrr G23 = Set.range fun label => (basis.representation label).character := by
  rw [CFSG.blocksIrr_eq_irreducible_characters]
  ext χ
  constructor
  · rintro ⟨data, hirr, rfl⟩
    obtain ⟨label, hlabel⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr
    exact ⟨label, hlabel⟩
  · rintro ⟨label, rfl⟩
    exact ⟨basis.representation label, basis.irreducible label, rfl⟩

end GL2ThreeCharacters

open GL2ThreeCharacters CFSG.TwoRankLowerBound.Helpers in
theorem GL2_three_ordinary_character_table_construction
    (basis : FiniteIrreducibleCharacterBasis (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (a p b : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (ha : orderOf a = 8)
    (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    let H := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)
    let z : H := -1
    let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)
    let ω : ℂ := ξ + ξ ^ 3
    let rep : Fin 8 → H := ![1, z, a ^ 2, p, z * p, b, a, a⁻¹]
    let size : Fin 8 → ℕ := ![1, 1, 6, 8, 8, 12, 6, 6]
    let table : Fin 8 → Fin 8 → ℂ := ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, -1, -1, -1],
      ![2, 2, 2, -1, -1, 0, 0, 0], ![3, 3, -1, 0, 0, -1, 1, 1], ![3, 3, -1, 0, 0, 1, -1, -1],
      ![4, -4, 0, 1, -1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, ω, -ω], ![2, -2, 0, -1, 1, 0, -ω, ω]]
    ω ^ 2 = -2 ∧
    (∀ g : H, ∃ j, IsConj (rep j) g) ∧ (∀ i j, IsConj (rep i) (rep j) → i = j) ∧
    (∀ j, Nat.card {g : H // IsConj (rep j) g} = size j) ∧
    ∃ φ : Fin 8 → basis.index, Function.Bijective φ ∧
      (∀ i, (basis.representation (φ i)).IsIrreducible) ∧
      (∀ i j, (basis.representation (φ i)).character (rep j) = table i j) ∧
      CFSG.BlocksIrr H = Set.range fun i => (basis.representation (φ i)).character := by
  intro H z ξ ω rep size table
  have hξ : ξ = xi := by
    simp only [ξ, xi, cyclicRoot]
    norm_num
  have hω : ω = omega8 := by
    show ξ + ξ ^ 3 = omega8
    rw [hξ]
  have hneg : ∀ x : H, x * -1 = -1 * x := fun x => by rw [mul_neg_one, neg_one_mul]
  have hbneg : b ≠ -1 := fun h =>
    hbz (h ▸ Subgroup.mem_center_iff.mpr fun x => hneg x)
  obtain ⟨ha67, ha2⟩ := classOf_of_orderOf_eight ha
  obtain ⟨hp3, hzp⟩ := classOf_of_orderOf_three hp
  have hb5 := classOf_of_orderOf_two hb hbneg
  choose ℓ hℓ using exists_label basis
  have hℓinj : Function.Injective ℓ := fun i j h => psi_injective (by rw [← hℓ, ← hℓ, h])
  have hcard := card_basis_index_le basis
  have key : ∀ σ : Fin 8 → Fin 8, (∀ j, σ (σ j) = j) → (∀ j, classOf (rep j) = σ j) →
      (∀ j, classSize (σ j) = classSize j) →
      (∀ i j, tableA (σ i) (σ j) = tableA i j ∧ tableB (σ i) (σ j) = tableB i j) →
      (∀ g : H, ∃ j, IsConj (rep j) g) ∧ (∀ i j, IsConj (rep i) (rep j) → i = j) ∧
      (∀ j, Nat.card {g : H // IsConj (rep j) g} = size j) ∧
      ∃ φ : Fin 8 → basis.index, Function.Bijective φ ∧
        (∀ i, (basis.representation (φ i)).IsIrreducible) ∧
        (∀ i j, (basis.representation (φ i)).character (rep j) = table i j) ∧
        CFSG.BlocksIrr H = Set.range fun i => (basis.representation (φ i)).character := by
    intro σ hσσ hrep hsize htable
    have hσinj : Function.Injective σ := fun i j h => by rw [← hσσ i, h, hσσ j]
    refine ⟨fun g => ⟨σ (classOf g), ?_⟩, fun i j h => ?_, fun j => ?_, ?_⟩
    · rw [isConj_iff_classOf, hrep, hσσ]
    · rw [isConj_iff_classOf, hrep, hrep] at h
      exact hσinj h
    · have e : {g : H // IsConj (rep j) g} ≃ {g : H // classOf g = σ j} :=
        Equiv.subtypeEquivRight fun g => by rw [isConj_iff_classOf, hrep, eq_comm]
      rw [Nat.card_congr e, nat_card_classOf, hsize]
      fin_cases j <;> rfl
    · have hφinj : Function.Injective fun i => ℓ (σ i) := hℓinj.comp hσinj
      have hbij : Function.Bijective fun i => ℓ (σ i) := by
        rw [Fintype.bijective_iff_injective_and_card]
        refine ⟨hφinj, ?_⟩
        have h8 := Fintype.card_le_of_injective _ hφinj
        simp only [Fintype.card_fin] at h8 ⊢
        omega
      refine ⟨fun i => ℓ (σ i), hbij, fun i => basis.irreducible _, fun i j => ?_, ?_⟩
      · rw [hℓ, psi_eq_table, hrep, (htable i j).1, (htable i j).2]
        fin_cases i <;> fin_cases j <;> simp [table, tableA, tableB, hω]
      · rw [blocksIrr_eq_range_basis basis]
        ext χ
        constructor
        · rintro ⟨label, rfl⟩
          obtain ⟨i, hi⟩ := hbij.2 label
          exact ⟨i, by rw [← hi]⟩
        · rintro ⟨i, rfl⟩
          exact ⟨_, rfl⟩
  refine ⟨hω ▸ omega8_sq, ?_⟩
  rcases ha67 with h6 | h7
  · refine key id (fun _ => rfl) (fun j => ?_) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl⟩)
    fin_cases j
    · exact classOf_one
    · exact classOf_neg_one
    · exact ha2
    · exact hp3
    · exact hzp
    · exact hb5
    · exact h6
    · show classOf a⁻¹ = 7
      rw [classOf_inv, h6]
      rfl
  · refine key (Equiv.swap (6 : Fin 8) 7) (fun j => Equiv.swap_apply_self _ _ j) (fun j => ?_)
      classSize_swap table_swap
    fin_cases j
    · exact classOf_one
    · exact classOf_neg_one
    · exact ha2
    · exact hp3
    · exact hzp
    · exact hb5
    · exact h7
    · show classOf a⁻¹ = 6
      rw [classOf_inv, h7]
      rfl

end CFSG.Semidihedral.Principal
