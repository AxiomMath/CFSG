module

public import CFSG.CharacterTheory.Semidihedral.OddLinearNormals
public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.CharacterTheory.Semidihedral.QuaternionAutomorphismLifting

public section

namespace CFSG.Semidihedral.OddFieldSL2

open Matrix
open CFSG.Open

universe u

variable (F : Type u) [Field F]

@[expose] def minusIdentity : SpecialLinearGroup (Fin 2) F := -1

theorem minusIdentity_matrix :
    (minusIdentity F : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusIdentity]

theorem quarterTurn_square :
    (OddLinearNormals.quarterTurn F) ^ 2 = minusIdentity F := by
  apply Subtype.ext
  exact (OddLinearNormals.quarterTurn_square_matrix F).trans
    (minusIdentity_matrix F).symm

theorem minusIdentity_mem_center :
    minusIdentity F ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [← quarterTurn_square]
  exact OddLinearNormals.quarterTurn_square_mem_center F

theorem minusIdentity_square : (minusIdentity F) ^ 2 = 1 := by
  simp [minusIdentity, pow_two]

theorem minusIdentity_ne_one (h2 : (2 : F) ≠ 0) : minusIdentity F ≠ 1 := by
  intro h
  have hentry := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have hn : (-1 : F) = 1 := by simpa [minusIdentity] using hentry
  apply h2
  linear_combination -hn

theorem minusIdentity_orderOf (h2 : (2 : F) ≠ 0) : orderOf (minusIdentity F) = 2 := by
  apply orderOf_eq_prime
  · exact minusIdentity_square F
  · exact minusIdentity_ne_one F h2

theorem eq_one_or_minusIdentity_of_inv_eq_self (h2 : (2 : F) ≠ 0)
    (x : SpecialLinearGroup (Fin 2) F) (hx : x⁻¹ = x) :
    x = 1 ∨ x = minusIdentity F := by
  have hm := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F)) hx
  rw [SpecialLinearGroup.SL2_inv_expl] at hm
  have hd : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = x.1 0 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hm
  have hb : -(x.1 0 1) = x.1 0 1 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hm
  have hc : -(x.1 1 0) = x.1 1 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hm
  have hb0 : x.1 0 1 = 0 := by
    apply (mul_eq_zero.mp (show (2 : F) * x.1 0 1 = 0 by linear_combination -hb)).resolve_left h2
  have hc0 : x.1 1 0 = 0 := by
    apply (mul_eq_zero.mp (show (2 : F) * x.1 1 0 = 0 by linear_combination -hc)).resolve_left h2
  have ha : (x.1 0 0) ^ 2 = 1 := by
    simpa only [Matrix.det_fin_two, hd, hb0, hc0, zero_mul, sub_zero, pow_two] using x.2
  rcases sq_eq_one_iff.mp ha with ha1 | han
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, hb0, hc0, ha1]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [minusIdentity, hd, hb0, hc0, han]

theorem orderOf_eq_two_iff (h2 : (2 : F) ≠ 0)
    (x : SpecialLinearGroup (Fin 2) F) : orderOf x = 2 ↔ x = minusIdentity F := by
  constructor
  · intro hx
    rcases eq_one_or_minusIdentity_of_inv_eq_self F h2 x
      (inv_eq_self_of_orderOf_eq_two hx) with h1 | hn
    · simp [h1] at hx
    · exact hn
  · rintro rfl
    exact minusIdentity_orderOf F h2


@[expose] def secondGenerator (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, b; b, -a], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hab⟩

theorem secondGenerator_square (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    (secondGenerator F a b hab) ^ 2 = minusIdentity F := by
  apply Subtype.ext
  change (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa only [pow_two] using hab
  · ring
  · ring
  · simpa only [pow_two, add_comm] using hab

theorem quarterTurn_period : (OddLinearNormals.quarterTurn F) ^ 4 = 1 := by
  calc
    (OddLinearNormals.quarterTurn F) ^ 4 =
        ((OddLinearNormals.quarterTurn F) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [quarterTurn_square, minusIdentity_square]

theorem generators_inversion (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    OddLinearNormals.quarterTurn F * secondGenerator F a b hab =
      secondGenerator F a b hab * (OddLinearNormals.quarterTurn F)⁻¹ := by
  have hm : (OddLinearNormals.quarterTurn F : Matrix (Fin 2) (Fin 2) F) *
      (secondGenerator F a b hab : Matrix (Fin 2) (Fin 2) F) =
    (secondGenerator F a b hab : Matrix (Fin 2) (Fin 2) F) *
      (((OddLinearNormals.quarterTurn F)⁻¹ : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    change (OddLinearNormals.quarterTurn F : Matrix (Fin 2) (Fin 2) F) *
        (secondGenerator F a b hab : Matrix (Fin 2) (Fin 2) F) =
      (secondGenerator F a b hab : Matrix (Fin 2) (Fin 2) F) *
        Matrix.of ![![(OddLinearNormals.quarterTurn F).1 1 1,
          -(OddLinearNormals.quarterTurn F).1 0 1],
          ![-(OddLinearNormals.quarterTurn F).1 1 0, (OddLinearNormals.quarterTurn F).1 0 0]]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [secondGenerator, OddLinearNormals.quarterTurn, Matrix.mul_apply, Fin.sum_univ_two]
  exact Subtype.ext hm

@[expose] noncomputable def quaternionHom (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    QuaternionGroup 2 →* SpecialLinearGroup (Fin 2) F :=
  CFSG.TwoRankLowerBound.Helpers.quaternionNormalFormHom 2
    (QuaternionAutomorphismLifting.coordinatePowerHom 4
      (OddLinearNormals.quarterTurn F) (quarterTurn_period F))
    (secondGenerator F a b hab)
    (by rw [QuaternionAutomorphismLifting.coordinatePowerHom_natCast,
      secondGenerator_square, quarterTurn_square])
    (fun i => QuaternionAutomorphismLifting.power_passes_outside _ _
      (generators_inversion F a b hab) i.val)

theorem quaternionHom_half (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    quaternionHom F a b hab (QuaternionGroup.a (2 : ZMod 4)) = minusIdentity F := by
  change QuaternionAutomorphismLifting.coordinatePowerHom 4
    (OddLinearNormals.quarterTurn F) (quarterTurn_period F)
    (Multiplicative.ofAdd (2 : ZMod 4)) = minusIdentity F
  simpa only [Nat.cast_ofNat] using
    (QuaternionAutomorphismLifting.coordinatePowerHom_natCast 4
      (OddLinearNormals.quarterTurn F) (quarterTurn_period F) 2).trans (quarterTurn_square F)

theorem quaternionHom_rotation (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    quaternionHom F a b hab (QuaternionGroup.a (1 : ZMod 4)) =
      OddLinearNormals.quarterTurn F := by
  change QuaternionAutomorphismLifting.coordinatePowerHom 4
    (OddLinearNormals.quarterTurn F) (quarterTurn_period F)
    (Multiplicative.ofAdd (1 : ZMod 4)) = OddLinearNormals.quarterTurn F
  simpa only [Nat.cast_one, pow_one] using
    QuaternionAutomorphismLifting.coordinatePowerHom_natCast 4
      (OddLinearNormals.quarterTurn F) (quarterTurn_period F) 1

theorem quaternionHom_outside (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    quaternionHom F a b hab (QuaternionGroup.xa (0 : ZMod 4)) =
      secondGenerator F a b hab := by
  change secondGenerator F a b hab *
    QuaternionAutomorphismLifting.coordinatePowerHom 4
      (OddLinearNormals.quarterTurn F) (quarterTurn_period F) 1 = _
  rw [map_one, mul_one]

theorem quaternionEight_nonidentity : ∀ q : QuaternionGroup 2,
    q ≠ 1 → q = QuaternionGroup.a (2 : ZMod 4) ∨
      q ^ 2 = QuaternionGroup.a (2 : ZMod 4) := by decide

theorem quaternionHom_injective (h2 : (2 : F) ≠ 0)
    (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    Function.Injective (quaternionHom F a b hab) := by
  apply (injective_iff_map_eq_one _).mpr
  intro q hq
  by_contra hn
  rcases quaternionEight_nonidentity q hn with hhalf | hsquare
  · rw [hhalf, quaternionHom_half] at hq
    exact minusIdentity_ne_one F h2 hq
  · have he := congrArg (quaternionHom F a b hab) hsquare
    rw [map_pow, hq, one_pow, quaternionHom_half] at he
    exact minusIdentity_ne_one F h2 he.symm

@[expose] noncomputable def quaternionSubgroup (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    Subgroup (SpecialLinearGroup (Fin 2) F) := (quaternionHom F a b hab).range

@[expose] noncomputable def quaternionSubgroupEquiv (h2 : (2 : F) ≠ 0)
    (a b : F) (hab : a ^ 2 + b ^ 2 = -1) :
    quaternionSubgroup F a b hab ≃* QuaternionGroup 2 :=
  (MulEquiv.ofBijective (quaternionHom F a b hab).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (quaternionHom_injective F h2 a b hab),
      MonoidHom.rangeRestrict_surjective _⟩).symm

theorem quaternionEight_noncommutative : ¬IsMulCommutative (QuaternionGroup 2) := by
  intro h
  have he := isMulCommutative_iff.mp h
    (QuaternionGroup.a (1 : ZMod 4)) (QuaternionGroup.xa (0 : ZMod 4))
  have hn : (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2) *
      QuaternionGroup.xa 0 ≠ QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  exact hn he

section FiniteField

variable [Finite F]

theorem two_ne_zero_of_odd_card (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  let : Fintype F := Fintype.ofFinite F
  have hm : Fintype.card F % 2 = 1 :=
    Nat.odd_iff.mp (by simpa only [Nat.card_eq_fintype_card] using hodd)
  apply Ring.two_ne_zero
  intro hc
  have he := FiniteField.even_card_of_char_two hc
  omega

theorem sum_two_squares (hodd : Odd (Nat.card F)) (c : F) :
    ∃ a b : F, a ^ 2 + b ^ 2 = c := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let f : Polynomial F := Polynomial.X ^ 2
  let g : Polynomial F := Polynomial.X ^ 2 - Polynomial.C c
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := f) (g := g) (Polynomial.degree_X_pow 2)
    (Polynomial.degree_X_pow_sub_C (by decide) c)
    (Nat.odd_iff.mp (by simpa only [Nat.card_eq_fintype_card] using hodd))
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [f, g, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_sub, ← add_sub_assoc] using hab

theorem twoRank_le_one (hodd : Odd (Nat.card F)) :
    twoRank (SpecialLinearGroup (Fin 2) F) ≤ 1 := by
  apply csSup_le'
  rintro rank ⟨E, _, hE, hcard⟩
  have h2 := two_ne_zero_of_odd_card F hodd
  have hsub : (E : Set (SpecialLinearGroup (Fin 2) F)) ⊆ {1, minusIdentity F} := by
    intro x hx
    by_cases h1 : x = 1
    · simp [h1]
    · have ho : orderOf x = 2 := orderOf_eq_prime (hE.2 x hx) h1
      simp [(orderOf_eq_two_iff F h2 x).mp ho]
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair (minusIdentity_ne_one F h2).symm] at hle
  change Nat.card E ≤ 2 at hle
  rw [hcard] at hle
  by_contra hn
  have hlarge : 2 ^ 2 ≤ 2 ^ rank := pow_le_pow_right' (by omega) (by omega)
  norm_num at hlarge
  omega

theorem exists_quaternionSubgroup (hodd : Odd (Nat.card F)) :
    ∃ Q : Subgroup (SpecialLinearGroup (Fin 2) F), Nonempty (Q ≃* QuaternionGroup 2) := by
  obtain ⟨a, b, hab⟩ := sum_two_squares F hodd (-1)
  exact ⟨quaternionSubgroup F a b hab,
    ⟨quaternionSubgroupEquiv F (two_ne_zero_of_odd_card F hodd) a b hab⟩⟩

theorem exists_quaternion_embedding_in_sylow (hodd : Odd (Nat.card F))
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) F)) :
    ∃ f : QuaternionGroup 2 →* (P : Subgroup (SpecialLinearGroup (Fin 2) F)),
      Function.Injective f := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_quaternionSubgroup F hodd
  have hQ : IsPGroup 2 Q := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  let f := ((Sylow.equiv S P).toMonoidHom.comp (Subgroup.inclusion hQS)).comp e.symm.toMonoidHom
  exact ⟨f, (Sylow.equiv S P).injective.comp
    ((Subgroup.inclusion_injective hQS).comp e.symm.injective)⟩

theorem sylow_two_not_isMulCommutative (hodd : Odd (Nat.card F))
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) F)) :
    ¬IsMulCommutative (P : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
  obtain ⟨f, hf⟩ := exists_quaternion_embedding_in_sylow F hodd P
  intro h
  apply quaternionEight_noncommutative
  apply isMulCommutative_iff.mpr
  intro x y
  apply hf
  rw [map_mul, map_mul, isMulCommutative_iff.mp h]

theorem sylow_two_quaternion (hodd : Odd (Nat.card F))
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) F)) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty
      ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) ≃* QuaternionGroup (2 ^ (n - 2))) := by
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion
    (P : Subgroup (SpecialLinearGroup (Fin 2) F)) P.isPGroup'
    ((CFSG.TwoRankLowerBound.Helpers.twoRank_subgroup_le _).trans (twoRank_le_one F hodd))
    with hcyclic | hquaternion
  · let : IsCyclic (P : Subgroup (SpecialLinearGroup (Fin 2) F)) := hcyclic
    exact False.elim (sylow_two_not_isMulCommutative F hodd P inferInstance)
  · exact hquaternion

theorem odd_field_involution_structure (hodd : Odd (Nat.card F)) :
    minusIdentity F ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∧
    orderOf (minusIdentity F) = 2 ∧
    (∀ x : SpecialLinearGroup (Fin 2) F, orderOf x = 2 ↔ x = minusIdentity F) ∧
    (∃ Q : Subgroup (SpecialLinearGroup (Fin 2) F), Nonempty (Q ≃* QuaternionGroup 2)) ∧
    (∀ P : Sylow 2 (SpecialLinearGroup (Fin 2) F),
      ¬IsMulCommutative (P : Subgroup (SpecialLinearGroup (Fin 2) F))) :=
  ⟨minusIdentity_mem_center F, minusIdentity_orderOf F (two_ne_zero_of_odd_card F hodd),
    orderOf_eq_two_iff F (two_ne_zero_of_odd_card F hodd), exists_quaternionSubgroup F hodd,
    sylow_two_not_isMulCommutative F hodd⟩

end FiniteField

end CFSG.Semidihedral.OddFieldSL2
