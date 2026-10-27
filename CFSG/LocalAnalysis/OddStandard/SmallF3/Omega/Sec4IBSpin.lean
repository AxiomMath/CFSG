module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBMono

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sec4IZMod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private lemma sec4ISgn_one : sec4ISgn 1 = -1 := by decide

theorem sec4I_isEvenVec_iff_even_vecWeight {n : ℕ} (v : Fin n → ZMod 2) :
    IsEvenVec v ↔ Even (vecWeight v) := by
  unfold IsEvenVec vecWeight
  have h1 : (∑ i, v i) = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), v i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : v i = 0 <;> simp [h]
  rw [h1]
  have h2 : (∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), v i)
      = ∑ _i ∈ Finset.univ.filter (fun i => v i ≠ 0), (1 : ZMod 2) :=
    Finset.sum_congr rfl fun i hi =>
      sec4IZMod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi).2
  rw [h2, Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff_even]

private noncomputable def sec4INegClass : Multiplicative (SquareClassGroup (ZMod 3)) :=
  Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))

private lemma sec4INegClass_sq : sec4INegClass ^ 2 = 1 := by
  unfold sec4INegClass
  rw [pow_two, ← ofAdd_add]
  have h : squareClass (-1 : (ZMod 3)ˣ) + squareClass (-1 : (ZMod 3)ˣ) = 0 := by
    rw [← squareClass_mul]
    exact (squareClass_eq_zero_iff _).mpr ⟨(1 : (ZMod 3)ˣ), by simp⟩
  rw [h, ofAdd_zero]

private lemma sec4INegClass_ne_one : sec4INegClass ≠ 1 := by
  intro h
  rw [sec4INegClass] at h
  exact aux_squareClass_neg_one_ne_zero (ofAdd_eq_one.mp h)

private lemma pow_eq_one_iff_even_of_sq_eq_one {G : Type*} [Group G] {g : G}
    (h2 : g ^ 2 = 1) (h1 : g ≠ 1) (n : ℕ) : g ^ n = 1 ↔ Even n := by
  constructor
  · intro h
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exfalso
      obtain ⟨k, rfl⟩ := ho
      rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h
      exact h1 h
  · intro he
    obtain ⟨k, rfl⟩ := he
    rw [show k + k = 2 * k by ring, pow_mul, h2, one_pow]

private lemma sec4INegClass_pow_eq_one_iff (n : ℕ) : sec4INegClass ^ n = 1 ↔ Even n :=
  pow_eq_one_iff_even_of_sq_eq_one sec4INegClass_sq sec4INegClass_ne_one n

private noncomputable def sec4ISignUnit : ℤˣ →* (ZMod 3)ˣ :=
  Units.map (Int.castRingHom (ZMod 3))

private lemma sec4ISignUnit_neg_one : sec4ISignUnit (-1 : ℤˣ) = -1 := by
  ext
  simp [sec4ISignUnit]

private lemma sec4ISignUnit_eq_one_iff (s : ℤˣ) : sec4ISignUnit s = 1 ↔ s = 1 := by
  rcases Int.units_eq_one_or s with h | h
  · rw [h, map_one]
    simp
  · rw [h]
    constructor
    · intro hh
      rw [sec4ISignUnit_neg_one] at hh
      exact absurd hh (by decide : (-1 : (ZMod 3)ˣ) ≠ 1)
    · intro hh
      exact absurd hh (by decide : (-1 : ℤˣ) ≠ 1)

private theorem sec4IT_single_eq_reflection (fr : Sec4IFrame Q) (i : Fin 7)
    [Invertible (Q (fr.b i))] :
    sec4IT fr (Pi.single i 1) = TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b i) := by
  apply sec4I_ogroup_ext fr
  intro j
  rw [sec4IT_apply_basis, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
  by_cases hji : j = i
  · rw [hji]
    rw [Pi.single_eq_same, sec4ISgn_one, Units.val_neg, Units.val_one, polar_self, fr.neg]
    have h2 : (2 : ℕ) • (-1 : ZMod 3) = 1 := by decide
    have h3 : (1 : ZMod 3) / (-1) = -1 := by rw [div_neg, div_one]
    rw [h2, h3, neg_one_smul, sub_neg_eq_add, ← two_smul (ZMod 3) (fr.b i)]
    have h4 : (2 : ZMod 3) = -1 := by decide
    rw [h4, neg_one_smul]
  · rw [Pi.single_eq_of_ne hji, sec4ISgn_zero, Units.val_one, one_smul,
      fr.orth i j (Ne.symm hji)]
    simp

private theorem detSpinorNorm_sec4IT_single (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (i : Fin 7) :
    detSpinorNorm hQ (sec4IT fr (Pi.single i 1)) = ((-1 : (ZMod 3)ˣ), sec4INegClass) := by
  haveI : Invertible (Q (fr.b i)) := invertibleOfNonzero (by rw [fr.neg i]; decide)
  rw [sec4IT_single_eq_reflection fr i, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b i)) = (-1 : (ZMod 3)ˣ) :=
    Units.ext (by rw [val_unitOfInvertible, fr.neg i]; rfl)
  rw [hunit, squareClassHom_apply]
  rfl

private lemma sum_sec4IEvec_eq (s : Finset (Fin 7)) :
    (∑ x ∈ s, Pi.single x (1 : ZMod 2)) = fun a => if a ∈ s then (1 : ZMod 2) else 0 := by
  funext a
  rw [Finset.sum_apply]
  exact Finset.sum_pi_single a (fun _ => (1 : ZMod 2)) s

private lemma sum_sec4IEvec_filter (u : Fin 7 → ZMod 2) :
    (∑ i ∈ Finset.univ.filter (fun i => u i ≠ 0), Pi.single i (1 : ZMod 2)) = u := by
  rw [sum_sec4IEvec_eq]
  funext j
  by_cases hj : u j = 0
  · simp [hj]
  · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩),
      sec4IZMod2_eq_one_of_ne_zero hj]

private theorem detSpinorNorm_sec4IT_sum (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (s : Finset (Fin 7)) :
    detSpinorNorm hQ (sec4IT fr (∑ i ∈ s, Pi.single i (1 : ZMod 2))) =
      (((-1 : (ZMod 3)ˣ) ^ s.card), sec4INegClass ^ s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, sec4IT_zero fr, map_one, Finset.card_empty]
    simp only [pow_zero]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, sec4IT_add, map_mul, ih, detSpinorNorm_sec4IT_single,
      Finset.card_insert_of_notMem ha, pow_succ', pow_succ', Prod.mk_mul_mk]

private theorem detSpinorNorm_sec4IT (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (u : Fin 7 → ZMod 2) :
    detSpinorNorm hQ (sec4IT fr u) =
      (((-1 : (ZMod 3)ˣ) ^ vecWeight u), sec4INegClass ^ vecWeight u) := by
  have hsum := sum_sec4IEvec_filter u
  conv_lhs => rw [← hsum]
  rw [detSpinorNorm_sec4IT_sum]
  simp only [vecWeight]

private lemma sec4IQ_sub (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b) :
    Q (fr.b a - fr.b b) = 1 := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, QuadraticMap.polar_neg_right,
    fr.neg a, fr.neg b, fr.orth a b hab, neg_zero, add_zero]
  decide

private lemma sec4I_polar_sub_left (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b a) = 1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self,
    QuadraticMap.polar_comm Q (fr.b b) (fr.b a), fr.neg a, fr.orth a b hab]
  decide

private lemma sec4I_polar_sub_right (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b b) = -1 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, fr.neg b, fr.orth a b hab]
  decide

private lemma sec4I_polar_sub_of_ne (fr : Sec4IFrame Q) {a b c : Fin 7}
    (hca : c ≠ a) (hcb : c ≠ b) :
    polar Q (fr.b a - fr.b b) (fr.b c) = 0 := by
  rw [QuadraticMap.polar_sub_left, fr.orth a c hca.symm, fr.orth b c hcb.symm]
  decide

private theorem sec4IP_swap_eq_reflection (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b)
    [Invertible (Q (fr.b a - fr.b b))] :
    sec4IP fr (Equiv.swap a b) = TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.b a - fr.b b) := by
  apply sec4I_ogroup_ext fr
  intro c
  rw [sec4IP, sec4IMono_apply, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.reflection_apply_eq_sub_div, sec4IQ_sub fr hab]
  by_cases hca : c = a
  · subst hca
    rw [Equiv.swap_apply_left, Pi.zero_apply, sec4ISgn_zero, Units.val_one, one_smul,
      sec4I_polar_sub_left fr hab, div_one, one_smul]
    abel
  · by_cases hcb : c = b
    · subst hcb
      rw [Equiv.swap_apply_right, Pi.zero_apply, sec4ISgn_zero, Units.val_one, one_smul,
        sec4I_polar_sub_right fr hab, div_one]
      module
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb, Pi.zero_apply, sec4ISgn_zero, Units.val_one,
        one_smul, sec4I_polar_sub_of_ne fr hca hcb, zero_div, zero_smul, sub_zero]

private theorem detSpinorNorm_sec4IP_swap (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {a b : Fin 7} (hab : a ≠ b) :
    detSpinorNorm hQ (sec4IP fr (Equiv.swap a b)) = ((-1 : (ZMod 3)ˣ), 1) := by
  haveI : Invertible (Q (fr.b a - fr.b b)) :=
    invertibleOfNonzero (by rw [sec4IQ_sub fr hab]; decide)
  rw [sec4IP_swap_eq_reflection fr hab, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q (fr.b a - fr.b b)) = 1 :=
    Units.ext (by rw [val_unitOfInvertible, sec4IQ_sub fr hab]; rfl)
  rw [hunit, map_one]

private theorem detSpinorNorm_sec4IP (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (σ : Equiv.Perm (Fin 7)) :
    detSpinorNorm hQ (sec4IP fr σ) = (sec4ISignUnit (Equiv.Perm.sign σ), 1) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    rw [sec4IP_one, map_one, Equiv.Perm.sign_one, map_one]
    rfl
  | swap_mul τ a b hab ih =>
    rw [← sec4IP_mul, map_mul, ih, detSpinorNorm_sec4IP_swap hQ fr hab, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hab, map_mul, sec4ISignUnit_neg_one]
    simp

theorem sec4IMono_mem_omegaGroup_iff (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2) :
    sec4IMono fr σ u ∈ omegaGroup hQ ↔ Equiv.Perm.sign σ = 1 ∧ IsEvenVec u := by
  rw [mem_omegaGroup_iff hQ, sec4IMono_eq_P_mul_T, map_mul, detSpinorNorm_sec4IP hQ fr σ,
    detSpinorNorm_sec4IT hQ fr u]
  rw [show (1 : (ZMod 3)ˣ × Multiplicative (SquareClassGroup (ZMod 3))) = (1, 1) from rfl,
    Prod.mk_mul_mk, one_mul, Prod.mk.injEq]
  have hIsE : IsEvenVec u ↔ Even (vecWeight u) := sec4I_isEvenVec_iff_even_vecWeight u
  have hw : sec4INegClass ^ vecWeight u = 1 ↔ Even (vecWeight u) :=
    sec4INegClass_pow_eq_one_iff (vecWeight u)
  have hfirst : ∀ (_ : Even (vecWeight u)),
      sec4ISignUnit (Equiv.Perm.sign σ) * (-1 : (ZMod 3)ˣ) ^ vecWeight u = 1 ↔
        Equiv.Perm.sign σ = 1 := by
    intro he
    rw [he.neg_one_pow, mul_one]
    exact sec4ISignUnit_eq_one_iff _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hfirst (hw.mp h2)).mp h1, hIsE.mpr (hw.mp h2)⟩
  · rintro ⟨hs, hu⟩
    exact ⟨(hfirst (hIsE.mp hu)).mpr hs, hw.mpr (hIsE.mp hu)⟩

end CFSG.OddStandard.SmallF3.Omega
