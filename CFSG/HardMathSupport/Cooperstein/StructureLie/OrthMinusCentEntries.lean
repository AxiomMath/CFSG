module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusMat
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentMatrix

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Steinberg.SpinFrame

variable {n : ℕ} {K : Type} [Field K] {b c : K}

abbrev SM (n : ℕ) := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2

@[expose] def iota : Fin (n - 1) ⊕ Fin (n - 1) → SM n
  | .inl a => .inl a
  | .inr a => .inr (.inl a)

theorem iota_injective : Function.Injective (iota (n := n)) := by
  rintro (a | a) (a' | a') h <;> simp_all [iota]

theorem iota_kap (m : Fin (n - 1)) (r : Bool) : iota (kap m r) = minusPos n m r := by
  cases r <;> rfl

@[expose] def restr (G : Matrix (SM n) (SM n) K) : Matrix (Fin (n - 1) ⊕ Fin (n - 1))
    (Fin (n - 1) ⊕ Fin (n - 1)) K := fun x y => G (iota x) (iota y)

theorem comm_entries_long_mat {a b' : Fin (n - 1)} (hab : a ≠ b') (t : Bool)
    (G : Matrix (SM n) (SM n) K)
    (hG : G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) =
      mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) * G) (x y : SM n) :
    G x (minusPos n a true) * (if y = minusPos n b' (!t) then 1 else 0) -
        G x (minusPos n b' t) * (if y = minusPos n a false then 1 else 0) =
      (if x = minusPos n a true then 1 else 0) * G (minusPos n b' (!t)) y -
        (if x = minusPos n b' t then 1 else 0) * G (minusPos n a false) y := by
  have h := congrFun (congrFun hG x) y
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  simp only [mat_longRoot_apply (K := K) (b := b) (c := c) n hab true t 1, Bool.not_true, one_mul,
    mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    ite_mul, mul_one, mul_zero, zero_mul, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  by_cases hxp : x = minusPos n a true <;> by_cases hxr : x = minusPos n b' t <;>
    by_cases hyr : y = minusPos n b' (!t) <;> by_cases hyp : y = minusPos n a false <;>
    simp [hxp, hxr, hyr, hyp, eq_comm] at h ⊢ <;> first | done | linear_combination h

theorem comm_entries_long {a b' : Fin (n - 1)} (hab : a ≠ b') (t : Bool)
    (k : spinGroup (quadMinus n K b c))
    (hk : k * (minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1) =
      (minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1) * k) (x y : SM n) :
    mat n k x (minusPos n a true) * (if y = minusPos n b' (!t) then 1 else 0) -
        mat n k x (minusPos n b' t) * (if y = minusPos n a false then 1 else 0) =
      (if x = minusPos n a true then 1 else 0) * mat n k (minusPos n b' (!t)) y -
        (if x = minusPos n b' t then 1 else 0) * mat n k (minusPos n a false) y :=
  comm_entries_long_mat hab t (mat n k) (by rw [← mat_mul, ← mat_mul, hk]) x y

theorem hm_restr_mat {a b' : Fin (n - 1)} (hab : a ≠ b') (t : Bool) (G : Matrix (SM n) (SM n) K)
    (hG : G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) =
      mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) * G) :
    HM (restr G) (kap a true) (kap b' t) := by
  intro x y
  have h := comm_entries_long_mat hab t G hG (iota x) (iota y)
  rw [bar_kap, bar_kap]
  simp only [← iota_kap, iota_injective.eq_iff] at h
  simpa only [restr, ← iota_kap, Bool.not_true] using h

@[expose] def pl (n : ℕ) (u : Fin 2) : SM n := .inr (.inr u)

@[expose] def planeN (c : K) (u : Fin 2) : K := if u = 0 then 1 else c

theorem shortMat_entry [CharP K 2] (a : Fin (n - 1)) (s : Bool) (u : Fin 2) (x y : SM n) :
    shortMat b c n a s (Pi.single u 1) x y =
      (if x = y then 1 else 0) + (if x = pl n u then 1 else 0) * (if y = minusPos n a (!s) then 1 else 0) -
        (if x = minusPos n a s then 1 else 0) *
          (b * (if y = pl n (1 - u) then 1 else 0) +
            planeN c u * (if y = minusPos n a (!s) then 1 else 0)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hpv : planeVec n (Pi.single u (1 : K)) = Pi.single (pl n u) 1 :=
    (single_inr_inr_eq_planeVec u).symm
  have hpolar : ∀ y : SM n, polarVec b c n (Pi.single u (1 : K)) y =
      b * (if y = pl n (1 - u) then 1 else 0) := by
    intro y
    unfold polarVec
    rw [hpv]
    revert u
    refine Fin.forall_fin_two.mpr ⟨fun hpv => ?_, fun hpv => ?_⟩
    · show QuadraticMap.polar (quadMinus n K b c) (Pi.single y 1) (Pi.single (pl n 0) 1) = b * if y = pl n (1 - 0) then 1 else 0
      rw [show pl n 0 = .inr (.inr 0) from rfl, polar_quadMinus_single_inr_inr_zero, h2]
      by_cases hy : y = pl n 1
      · subst hy; simp [pl, Pi.single_apply]
      · have : (Pi.single y (1 : K) : SM n → K) (.inr (.inr 1)) = 0 := by
          rw [Pi.single_apply, if_neg]; exact fun h => hy h.symm
        rw [this]; simp only [pl, zero_mul, add_zero, zero_add, Fin.isValue]; simp; intro h; exact absurd h hy
    · show QuadraticMap.polar (quadMinus n K b c) (Pi.single y 1) (Pi.single (pl n 1) 1) = b * if y = pl n (1 - 1) then 1 else 0
      rw [show pl n 1 = .inr (.inr 1) from rfl, polar_quadMinus_single_inr_inr_one, h2]
      by_cases hy : y = pl n 0
      · subst hy; simp [pl, Pi.single_apply]
      · have : (Pi.single y (1 : K) : SM n → K) (.inr (.inr 0)) = 0 := by
          rw [Pi.single_apply, if_neg]; exact fun h => hy h.symm
        rw [this]; simp only [pl, zero_mul, add_zero, zero_add, Fin.isValue]; simp; intro h; exact absurd h hy
  have hN : planeNorm b c (Pi.single u (1 : K)) = planeN c u := by
    fin_cases u <;> simp [planeNorm, planeN]
  simp only [shortMat, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpolar, hN, hpv, Pi.single_apply]

theorem comm_entries_short_mat (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) [CharP K 2]
    (a : Fin (n - 1)) (u : Fin 2) (G : Matrix (SM n) (SM n) K)
    (hG : G * mat n (twShortRoot n hirr a true (Multiplicative.ofAdd (Pi.single u 1))) =
      mat n (twShortRoot n hirr a true (Multiplicative.ofAdd (Pi.single u 1))) * G) (x y : SM n) :
    G x (pl n u) * (if y = minusPos n a false then 1 else 0) -
        G x (minusPos n a true) * (b * (if y = pl n (1 - u) then 1 else 0) +
          planeN c u * (if y = minusPos n a false then 1 else 0)) =
      (if x = pl n u then 1 else 0) * G (minusPos n a false) y -
        (if x = minusPos n a true then 1 else 0) *
          (b * G (pl n (1 - u)) y + planeN c u * G (minusPos n a false) y) := by
  have h := congrFun (congrFun hG x) y
  rw [mat_twShortRoot_eq hirr, Matrix.mul_apply, Matrix.mul_apply] at h
  simp only [shortMat_entry, Bool.not_true, mul_add, mul_sub, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    one_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  by_cases h1 : x = minusPos n a true <;> by_cases h2 : y = pl n (1 - u) <;>
    by_cases h3 : y = minusPos n a false <;> by_cases h4 : x = pl n u <;>
    simp only [h1, h2, h3, h4, if_true, if_false, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      one_mul, mul_add] at h ⊢ <;> linear_combination h

end CFSG.HardMathSupport.Cooperstein.StructureLie
