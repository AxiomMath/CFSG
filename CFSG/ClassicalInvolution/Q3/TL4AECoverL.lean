module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverJ

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {A : Type*} [CommGroup A] {k : ℕ} (u : Fin k → A)

@[expose] def sv (v : Fin k → ZMod 2) : A := ∏ p, u p ^ (v p).val

theorem sv_zero : sv u 0 = 1 := by
  simp [sv]

theorem pow_val_add {x : A} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  fin_cases a <;> fin_cases b
  · show x ^ 0 = x ^ 0 * x ^ 0
    rw [pow_zero, one_mul]
  · show x ^ 1 = x ^ 0 * x ^ 1
    rw [pow_zero, one_mul]
  · show x ^ 1 = x ^ 1 * x ^ 0
    rw [pow_zero, mul_one]
  · show x ^ 0 = x ^ 1 * x ^ 1
    rw [pow_zero, pow_one, hx]

theorem sv_add (hu : ∀ p, u p * u p = 1) (v w : Fin k → ZMod 2) :
    sv u (v + w) = sv u v * sv u w := by
  rw [sv, sv, sv, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => pow_val_add (hu p) (v p) (w p)

theorem map_sv (c : A →* A) (σ : Equiv.Perm (Fin k)) (hc : ∀ p, c (u p) = u (σ p))
    (v : Fin k → ZMod 2) : c (sv u v) = sv u fun q => v (σ.symm q) := by
  rw [sv, map_prod, sv]
  simp only [map_pow, hc]
  exact Fintype.prod_equiv σ _ _ fun p => by rw [Equiv.symm_apply_apply]

variable {M : Type*} [Group M]

theorem f_prod_eq (f : A →* AEQ k) (hf : ∀ p, f (u p) = ePt k p) (v : Fin k → ZMod 2)
    (S : Finset (Fin k)) :
    f (∏ p ∈ S, u p ^ (v p).val) = mkQ k (ofVec fun i => if i ∈ S then v i else 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, map_one, Finset.notMem_empty, ite_false]
    rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, map_mul, ih, map_pow, hf, ePt, mkQ_ofVec_pow, ← map_mul,
      ← ofVec_add]
    congr 2
    funext i
    rw [Pi.add_apply, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
    by_cases hia : i = a
    · subst hia
      simp [ha]
    · simp [hia]

theorem f_sv (f : A →* AEQ k) (hf : ∀ p, f (u p) = ePt k p) (v : Fin k → ZMod 2) :
    f (sv u v) = mkQ k (ofVec v) := by
  rw [sv, f_prod_eq u f hf v Finset.univ]
  simp

theorem eq_one_of_sv (hk : Odd k) (f : A →* AEQ k) (hf : ∀ p, f (u p) = ePt k p)
    {v : Fin k → ZMod 2} (hv : ∑ i, v i = 0) (h1 : f (sv u v) = 1) : sv u v = 1 := by
  rw [f_sv u f hf] at h1
  rw [eq_zero_of_mkQ_ofVec_eq_one hk hv h1, sv_zero]

end CFSG.ClassicalInvolution.Q3.TL4.AECov
