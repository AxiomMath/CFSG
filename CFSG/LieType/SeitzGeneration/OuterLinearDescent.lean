module

public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2

section Rational

variable {K : Type*} [Field K] {n : ℕ}

theorem twistedProd_of_fixed (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K)
    (hA : A.map σ = A) (j : ℕ) : twistedProd σ A j = A ^ j := by
  induction j with
  | zero => rw [twistedProd_zero, pow_zero]
  | succ j ih =>
    rw [twistedProd_succ, ih, pow_succ', Matrix.map_pow A σ j, hA]

end Rational

section Descent

variable {K : Type} [Field K] {ℓ e p : ℕ}

theorem iterate_eq_id_of_orderOf (σ : K ≃+* K) (hσ : orderOf σ = p) (x : K) :
    (⇑σ)^[p] x = x := by
  rw [← RingAut.coe_pow, ← hσ, pow_orderOf_eq_one]
  rfl

theorem exists_fixed_matrix [Finite K] (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (σ : K ≃+* K) (hσ : orderOf σ = p) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.map σ = g) (hgp : g ^ p = 1) :
    ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M.det ∧ g * M.map σ = M := by
  have hdet : IsUnit g.det := by
    have h1 : g.det ^ p = 1 := by rw [← Matrix.det_pow, hgp, Matrix.det_one]
    exact isUnit_iff_ne_zero.mpr fun h => by
      rw [h, zero_pow hp.ne_zero] at h1
      exact zero_ne_one h1
  refine exists_isUnit_det_fixed hℓ he hK σ hσ g hdet fun v => ?_
  have h1 : twistedProd (⇑σ) g p = 1 := by
    have := twistedProd_of_fixed (σ : K →+* K) g hg p
    rw [hgp] at this
    exact this
  have h2 : (⇑σ)^[p] ∘ v = v := funext fun i => iterate_eq_id_of_orderOf σ hσ (v i)
  rw [h1, h2, Matrix.one_mulVec]

theorem iterate_mul_apply (σ : K ≃+* K) (lam : K) (j : ℕ) (v : K) :
    (fun x : K => lam * σ x)^[j] v = (∏ i ∈ Finset.range j, (σ ^ i) lam) * (σ ^ j) v := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Finset.prod_range_succ']
    have e1 : ∀ i, σ ((σ ^ i) lam) = (σ ^ (i + 1)) lam := fun i => by rw [pow_succ']; rfl
    have e2 : σ ((σ ^ j) v) = (σ ^ (j + 1)) v := by rw [pow_succ']; rfl
    rw [map_mul, map_prod]
    simp only [e1, e2, pow_zero]
    change lam * ((∏ i ∈ Finset.range j, (σ ^ (i + 1)) lam) * (σ ^ (j + 1)) v) =
      (∏ i ∈ Finset.range j, (σ ^ (i + 1)) lam) * lam * (σ ^ (j + 1)) v
    ring

theorem exists_hilbert90 [Finite K] (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (σ : K ≃+* K) (hσ : orderOf σ = p) (lam : K)
    (hN : ∏ i ∈ Finset.range p, (σ ^ i) lam = 1) : ∃ c : K, c ≠ 0 ∧ lam * σ c = c := by
  have hlam : lam ≠ 0 := by
    intro h0
    have : ∏ i ∈ Finset.range p, (σ ^ i) lam = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp [h0])
    rw [hN] at this
    exact one_ne_zero this
  let a : K ≃+ K :=
    { toFun := fun x => lam * σ x
      invFun := fun y => σ.symm (lam⁻¹ * y)
      left_inv := fun x => by simp [hlam]
      right_inv := fun y => by simp [hlam]
      map_add' := fun x y => by rw [map_add, mul_add] }
  have ha : ∀ (c v : K), a (c • v) = σ c • a v := fun c v => by
    change lam * σ (c * v) = σ c * (lam * σ v)
    rw [map_mul]
    ring
  have hah : ∀ v, (⇑a)^[p] v = v := fun v => by
    have h1 : (⇑a)^[p] v = (fun x : K => lam * σ x)^[p] v := rfl
    rw [h1, iterate_mul_apply, hN, one_mul, ← hσ, pow_orderOf_eq_one]
    rfl
  obtain ⟨-, -, -, -, b, hb, -⟩ :=
    semilinear_fixed_basis hℓ he hK σ hσ (Module.finrank_self K) a ha hah
  refine ⟨b 0, b.ne_zero 0, ?_⟩
  exact hb 0

theorem exists_rational_smul [Finite K] (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (σ : K ≃+* K) (hσ : orderOf σ = p) {n : ℕ}
    {X : Matrix (Fin n) (Fin n) K} (hX0 : X ≠ 0) {lam : K} (hX : X.map σ = lam • X) :
    ∃ c : K, c ≠ 0 ∧ (c • X).map σ = c • X := by
  have hit : ∀ j : ℕ, X.map ⇑(σ ^ j) = (∏ i ∈ Finset.range j, (σ ^ i) lam) • X := by
    intro j
    induction j with
    | zero =>
      ext a b
      simp
    | succ j ih =>
      have h1 : X.map ⇑(σ ^ (j + 1)) = (X.map ⇑(σ ^ j)).map σ := by
        ext a b
        simp only [Matrix.map_apply]
        rw [pow_succ']
        rfl
      rw [h1, ih, Finset.prod_range_succ']
      ext a b
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      have hab := congrFun (congrFun hX a) b
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hab
      rw [map_mul, map_prod, hab]
      have e1 : ∀ i, σ ((σ ^ i) lam) = (σ ^ (i + 1)) lam := fun i => by rw [pow_succ']; rfl
      simp only [e1, pow_zero]
      change _ = (∏ i ∈ Finset.range j, (σ ^ (i + 1)) lam) * lam * X a b
      ring
  have hN : ∏ i ∈ Finset.range p, (σ ^ i) lam = 1 := by
    have h1 := hit p
    have hpow : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have h2 : X.map ⇑(σ ^ p) = X := by
      rw [hpow]
      ext a b
      simp
    rw [h2] at h1
    obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hX0 (Matrix.ext hcon)
    have h3 := congrFun (congrFun h1 a) b
    simp only [Matrix.smul_apply, smul_eq_mul] at h3
    exact (mul_left_eq_self₀.mp h3.symm).resolve_right hab
  obtain ⟨c, hc0, hc⟩ := exists_hilbert90 hp hℓ he hK σ hσ lam hN
  refine ⟨c, hc0, ?_⟩
  ext a b
  have hab := congrFun (congrFun hX a) b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hab ⊢
  rw [map_mul, hab]
  calc σ c * (lam * X a b) = (lam * σ c) * X a b := by ring
    _ = c * X a b := by rw [hc]

end Descent

end CFSG.LieType.SeitzGeneration
