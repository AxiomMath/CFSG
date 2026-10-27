module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenPair

public section

namespace CFSG.HardMathSupport.Dickson.I271.M13

open CFSG.HardMathSupport.Dickson.I271

variable {G : Type*} [Group G]

@[expose] def Act (d c n : G) (p q r s : ℕ) : Prop :=
  n * d * n⁻¹ = d ^ p * c ^ q ∧ n * c * n⁻¹ = d ^ r * c ^ s

structure PlaneData (d c : G) : Prop where
  comm : Commute d c
  hd : d ^ 13 = 1
  hc : c ^ 13 = 1
  ind : ∀ j k : ℕ, d ^ j * c ^ k = 1 → j % 13 = 0 ∧ k % 13 = 0

namespace PlaneData

theorem dpow_mod {d c : G} (P : PlaneData d c) (m : ℕ) : d ^ m = d ^ (m % 13) :=
  pow_eq_pow_mod m P.hd

theorem cpow_mod {d c : G} (P : PlaneData d c) (m : ℕ) : c ^ m = c ^ (m % 13) :=
  pow_eq_pow_mod m P.hc

theorem ev_mul {d c : G} (P : PlaneData d c) (a b a' b' : ℕ) :
    (d ^ a * c ^ b) * (d ^ a' * c ^ b') = d ^ (a + a') * c ^ (b + b') := by
  calc (d ^ a * c ^ b) * (d ^ a' * c ^ b') = d ^ a * (c ^ b * d ^ a') * c ^ b' := by
        simp only [mul_assoc]
    _ = d ^ a * (d ^ a' * c ^ b) * c ^ b' := by rw [(P.comm.pow_pow a' b).symm.eq]
    _ = d ^ (a + a') * c ^ (b + b') := by rw [pow_add, pow_add]; simp only [mul_assoc]

theorem ev_pow {d c : G} (P : PlaneData d c) (a b n : ℕ) :
    (d ^ a * c ^ b) ^ n = d ^ (a * n) * c ^ (b * n) := by
  rw [(P.comm.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul]

end PlaneData

theorem Act.conj_ev {d c n : G} (P : PlaneData d c) {p q r s : ℕ} (h : Act d c n p q r s)
    (j k : ℕ) : n * (d ^ j * c ^ k) * n⁻¹ = d ^ (p * j + r * k) * c ^ (q * j + s * k) := by
  obtain ⟨h1, h2⟩ := h
  have e : n * (d ^ j * c ^ k) * n⁻¹ = (n * d * n⁻¹) ^ j * (n * c * n⁻¹) ^ k := by
    rw [conj_pow, conj_pow]
    group
  rw [e, h1, h2, P.ev_pow, P.ev_pow, P.ev_mul]

theorem Act.mul {d c n n' : G} (P : PlaneData d c) {p q r s p' q' r' s' : ℕ}
    (h : Act d c n p q r s) (h' : Act d c n' p' q' r' s') :
    Act d c (n * n') (p * p' + r * q') (q * p' + s * q') (p * r' + r * s') (q * r' + s * s') := by
  have e : ∀ x : G, n * n' * x * (n * n')⁻¹ = n * (n' * x * n'⁻¹) * n⁻¹ := fun x => by group
  refine ⟨?_, ?_⟩
  · rw [e, h'.1, Act.conj_ev P h]
  · rw [e, h'.2, Act.conj_ev P h]

theorem Act.inv {d c n : G} (P : PlaneData d c) {p q r s p' q' r' s' : ℕ}
    (h : Act d c n p q r s) (h1 : (p * p' + r * q') % 13 = 1) (h2 : (q * p' + s * q') % 13 = 0)
    (h3 : (p * r' + r * s') % 13 = 0) (h4 : (q * r' + s * s') % 13 = 1) :
    Act d c n⁻¹ p' q' r' s' := by
  have e1 : n * (d ^ p' * c ^ q') * n⁻¹ = d := by
    rw [Act.conj_ev P h, P.dpow_mod, P.cpow_mod, h1, h2]; simp
  have e2 : n * (d ^ r' * c ^ s') * n⁻¹ = c := by
    rw [Act.conj_ev P h, P.dpow_mod (p * r' + r * s'), P.cpow_mod (q * r' + s * s'), h3, h4]; simp
  refine ⟨?_, ?_⟩
  · rw [inv_inv]
    calc n⁻¹ * d * n = n⁻¹ * (n * (d ^ p' * c ^ q') * n⁻¹) * n := by rw [e1]
      _ = d ^ p' * c ^ q' := by group
  · rw [inv_inv]
    calc n⁻¹ * c * n = n⁻¹ * (n * (d ^ r' * c ^ s') * n⁻¹) * n := by rw [e2]
      _ = d ^ r' * c ^ s' := by group

theorem Act.mem_centSet {d c n : G} (P : PlaneData d c) {A : Subgroup G} (hd : d ∈ A) (hc : c ∈ A)
    {p q r s : ℕ} (h : Act d c n p q r s) (j k : ℕ) (hj : (p * j + r * k) % 13 = j % 13)
    (hk : (q * j + s * k) % 13 = k % 13) (hne : ¬ (j % 13 = 0 ∧ k % 13 = 0)) :
    n ∈ centSet A := by
  refine ⟨d ^ j * c ^ k, A.mul_mem (A.pow_mem hd j) (A.pow_mem hc k), ?_, ?_⟩
  · intro h1
    exact hne (P.ind j k h1)
  · have := Act.conj_ev P h j k
    rw [P.dpow_mod (p * j + r * k), P.cpow_mod (q * j + s * k), hj, hk, ← P.dpow_mod,
      ← P.cpow_mod] at this
    exact mul_inv_eq_iff_eq_mul.1 this

theorem Act.inv_mul_mem_centSet {d c n z : G} (P : PlaneData d c) {A : Subgroup G} (hc : c ∈ A)
    (hc1 : c ≠ 1) {r s p' q' r' s' : ℕ} (h : n * c * n⁻¹ = d ^ r * c ^ s)
    (hz : Act d c z p' q' r' s') (hr : r % 13 = r' % 13) (hs : s % 13 = s' % 13) :
    z⁻¹ * n ∈ centSet A := by
  refine ⟨c, hc, hc1, ?_⟩
  have h2 := hz.2
  rw [P.dpow_mod r, P.cpow_mod s, hr, hs, ← P.dpow_mod, ← P.cpow_mod, ← h2] at h
  have h3 : n * c = z * c * z⁻¹ * n := mul_inv_eq_iff_eq_mul.1 h
  calc z⁻¹ * n * c = z⁻¹ * (n * c) := by rw [mul_assoc]
    _ = c * (z⁻¹ * n) := by rw [h3]; group

end CFSG.HardMathSupport.Dickson.I271.M13
