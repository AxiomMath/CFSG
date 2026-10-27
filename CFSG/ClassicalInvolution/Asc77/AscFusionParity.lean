module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

theorem exists_fixedPoint_of_involutive {X : Type*} [Finite X] (hX : Odd (Nat.card X))
    {φ : X → X} (hφ : Function.Involutive φ) : ∃ x, φ x = x := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ¬ 2 ∣ Fintype.card X := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hX)
  have hsq : (hφ.toPerm φ) ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two, Equiv.Perm.mul_apply, hφ x]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) h2 hsq
  exact ⟨a, ha⟩

variable {G : Type*} [Group G]

theorem exists_mem_coset_conj_eq_mul {J N : Subgroup G} {z t j₀ : G}
    (hNodd : Odd (Nat.card N)) (hNJ : N ≤ J)
    (hJN : ∀ j ∈ J, ∀ n ∈ N, j⁻¹ * n * j ∈ N)
    (hzN : ∀ n ∈ N, z⁻¹ * n * z ∈ N)
    (hz2 : z * z = 1) (ht2 : t * t = 1) (ht : t ∈ J) (htz : z * t = t * z) (hj₀ : j₀ ∈ J)
    (h : j₀⁻¹ * (z⁻¹ * j₀ * z) * t⁻¹ ∈ N) :
    ∃ j ∈ J, j₀⁻¹ * j ∈ N ∧ z⁻¹ * j * z = j * t := by
  have hNfin : Finite N := Nat.finite_of_card_ne_zero hNodd.pos.ne'
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [hzi, hti] at h
  rw [hzi] at hzN
  rw [hzi]
  have htn : ∀ n ∈ N, t * n * t ∈ N := fun n hn => by
    simpa [hti] using hJN t⁻¹ (J.inv_mem ht) n hn
  have key : ∀ n : G, (j₀⁻¹ * (z * j₀ * z) * t) * (t * (z * n * z) * t) =
      j₀⁻¹ * (z * (j₀ * n) * z * t) := by
    intro n
    have e1 : (j₀⁻¹ * (z * j₀ * z) * t) * (t * (z * n * z) * t) =
        j₀⁻¹ * (z * j₀ * (z * (t * t) * z) * n * z * t) := by group
    rw [e1, ht2, mul_one, hz2]
    group
  let ψ : N → N := fun n => ⟨(j₀⁻¹ * (z * j₀ * z) * t) * (t * (z * (n : G) * z) * t),
    N.mul_mem h (htn _ (hzN _ n.2))⟩
  have hψ : ∀ n : N, ((ψ n : N) : G) = j₀⁻¹ * (z * (j₀ * n) * z * t) := fun n => key n
  have hinv : Function.Involutive ψ := by
    intro n
    apply Subtype.ext
    have h1 : j₀ * ((ψ n : N) : G) = z * (j₀ * n) * z * t := by
      rw [hψ n]; group
    rw [hψ (ψ n), h1]
    have hztz : z * t * z = t := by rw [htz, mul_assoc, hz2, mul_one]
    calc j₀⁻¹ * (z * (z * (j₀ * n) * z * t) * z * t)
        = j₀⁻¹ * ((z * z) * (j₀ * n) * (z * t * z) * t) := by group
      _ = j₀⁻¹ * ((j₀ * n) * t * t) := by rw [hz2, one_mul, hztz]
      _ = n := by rw [mul_assoc (j₀ * n) t t, ht2, mul_one]; group
  obtain ⟨n, hn⟩ := exists_fixedPoint_of_involutive (X := N) hNodd hinv
  have hn' := congrArg (fun m : N => (m : G)) hn
  simp only [hψ n] at hn'
  refine ⟨j₀ * n, J.mul_mem hj₀ (hNJ n.2), by simp, ?_⟩
  have h2 : j₀ * (j₀⁻¹ * (z * (j₀ * n) * z * t)) = j₀ * n := by rw [hn']
  have h3 : z * (j₀ * n) * z * t = j₀ * n := by simpa using h2
  calc z * (j₀ * (n : G)) * z = (z * (j₀ * n) * z * t) * t := by
        rw [mul_assoc (z * (j₀ * (n : G)) * z) t t, ht2, mul_one]
    _ = j₀ * n * t := by rw [h3]

end CFSG.ClassicalInvolution.Asc77.AscFusion
