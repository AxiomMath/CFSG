module

public import CFSG.GH74.GLS.Stage4.T2OddAut
public import CFSG.CharacterTheory.Wreathed.AutomorphismTwoGroup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem sdw3_aux_oddAut {X : Type} [Group X] (S : Subgroup X)
    (hshape : (∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup m)) ∨
      (∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.WreathedTwoGroup m)))
    (θ : MulAut ↥S) (hθ : Odd (orderOf θ)) : θ = 1 := by
  rcases hshape with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact t2C_oddAut_semidihedral ⟨hm, ⟨e⟩⟩ θ hθ
  · refine t2OA_congr e (fun θ' hθ' => ?_) θ hθ
    obtain ⟨k, hk⟩ := CFSG.Wreathed.wreathedTwoGroup_automorphism_isPGroup m hm θ'
    have hdvd : orderOf θ' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj : j = 0 := by
      by_contra hj0
      have h2 : 2 ∣ orderOf θ' := by
        rw [hj']
        exact dvd_pow_self 2 hj0
      exact (Nat.not_even_iff_odd.mpr hθ') (even_iff_two_dvd.mpr h2)
    rw [hj, pow_zero] at hj'
    exact orderOf_eq_one_iff.1 hj'

theorem sdw_three_le {X : Type} [Group X] [Finite X] {E : Subgroup X} [E.Normal]
    (hE : ∀ S : Sylow 2 X, (S : Subgroup X) ≤ E)
    {K Q : Subgroup X} {w : X} (hwK : w ∈ K) (hQ2 : IsPGroup 2 Q) (hw3 : w ^ 3 = 1)
    (hwQ : w ∉ Q) (hact : ∃ k ∈ Q, w * k * w⁻¹ ≠ k)
    (hcos : ∀ g ∈ K, g ∈ Q ∨ (∃ q ∈ Q, g = q * w) ∨ (∃ q ∈ Q, g = q * w ^ 2))
    (S : Sylow 2 X) (hQS : Q ≤ (S : Subgroup X))
    (hshape : (∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.SemidihedralGroup m)) ∨
      (∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.WreathedTwoGroup m)))
    (hSK : ∀ s ∈ (S : Subgroup X), ∀ k ∈ K, s * k * s⁻¹ ∈ K) : K ≤ E := by
  have hSE : (S : Subgroup X) ≤ E := hE S
  have hw3' : w * w * w = 1 := by
    have : w ^ 3 = w * w * w := by
      rw [pow_three]; exact (mul_assoc w w w).symm
    rw [← this]; exact hw3
  have hA : ∃ s ∈ (S : Subgroup X), ∀ q ∈ Q, s * w * s⁻¹ ≠ q * w := by
    by_contra hcon
    push Not at hcon
    have hconj : ∀ s ∈ (S : Subgroup X), w * s * w⁻¹ ∈ (S : Subgroup X) := by
      intro s hs
      obtain ⟨q', hq', hq'eq⟩ := hcon s⁻¹ ((S : Subgroup X).inv_mem hs)
      have h0 : w * s = s * (q' * w) := by
        have h1 := congrArg (fun y => s * y) hq'eq
        simp only [inv_inv] at h1
        calc w * s = s * (s⁻¹ * w * s) := by group
          _ = s * (q' * w) := h1
      have h1 : w * s * w⁻¹ = s * q' := by
        calc w * s * w⁻¹ = s * (q' * w) * w⁻¹ := by rw [h0]
          _ = s * q' := by group
      rw [h1]
      exact (S : Subgroup X).mul_mem hs (hQS hq')
    let f : ↥(S : Subgroup X) →* ↥(S : Subgroup X) :=
      { toFun := fun s => ⟨w * s * w⁻¹, hconj s s.2⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp [mul_assoc] }
    have hfinj : Function.Injective f := by
      intro a b hab
      have := congrArg (fun y : ↥(S : Subgroup X) => (y : X)) hab
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this
    let θ : MulAut ↥(S : Subgroup X) := MulEquiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
    have hθapp : ∀ s : ↥(S : Subgroup X), ((θ s : ↥(S : Subgroup X)) : X) = w * s * w⁻¹ := fun s => rfl
    have hθ3 : θ ^ 3 = 1 := by
      ext s
      have h3 : ((θ ^ 3) s : X) = w * (w * (w * s * w⁻¹) * w⁻¹) * w⁻¹ := by
        simp [pow_succ, MulAut.mul_apply, hθapp]
      rw [h3]
      calc w * (w * (w * (s : X) * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * s * (w * w * w)⁻¹ := by group
        _ = s := by rw [hw3']; simp
    have hodd : Odd (orderOf θ) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hθ3)
    have hθ1 : θ = 1 := sdw3_aux_oddAut (S : Subgroup X) hshape θ hodd
    obtain ⟨k, hk, hkne⟩ := hact
    apply hkne
    have := congrArg (fun φ : MulAut ↥(S : Subgroup X) => ((φ ⟨k, hQS hk⟩ : ↥(S : Subgroup X)) : X)) hθ1
    simpa [hθapp] using this
  obtain ⟨s, hs, hsne⟩ := hA
  have hg : s * w * s⁻¹ ∈ K := hSK s hs w hwK
  have hsE : s ∈ E := hSE hs
  have hwE : w ∈ E := by
    rcases hcos _ hg with hgQ | ⟨q, hq, hqeq⟩ | ⟨q, hq, hqeq⟩
    · exfalso
      have h3 : (s * w * s⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hw3]; simp
      obtain ⟨k, hk⟩ := hQ2 ⟨_, hgQ⟩
      have hk' : (s * w * s⁻¹) ^ (2 ^ k) = 1 := by
        have := congrArg (fun y : ↥Q => (y : X)) hk
        simpa using this
      have hord : orderOf (s * w * s⁻¹) ∣ Nat.gcd 3 (2 ^ k) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
      have hcop : Nat.gcd 3 (2 ^ k) = 1 := by
        apply Nat.Coprime.pow_right
        decide
      rw [hcop] at hord
      have h1 : s * w * s⁻¹ = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
      apply hwQ
      have : w = 1 := by
        calc w = s⁻¹ * (s * w * s⁻¹) * s := by group
          _ = 1 := by rw [h1]; simp
      rw [this]
      exact Q.one_mem
    · exact absurd hqeq (hsne q hq)
    · have h1 : (s * w * s⁻¹) * w⁻¹ = q * w := by
        rw [hqeq]; group
      have h2 : (s * w * s⁻¹) * w⁻¹ ∈ E := by
        have h3 : w * s⁻¹ * w⁻¹ ∈ E := Subgroup.Normal.conj_mem inferInstance _ (E.inv_mem hsE) w
        have : (s * w * s⁻¹) * w⁻¹ = s * (w * s⁻¹ * w⁻¹) := by group
        rw [this]
        exact E.mul_mem hsE h3
      rw [h1] at h2
      have hqE : q ∈ E := hSE (hQS hq)
      have : w = q⁻¹ * (q * w) := by group
      rw [this]
      exact E.mul_mem (E.inv_mem hqE) h2
  intro k hk
  rcases hcos k hk with hkQ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact hSE (hQS hkQ)
  · exact E.mul_mem (hSE (hQS hq)) hwE
  · exact E.mul_mem (hSE (hQS hq)) (E.pow_mem hwE 2)

end CFSG.GH74.GLS.Stage4.Rest
