module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

theorem inv_of_fixedPointFree {Γ : Type} [Group Γ] (P : Subgroup Γ) [Finite P] (u : Γ)
    (hu2 : u * u = 1) (hPu : ∀ p ∈ P, u * p * u⁻¹ ∈ P)
    (hfpf : ∀ p ∈ P, p * u = u * p → p = 1) : ∀ p ∈ P, u * p * u⁻¹ = p⁻¹ := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let f : ↥P → ↥P := fun p =>
    ⟨(p : Γ)⁻¹ * (u * p * u⁻¹), P.mul_mem (P.inv_mem p.2) (hPu p p.2)⟩
  have hf_inj : Function.Injective f := by
    intro p p' h
    have E : (p : Γ)⁻¹ * (u * p * u⁻¹) = (p' : Γ)⁻¹ * (u * p' * u⁻¹) :=
      Subtype.ext_iff.mp h
    have h1 : (p' : Γ) * (p : Γ)⁻¹ * u = u * ((p' : Γ) * (p : Γ)⁻¹) := by
      have := congrArg (fun z => (p' : Γ) * z * u * (p : Γ)⁻¹) E
      simpa [mul_assoc, hu2] using this
    have hd : (p' : Γ) * (p : Γ)⁻¹ = 1 :=
      hfpf _ (P.mul_mem p'.2 (P.inv_mem p.2)) h1
    exact Subtype.ext (mul_inv_eq_one.mp hd).symm
  have key : ∀ x : Γ, u * (x⁻¹ * (u * x * u⁻¹)) * u⁻¹ = (x⁻¹ * (u * x * u⁻¹))⁻¹ := by
    intro x
    simp [hu, mul_assoc, hu2]
  intro p hp
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hf_inj ⟨p, hp⟩
  have hp_eq : p = (r : Γ)⁻¹ * (u * r * u⁻¹) := (Subtype.ext_iff.mp hr).symm
  rw [hp_eq]
  exact key r

theorem comm_of_fixedPointFree {Γ : Type} [Group Γ] (P : Subgroup Γ) [Finite P] (u : Γ)
    (hu2 : u * u = 1) (hPu : ∀ p ∈ P, u * p * u⁻¹ ∈ P)
    (hfpf : ∀ p ∈ P, p * u = u * p → p = 1) : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
  have hinv := inv_of_fixedPointFree P u hu2 hPu hfpf
  intro p hp q hq
  have hp' := hinv p hp
  have hq' := hinv q hq
  have hpq := hinv (p * q) (P.mul_mem hp hq)
  have h1 : u * (p * q) * u⁻¹ = p⁻¹ * q⁻¹ := by
    calc u * (p * q) * u⁻¹ = (u * p * u⁻¹) * (u * q * u⁻¹) := by group
      _ = p⁻¹ * q⁻¹ := by rw [hp', hq']
  have h2 : (p * q)⁻¹ = p⁻¹ * q⁻¹ := by rw [← hpq, h1]
  rw [mul_inv_rev] at h2
  have h3 := congrArg Inv.inv h2
  simpa [mul_inv_rev, inv_inv] using h3

theorem exists_torsion_subgroup {Γ : Type} [Group Γ] (H P : Subgroup Γ) [Finite P]
    (hPn : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (q : ℕ) [Fact q.Prime] (hq : q ∣ Nat.card P) :
    ∃ Q : Subgroup Γ, Q ≤ P ∧ (∀ h ∈ H, ∀ g ∈ Q, h * g * h⁻¹ ∈ Q) ∧ Q ≠ ⊥ ∧
      ∀ g ∈ Q, g ^ q = 1 := by
  let Q : Subgroup Γ :=
    { carrier := {g | g ∈ P ∧ g ^ q = 1}
      mul_mem' := by
        intro a b ha hb
        refine ⟨P.mul_mem ha.1 hb.1, ?_⟩
        rw [Commute.mul_pow (hcomm a ha.1 b hb.1), ha.2, hb.2, one_mul]
      one_mem' := ⟨P.one_mem, one_pow q⟩
      inv_mem' := by
        intro a ha
        refine ⟨P.inv_mem ha.1, ?_⟩
        rw [inv_pow, ha.2, inv_one] }
  have hQP : Q ≤ P := fun g hg => hg.1
  have hQnorm : ∀ h ∈ H, ∀ g ∈ Q, h * g * h⁻¹ ∈ Q := by
    intro h hh g hg
    refine ⟨hPn h hh g hg.1, ?_⟩
    rw [conj_pow, hg.2, mul_one, mul_inv_cancel]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hq
  have hxq : (x : Γ) ^ q = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa [Subgroup.coe_pow] using congrArg (Subtype.val) h
  have hxQ : (x : Γ) ∈ Q := ⟨x.2, hxq⟩
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : orderOf x = 1 := by rw [h, orderOf_one]
    rw [hx] at h1
    exact (Fact.out : q.Prime).ne_one h1
  have hx1' : (x : Γ) ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext (by simpa using h))
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot] at hxQ
    exact hx1' (Subgroup.mem_bot.mp hxQ)
  exact ⟨Q, hQP, hQnorm, hQne, fun g hg => hg.2⟩

theorem card_eq_prime_of_torsion {Γ : Type} [Group Γ] (Q : Subgroup Γ) [Finite Q] (q n : ℕ)
    [Fact q.Prime] (hQ1 : Q ≠ ⊥) (hexp : ∀ g ∈ Q, g ^ q = 1) (hdvd : Nat.card Q ∣ n)
    (hn : ¬ q ^ 2 ∣ n) : Nat.card Q = q := by
  have hPG : IsPGroup q ↥Q := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa [Subgroup.coe_pow] using hexp (g : Γ) g.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPG
  have hk1 : k = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      have h1 : Nat.card Q = 1 := by rw [hk, hk0, pow_zero]
      exact hQ1 (Subgroup.card_eq_one.mp h1)
    · by_contra hkne
      have hk2 : 2 ≤ k := by omega
      have hdvd2 : q ^ 2 ∣ q ^ k := pow_dvd_pow q hk2
      have hdvd3 : q ^ 2 ∣ Nat.card Q := by rw [hk]; exact hdvd2
      exact hn (dvd_trans hdvd3 hdvd)
  rw [hk, hk1, pow_one]

theorem eq_zpowers_of_card_eq_prime {Γ : Type} [Group Γ] (Q : Subgroup Γ) (q : ℕ)
    [Fact q.Prime] (hQ : Nat.card Q = q) {ζ : Γ} (hζ : ζ ∈ Q) (hζ1 : ζ ≠ 1) :
    Q = Subgroup.zpowers ζ := by
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact (Fact.out : q.Prime).ne_zero)
  let Z : Subgroup Γ := Subgroup.zpowers ζ
  have hZle : Z ≤ Q := Subgroup.zpowers_le.mpr hζ
  have hZdvd : Nat.card Z ∣ q := hQ ▸ Subgroup.card_dvd_of_le hZle
  have hZcard : Nat.card Z = q := by
    rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hZdvd with h1 | h2
    · exfalso
      have hZbot : Z = ⊥ := Subgroup.card_eq_one.mp h1
      have hmem : ζ ∈ Z := Subgroup.mem_zpowers ζ
      rw [hZbot] at hmem
      exact hζ1 (Subgroup.mem_bot.mp hmem)
    · exact h2
  have hZQ : Z = Q := Subgroup.eq_of_le_of_card_ge hZle (by rw [hQ, hZcard])
  simpa [Z] using hZQ.symm

theorem card_mulAut_lt_of_card_prime {Γ : Type} [Group Γ] (Q : Subgroup Γ) (q : ℕ)
    [Fact q.Prime] (hQ : Nat.card Q = q) (hq : q ≤ 17) : Nat.card (MulAut ↥Q) < 360 := by
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact (Fact.out : q.Prime).ne_zero)
  haveI : IsCyclic ↥Q := isCyclic_of_prime_card hQ
  rw [IsCyclic.card_mulAut, hQ, Nat.totient_prime (Fact.out : q.Prime)]
  have : 2 ≤ q := (Fact.out : q.Prime).two_le
  omega

end C10

end CFSG.OddStandard.SmallF3.Omega
