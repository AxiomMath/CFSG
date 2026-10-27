module

public import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU


theorem perm3_core1 (σ τ : Equiv.Perm (Fin 3)) :
    σ * σ = 1 → σ ≠ 1 → (∀ a, τ a ≠ a) → ∀ a, (σ * τ⁻¹ * σ * τ) a ≠ a := by
  revert σ τ
  decide

theorem perm3_core2 (τ : Equiv.Perm (Fin 3)) : (∀ a, τ a ≠ a) → τ ^ 3 = 1 := by
  revert τ
  decide

theorem perm3_core3 (σ : Equiv.Perm (Fin 3)) : σ * σ = 1 → ∃ a, σ a = a := by
  revert σ
  decide

theorem perm3_core4 (τ : Equiv.Perm (Fin 3)) : τ ^ 3 = 1 → τ ≠ 1 → ∀ a, τ a ≠ a := by
  revert τ
  decide

theorem perm3_core (σ τ : Equiv.Perm (Fin 3)) :
    (σ * σ = 1 → σ ≠ 1 → (∀ a, τ a ≠ a) → ∀ a, (σ * τ⁻¹ * σ * τ) a ≠ a) ∧
      ((∀ a, τ a ≠ a) → τ ^ 3 = 1) ∧ (σ * σ = 1 → ∃ a, σ a = a) ∧
      (τ ^ 3 = 1 → τ ≠ 1 → ∀ a, τ a ≠ a) :=
  ⟨perm3_core1 σ τ, perm3_core2 τ, perm3_core3 σ, perm3_core4 τ⟩

theorem perm3 {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 3)
    (σ τ : Equiv.Perm α) :
    (σ * σ = 1 → σ ≠ 1 → (∀ a, τ a ≠ a) → ∀ a, (σ * τ⁻¹ * σ * τ) a ≠ a) ∧
      ((∀ a, τ a ≠ a) → τ ^ 3 = 1) ∧ (σ * σ = 1 → ∃ a, σ a = a) ∧
      (τ ^ 3 = 1 → τ ≠ 1 → ∀ a, τ a ≠ a) := by
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq hα
  let φ : Equiv.Perm α ≃* Equiv.Perm (Fin 3) := Equiv.permCongrHom e
  have hφ : ∀ (p : Equiv.Perm α) (a : α), φ p (e a) = e (p a) := by
    intro p a
    simp [φ, Equiv.permCongrHom, Equiv.permCongr_apply]
  have key := perm3_core (φ σ) (φ τ)
  have h3'' : (∀ a, τ a ≠ a) → ∀ b, φ τ b ≠ b := by
    intro h3 b hb
    apply h3 (e.symm b)
    apply e.injective
    rw [← hφ, Equiv.apply_symm_apply, hb]
  refine ⟨fun h1 h2 h3 a => ?_, fun h3 => ?_, fun h1 => ?_, fun h1 h2 a => ?_⟩
  · have h1' : φ σ * φ σ = 1 := by rw [← map_mul, h1, map_one]
    have h2' : φ σ ≠ 1 := fun h => h2 (φ.injective (by rw [h, map_one]))
    have := key.1 h1' h2' (h3'' h3) (e a)
    have hmul : φ σ * (φ τ)⁻¹ * φ σ * φ τ = φ (σ * τ⁻¹ * σ * τ) := by
      simp [map_mul, map_inv]
    intro hcon
    apply this
    rw [hmul, hφ, hcon]
  · exact φ.injective (by rw [map_pow, key.2.1 (h3'' h3), map_one])
  · have h1' : φ σ * φ σ = 1 := by rw [← map_mul, h1, map_one]
    obtain ⟨b, hb⟩ := key.2.2.1 h1'
    refine ⟨e.symm b, e.injective ?_⟩
    rw [← hφ, Equiv.apply_symm_apply, hb]
  · have h1' : φ τ ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    have h2' : φ τ ≠ 1 := fun h => h2 (φ.injective (by rw [h, map_one]))
    have := key.2.2.2 h1' h2' (e a)
    intro hcon
    apply this
    rw [hφ, hcon]

section Act

variable {H : Type} [Group H] [Finite H] (A : Subgroup H) [A.Normal]

noncomputable def actPerm : H →* Equiv.Perm {a : A // a ≠ 1} :=
  (nonidentityAutomorphismAction A).comp MulAut.conjNormal

omit [Finite H] in
theorem actPerm_apply (h : H) (a : A) (ha : a ≠ 1) :
    ((actPerm A h ⟨a, ha⟩ : A) : H) = h * (a : H) * h⁻¹ := by
  simp [actPerm]

omit [A.Normal] in
theorem card_nonidentity (hcard : Nat.card A = 4) : Nat.card {a : A // a ≠ 1} = 3 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : A => x = 1)]
  simp [← Nat.card_eq_fintype_card, hcard]

theorem exists_fixed_nonidentity (hcard : Nat.card A = 4) (x : H) (hx : x * x = 1) :
    ∃ a ∈ A, a ≠ 1 ∧ x * a * x⁻¹ = a := by
  classical
  let : Fintype {a : A // a ≠ 1} := Fintype.ofFinite _
  have h3 : Fintype.card {a : A // a ≠ 1} = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact card_nonidentity A hcard
  have := (perm3 h3 (actPerm A x) 1).2.2.1 (by rw [← map_mul, hx, map_one])
  obtain ⟨⟨a, ha⟩, hfix⟩ := this
  refine ⟨(a : H), a.2, fun h => ha (Subtype.ext h), ?_⟩
  have h := actPerm_apply A x a ha
  rw [hfix] at h
  exact h.symm

theorem exists_fpf_element (hcen : Subgroup.center H = ⊥) (hcard : Nat.card A = 4) :
    ∃ g : H, ∀ a ∈ A, a ≠ 1 → g * a * g⁻¹ ≠ a := by
  classical
  let : Fintype {a : A // a ≠ 1} := Fintype.ofFinite _
  have h3 : Fintype.card {a : A // a ≠ 1} = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact card_nonidentity A hcard
  by_contra hcon
  push Not at hcon
  have hfix : ∀ p ∈ (actPerm A).range, ∃ b, p b = b := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, haA, ha1, hga⟩ := hcon g
    have hne : (⟨a, haA⟩ : A) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    refine ⟨⟨⟨a, haA⟩, hne⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [actPerm_apply A g ⟨a, haA⟩ hne]
    exact hga
  have hP3 : ¬ 3 ∣ Nat.card (actPerm A).range := by
    intro hd
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨p, hp⟩ := exists_prime_orderOf_dvd_card' (G := (actPerm A).range) 3 hd
    have hp' : orderOf (p : Equiv.Perm {a : A // a ≠ 1}) = 3 := by
      rw [Subgroup.orderOf_coe]; exact hp
    obtain ⟨b, hb⟩ := hfix p p.2
    have h31 : (p : Equiv.Perm {a : A // a ≠ 1}) ^ 3 = 1 := by
      rw [← hp']; exact pow_orderOf_eq_one _
    have hne1 : (p : Equiv.Perm {a : A // a ≠ 1}) ≠ 1 := by
      intro h; rw [h, orderOf_one] at hp'; omega
    exact (perm3 h3 1 p).2.2.2 h31 hne1 b hb
  have hcardPerm : Nat.card (Equiv.Perm {a : A // a ≠ 1}) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h3]; rfl
  have hPdvd : Nat.card (actPerm A).range ∣ 2 * 3 := by
    have := Subgroup.card_subgroup_dvd_card (actPerm A).range
    rwa [hcardPerm] at this
  have hP2c : Nat.card (actPerm A).range ∣ 2 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3).symm) hPdvd
  have hP2 : IsPGroup 2 (actPerm A).range := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hP2c with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [h1]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [h1]; simp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hP2
    {a : A // a ≠ 1} (by rw [← Nat.card_eq_fintype_card] at h3; rw [h3]; omega)
  have hcentral : ((b : A) : H) ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : actPerm A g b = b := hb ⟨actPerm A g, g, rfl⟩
    have h2 : ((actPerm A g b : {a : A // a ≠ 1}) : A) = _ := rfl
    have h2' : g * ((b : A) : H) * g⁻¹ = ((b : A) : H) := by
      have h5 : (((actPerm A g b : {a : A // a ≠ 1}) : A) : H) = g * ((b : A) : H) * g⁻¹ :=
        actPerm_apply A g b.1 b.2
      rw [h1] at h5
      exact h5.symm
    calc g * ((b : A) : H) = (g * ((b : A) : H) * g⁻¹) * g := by group
      _ = ((b : A) : H) * g := by rw [h2']
  rw [hcen, Subgroup.mem_bot] at hcentral
  exact b.2 (Subtype.ext hcentral)

theorem rho_fpf (hcard : Nat.card A = 4) (x g : H) (hx : x * x = 1)
    (hxA : ∃ a ∈ A, x * a * x⁻¹ ≠ a) (hg : ∀ a ∈ A, a ≠ 1 → g * a * g⁻¹ ≠ a) :
    ∀ k : ℕ, ¬ 3 ∣ k → ∀ a ∈ A, a ≠ 1 →
      (x * (g⁻¹ * x * g)) ^ k * a * ((x * (g⁻¹ * x * g)) ^ k)⁻¹ ≠ a := by
  classical
  let : Fintype {a : A // a ≠ 1} := Fintype.ofFinite _
  have h3 : Fintype.card {a : A // a ≠ 1} = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact card_nonidentity A hcard
  set ρ : H := x * (g⁻¹ * x * g) with hρdef
  have hσ2 : actPerm A x * actPerm A x = 1 := by rw [← map_mul, hx, map_one]
  have hσ1 : actPerm A x ≠ 1 := by
    obtain ⟨a, haA, hxa⟩ := hxA
    have hne : (⟨a, haA⟩ : A) ≠ 1 := by
      intro h
      apply hxa
      have : a = 1 := congrArg Subtype.val h
      rw [this]; group
    intro h
    have h1 : actPerm A x ⟨⟨a, haA⟩, hne⟩ = ⟨⟨a, haA⟩, hne⟩ := by rw [h]; rfl
    apply hxa
    have h5 : (((actPerm A x ⟨⟨a, haA⟩, hne⟩ : {a : A // a ≠ 1}) : A) : H) = x * a * x⁻¹ :=
      actPerm_apply A x ⟨a, haA⟩ hne
    rw [h1] at h5
    exact h5.symm
  have hτ : ∀ b : {a : A // a ≠ 1}, actPerm A g b ≠ b := by
    rintro ⟨⟨a, haA⟩, hne⟩ h
    apply hg a haA (fun h' => hne (Subtype.ext h'))
    have h5 : (((actPerm A g ⟨⟨a, haA⟩, hne⟩ : {a : A // a ≠ 1}) : A) : H) = g * a * g⁻¹ :=
      actPerm_apply A g ⟨a, haA⟩ hne
    rw [h] at h5
    exact h5.symm
  have hρ : actPerm A ρ = actPerm A x * (actPerm A g)⁻¹ * actPerm A x * actPerm A g := by
    simp [hρdef, map_mul, map_inv, mul_assoc]
  have hρfpf : ∀ b, actPerm A ρ b ≠ b := by
    rw [hρ]; exact (perm3 h3 (actPerm A x) (actPerm A g)).1 hσ2 hσ1 hτ
  have hρ3 : (actPerm A ρ) ^ 3 = 1 := (perm3 h3 (actPerm A x) (actPerm A ρ)).2.1 hρfpf
  intro k hk a haA ha1
  have hne : (⟨a, haA⟩ : A) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hpow : (actPerm A ρ) ^ k = (actPerm A ρ) ^ (k % 3) := by
    conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hρ3, one_pow, mul_one]
  have hfpf : ∀ b, ((actPerm A ρ) ^ k) b ≠ b := by
    rw [hpow]
    rcases hk' with h | h
    · rw [h, pow_one]; exact hρfpf
    · rw [h]
      intro b hb
      have hinv : (actPerm A ρ) ^ 2 = (actPerm A ρ)⁻¹ := by
        have : (actPerm A ρ) ^ 2 * actPerm A ρ = 1 := by rw [← pow_succ, hρ3]
        exact mul_eq_one_iff_eq_inv.mp this
      rw [hinv] at hb
      apply hρfpf b
      have : (actPerm A ρ)⁻¹ b = b := hb
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq] at this
      exact this.symm
  intro hcon
  apply hfpf ⟨⟨a, haA⟩, hne⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [← map_pow]
  have h5 : (((actPerm A (ρ ^ k) ⟨⟨a, haA⟩, hne⟩ : {a : A // a ≠ 1}) : A) : H) =
      ρ ^ k * a * (ρ ^ k)⁻¹ := actPerm_apply A (ρ ^ k) ⟨a, haA⟩ hne
  rw [h5]
  exact hcon

end Act

end CFSG.GH74.Uniqueness.SU.K.R3
