module

public import CFSG.GroupTheory.SteinbergCBHHBTheoremB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

section Quadratic

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem quadratic_pow_prime_eq_one {g : LinearMap.GeneralLinearGroup F V}
    (hg : ((g : V →ₗ[F] V) - 1) ^ 2 = 0) : g ^ p = 1 := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : ((g : V →ₗ[F] V) - 1) ^ p = 0 := pow_eq_zero_of_le h2 hg
  have h3 : ((g : V →ₗ[F] V) - 1) ^ (p ^ 1) = (g : V →ₗ[F] V) ^ (p ^ 1) - 1 :=
    CFSG.GroupTheory.HallHigmanB.sub_one_pow_char_pow (p := p) (g : V →ₗ[F] V) 1
  rw [pow_one] at h3
  rw [h1] at h3
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact (sub_eq_zero.1 h3.symm)

end Quadratic

section Main

variable {F : Type*} [Field F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime] [CharP F p]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem quadratic_centralizes_of_odd_or_abelian (hp2 : p ≠ 2) (hrp : r ≠ p)
    {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ) {g : Γ} (hg : ((ρ g : V →ₗ[F] V) - 1) ^ 2 = 0)
    {Q : Subgroup Γ} (hQ : IsPGroup r Q) (hQ2 : r ≠ 2 ∨ ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hgQ : g ∈ normalizer (Q : Set Γ)) : ∀ a ∈ Q, g * a = a * g := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haQ, hga⟩ := hcon
  set Q' : Subgroup (Module.End F V)ˣ := Q.map ρ with hQ'
  have hfin : Finite Q' := by
    have h1 : ((Q.map ρ : Subgroup _) : Set (Module.End F V)ˣ).Finite := by
      rw [Subgroup.coe_map]
      exact (Set.toFinite _).image _
    exact h1.to_subtype
  have hQ'r : IsPGroup r Q' := hQ.map ρ
  have hxQ : ρ g ∈ normalizer (Q' : Set (Module.End F V)ˣ) :=
    le_normalizer_map ρ (mem_map_of_mem ρ hgQ)
  have hxp : (ρ g) ^ (p ^ 1) = 1 := by
    rw [pow_one]
    exact quadratic_pow_prime_eq_one hg
  have hz : ∃ b ∈ Q', (ρ g) ^ (p ^ (1 - 1)) * b ≠ b * (ρ g) ^ (p ^ (1 - 1)) := by
    refine ⟨ρ a, mem_map_of_mem ρ haQ, fun h => hga (hρ ?_)⟩
    rw [map_mul, map_mul]
    simpa using h
  have hcore := CFSG.GroupTheory.HallHigmanB.hh_core_field (F := F) (V := V) (p := p) (q := r)
    hrp Q' hQ'r (ρ g) (n := 1) le_rfl hxQ hxp hz
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  rcases hcore with h | ⟨m, k, hm1, hm2, hk, hkr, hnab, -⟩
  · apply h
    have hle : 2 ≤ p ^ 1 - 1 := by
      rw [pow_one]
      omega
    exact pow_eq_zero_of_le hle hg
  · have hm : m = 1 := by omega
    subst hm
    rw [pow_one] at hkr
    rcases hQ2 with hr2 | hab
    · have hodd : p % 2 = 1 := by
        rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
        · exact absurd h hp2
        · exact h
      have h2p : 2 ∣ r ^ k := by
        rw [← hkr]
        exact Nat.dvd_of_mod_eq_zero (by omega)
      have h2r : 2 ∣ r := Nat.prime_two.dvd_of_dvd_pow h2p
      exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : r.Prime)).1 h2r).symm
    · obtain ⟨a', ha', b', hb', hne⟩ := hnab
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha'
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb'
      apply hne
      rw [← map_mul, ← map_mul, hab a₀ ha₀ b₀ hb₀]

theorem quadratic_centralizes_odd (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hrp : r ≠ p)
    {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ) {g : Γ} (hg : ((ρ g : V →ₗ[F] V) - 1) ^ 2 = 0)
    {Q : Subgroup Γ} (hQ : IsPGroup r Q) (hgQ : g ∈ normalizer (Q : Set Γ)) :
    ∀ a ∈ Q, g * a = a * g :=
  quadratic_centralizes_of_odd_or_abelian hp2 hrp ρ hρ hg hQ (Or.inl hr2) hgQ

theorem quadratic_centralizes_abelian (hp2 : p ≠ 2) (hrp : r ≠ p)
    {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ) {g : Γ} (hg : ((ρ g : V →ₗ[F] V) - 1) ^ 2 = 0)
    {Q : Subgroup Γ} (hQ : IsPGroup r Q) (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hgQ : g ∈ normalizer (Q : Set Γ)) : ∀ a ∈ Q, g * a = a * g :=
  quadratic_centralizes_of_odd_or_abelian hp2 hrp ρ hρ hg hQ (Or.inr hab) hgQ

theorem quadratic_le_centralizer_odd (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hrp : r ≠ p)
    {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ) {g : Γ} (hg : ((ρ g : V →ₗ[F] V) - 1) ^ 2 = 0)
    {Q : Subgroup Γ} (hQ : IsPGroup r Q) (hgQ : g ∈ normalizer (Q : Set Γ)) :
    Q ≤ centralizer ({g} : Set Γ) := fun a ha =>
  mem_centralizer_singleton_iff.2 (quadratic_centralizes_odd hp2 hr2 hrp ρ hρ hg hQ hgQ a ha).symm

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
