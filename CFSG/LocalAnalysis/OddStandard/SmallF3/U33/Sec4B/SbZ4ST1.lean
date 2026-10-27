module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem z4_mem_closure_of_comm_rho_cent_V (hp : Z4Pre t L S x₁ x₂ lam rho tau) {a : G}
    (haM : a ∈ ctxM t tau x₁ x₂) (haρ : a * rho = rho * a)
    (hay : a * x₁ ^ 2 * a⁻¹ = x₁ ^ 2) :
    a ∈ closure ({t, tau} : Set G) := by
  have hay' : a * x₁ ^ 2 = x₁ ^ 2 * a := by
    calc a * x₁ ^ 2 = a * x₁ ^ 2 * a⁻¹ * a := by group
      _ = x₁ ^ 2 * a := by rw [hay]
  have haρinv : a * rho⁻¹ = rho⁻¹ * a := by
    have hc : Commute a rho := haρ
    exact hc.inv_right
  have hcy : a * (rho * x₁ ^ 2 * rho⁻¹) = (rho * x₁ ^ 2 * rho⁻¹) * a := by
    calc a * (rho * x₁ ^ 2 * rho⁻¹) = (a * rho) * x₁ ^ 2 * rho⁻¹ := by group
      _ = (rho * a) * x₁ ^ 2 * rho⁻¹ := by rw [haρ]
      _ = rho * (a * x₁ ^ 2) * rho⁻¹ := by group
      _ = rho * (x₁ ^ 2 * a) * rho⁻¹ := by rw [hay']
      _ = rho * (x₁ ^ 2 * (a * rho⁻¹)) := by group
      _ = rho * (x₁ ^ 2 * (rho⁻¹ * a)) := by rw [haρinv]
      _ = (rho * x₁ ^ 2 * rho⁻¹) * a := by group
  have hcy' : a * (rho⁻¹ * x₁ ^ 2 * rho) = (rho⁻¹ * x₁ ^ 2 * rho) * a := by
    calc a * (rho⁻¹ * x₁ ^ 2 * rho) = (a * rho⁻¹) * x₁ ^ 2 * rho := by group
      _ = (rho⁻¹ * a) * x₁ ^ 2 * rho := by rw [haρinv]
      _ = rho⁻¹ * (a * x₁ ^ 2) * rho := by group
      _ = rho⁻¹ * (x₁ ^ 2 * a) * rho := by rw [hay']
      _ = rho⁻¹ * (x₁ ^ 2 * (a * rho)) := by group
      _ = rho⁻¹ * (x₁ ^ 2 * (rho * a)) := by rw [haρ]
      _ = (rho⁻¹ * x₁ ^ 2 * rho) * a := by group
  have hz : (x₁ * x₂) ^ 2 = rho * x₁ ^ 2 * rho⁻¹ ∨ (x₁ * x₂) ^ 2 = rho⁻¹ * x₁ ^ 2 * rho := by
    rcases hp.rho_V with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · right; rw [← h3]; group
    · left; rw [h1]
  have hw : x₂ ^ 2 = rho * x₁ ^ 2 * rho⁻¹ ∨ x₂ ^ 2 = rho⁻¹ * x₁ ^ 2 * rho := by
    rcases hp.rho_V with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left; rw [h1]
    · right; rw [← h3]; group
  have hcom : ∀ v ∈ fourGrp x₁ x₂, a * v = v * a := by
    intro v hv
    rw [hp.mem_V_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · group
    · exact hay'
    · rcases hz with h | h <;> rw [h] <;> [exact hcy; exact hcy']
    · rcases hw with h | h <;> rw [h] <;> [exact hcy; exact hcy']
  have hcent : a ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun v hv => (hcom v hv).symm
  have hCO : a ∈ ctxCO t tau x₁ x₂ rho := by
    refine ⟨?_, ?_⟩
    · rw [hp.O_eq_CV]; exact ⟨haM, hcent⟩
    · exact mem_centralizer_singleton_iff.mpr haρ
  rwa [hp.CO_rho] at hCO

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem cent_rho_decomp {n : G} (hnM : n ∈ ctxM t tau x₁ x₂) (hnρ : n * rho = rho * n) :
    ∃ e : G, (e = 1 ∨ e = rho ∨ e = rho⁻¹) ∧ ∃ n' ∈ closure ({t, tau} : Set G), n = e * n' := by
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := hp.y_mem_V
  have hconj : n * x₁ ^ 2 * n⁻¹ ∈ fourGrp x₁ x₂ := hp.normal_V.2 n hnM _ hyV
  have hne : n * x₁ ^ 2 * n⁻¹ ≠ 1 := by
    intro h
    apply hp.y_ne_one
    calc x₁ ^ 2 = n⁻¹ * (n * x₁ ^ 2 * n⁻¹) * n := by group
      _ = n⁻¹ * 1 * n := by rw [h]
      _ = 1 := by group
  have hcases : n * x₁ ^ 2 * n⁻¹ = x₁ ^ 2 ∨
      n * x₁ ^ 2 * n⁻¹ = rho * x₁ ^ 2 * rho⁻¹ ∨
      n * x₁ ^ 2 * n⁻¹ = rho⁻¹ * x₁ ^ 2 * rho := by
    have hmem := (hp.mem_V_iff (n * x₁ ^ 2 * n⁻¹)).mp hconj
    rcases hmem with h | h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · rcases hp.rho_V with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inr (by
          rw [h, show (x₁ * x₂) ^ 2 = rho⁻¹ * x₁ ^ 2 * rho from by rw [← h3]; group]))
      · exact Or.inr (Or.inl (by rw [h, h1]))
    · rcases hp.rho_V with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl (by rw [h, h1]))
      · exact Or.inr (Or.inr (by
          rw [h, show x₂ ^ 2 = rho⁻¹ * x₁ ^ 2 * rho from by rw [← h3]; group]))
  rcases hcases with h | h | h
  · refine ⟨1, Or.inl rfl, n, ?_, by group⟩
    exact z4_mem_closure_of_comm_rho_cent_V hp hnM hnρ (by rw [h])
  · refine ⟨rho, Or.inr (Or.inl rfl), rho⁻¹ * n, ?_, by group⟩
    exact z4_mem_closure_of_comm_rho_cent_V hp (mul_mem (inv_mem hp.rho_mem_M) hnM)
      (by
        calc (rho⁻¹ * n) * rho = rho⁻¹ * (n * rho) := by group
          _ = rho⁻¹ * (rho * n) := by rw [hnρ]
          _ = rho * (rho⁻¹ * n) := by group)
      (by
        calc (rho⁻¹ * n) * x₁ ^ 2 * (rho⁻¹ * n)⁻¹
            = rho⁻¹ * (n * x₁ ^ 2 * n⁻¹) * rho := by group
          _ = rho⁻¹ * (rho * x₁ ^ 2 * rho⁻¹) * rho := by rw [h]
          _ = x₁ ^ 2 := by group)
  · refine ⟨rho⁻¹, Or.inr (Or.inr rfl), rho * n, ?_, by group⟩
    exact z4_mem_closure_of_comm_rho_cent_V hp (mul_mem hp.rho_mem_M hnM)
      (by
        calc (rho * n) * rho = rho * (n * rho) := by group
          _ = rho * (rho * n) := by rw [hnρ]
          _ = rho * (rho * n) := rfl)
      (by
        calc (rho * n) * x₁ ^ 2 * (rho * n)⁻¹
            = rho * (n * x₁ ^ 2 * n⁻¹) * rho⁻¹ := by group
          _ = rho * (rho⁻¹ * x₁ ^ 2 * rho) * rho⁻¹ := by rw [h]
          _ = x₁ ^ 2 := by group)

theorem two_elt_cent_rho {n : G} (hnM : n ∈ ctxM t tau x₁ x₂) (hnρ : n * rho = rho * n) {k : ℕ}
    (hk : n ^ (2 ^ k) = 1) : n ∈ closure ({t, tau} : Set G) := by
  obtain ⟨e, he, n', hn', hn_eq⟩ := hp.cent_rho_decomp hnM hnρ
  have hle : closure ({t, tau} : Set G) ≤ centralizer ({rho} : Set G) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr hp.rho_comm_t.symm
    · exact mem_centralizer_singleton_iff.mpr hp.rho_comm_tau.symm
  have hnr : n' * rho = rho * n' := mem_centralizer_singleton_iff.mp (hle hn')
  have hn'2 : n' * n' = 1 := by
    have h4 := (S4B.mem_closure_pair_of_invol hp.t_mul_self hp.tau_mul_self hp.t_comm_tau).mp hn'
    rcases h4 with rfl | rfl | rfl | rfl
    · group
    · exact hp.t_mul_self
    · exact hp.tau_mul_self
    · calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
        _ = t * (t * tau) * tau := by rw [← hp.t_comm_tau]
        _ = (t * t) * (tau * tau) := by group
        _ = 1 := by rw [hp.t_mul_self, hp.tau_mul_self, one_mul]
  have hn'pow : n' ^ (2 ^ (k + 1)) = 1 := by
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, mul_comm]]
    rw [pow_mul, show n' ^ 2 = 1 by rw [pow_two]; exact hn'2, one_pow]
  have hnpow : n ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul, hk, one_pow]
  rcases he with he1 | he2 | he3
  · rw [he1, one_mul] at hn_eq
    rw [hn_eq]
    exact hn'
  · exfalso
    have hne' : n = rho * n' := by rw [hn_eq, he2]
    have hepow : rho ^ (2 ^ (k + 1)) = 1 := by
      have h := hnpow
      rw [hne', Commute.mul_pow (show Commute rho n' from hnr.symm) (2 ^ (k + 1)),
        hn'pow, mul_one] at h
      exact h
    have h3 : 3 ∣ 2 ^ (k + 1) := by
      rw [← hp.ord_rho]
      exact orderOf_dvd_iff_pow_eq_one.mpr hepow
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  · exfalso
    have hne' : n = rho⁻¹ * n' := by rw [hn_eq, he3]
    have hepow : (rho⁻¹) ^ (2 ^ (k + 1)) = 1 := by
      have h := hnpow
      rw [hne', Commute.mul_pow (Commute.inv_left (show Commute rho n' from hnr.symm))
        (2 ^ (k + 1)), hn'pow, mul_one] at h
      exact h
    have hrho : rho ^ (2 ^ (k + 1)) = 1 := by
      have h := hepow
      rw [inv_pow] at h
      exact inv_eq_one.mp h
    have h3 : 3 ∣ 2 ^ (k + 1) := by
      rw [← hp.ord_rho]
      exact orderOf_dvd_iff_pow_eq_one.mpr hrho
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32

end Z4Pre

end CFSG.OddStandard.SmallF3.HarrisU33
