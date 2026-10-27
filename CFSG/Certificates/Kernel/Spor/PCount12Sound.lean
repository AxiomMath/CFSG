module

public import Certificates.Data.Kernel.Spor.PCount12
public import CFSG.Certificates.Kernel.Spor.PCountSound

public section

namespace CFSG.KS.PCnt

open CFSG.KC.Enum CFSG.KS.PK CFSG.Sporadic.Schreier

theorem orderOf_eq_twelve_iff' {G : Type*} [Group G] (g : G) :
    orderOf g = 12 ↔ g ^ 12 = 1 ∧ g ^ 4 ≠ 1 ∧ g ^ 6 ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one g, fun h4 => ?_, fun h6 => ?_⟩
    · have := orderOf_dvd_of_pow_eq_one h4
      rw [h] at this
      omega
    · have := orderOf_dvd_of_pow_eq_one h6
      rw [h] at this
      omega
  · rintro ⟨h12, h4, h6⟩
    have hd := orderOf_dvd_of_pow_eq_one h12
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h4' : ¬ orderOf g ∣ 4 := fun d => h4 (orderOf_dvd_iff_pow_eq_one.1 d)
    have h6' : ¬ orderOf g ∣ 6 := fun d => h6 (orderOf_dvd_iff_pow_eq_one.1 d)
    interval_cases h : orderOf g <;> simp_all <;> omega

variable {n : Nat}

theorem ordTwelve_pk (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) :
    ordTwelve n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk σ) =
      if orderOf σ = 12 then 1 else 0 := by
  unfold ordTwelve
  rw [strictN_eq, pk_mul hn, strictN_eq, pk_mul hn, strictN_eq, pk_mul hn, pk_mul hn]
  have e2 : σ * σ = σ ^ 2 := (sq σ).symm
  have e4 : σ ^ 2 * σ ^ 2 = σ ^ 4 := by rw [← pow_add]
  have e6 : σ ^ 4 * σ ^ 2 = σ ^ 6 := by rw [← pow_add]
  have e12 : σ ^ 6 * σ ^ 6 = σ ^ 12 := by rw [← pow_add]
  rw [e2, e4, e6, e12]
  simp only [nIf_eq, beq_pk_iff hn]
  have e := orderOf_eq_twelve_iff' σ
  by_cases h12 : σ ^ 12 = 1 <;> by_cases h4 : σ ^ 4 = 1 <;> by_cases h6 : σ ^ 6 = 1 <;> simp_all

end CFSG.KS.PCnt

end
