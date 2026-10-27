module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseCentB

public section

namespace CFSG.GH74.QTGen4.Ku

variable {G : Type} [Group G]

namespace KuA6Model

variable [Finite G] {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
include Ψ

theorem no_central_mod_X (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) {u : G}
    (hux : u * x * u⁻¹ = x⁻¹)
    (hmod : ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∃ k : ℤ, u * c * u⁻¹ = x ^ k * c) :
    False := by
  apply Ψ.no_invert_centralize_delta hHN hxH hx hux
  intro e he
  have heE : e ∈ E := (Subgroup.mem_inf.mp he).1
  have heC : e ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp he).2
  by_cases he1 : e = 1
  · simp [he1]
  have hee : e * e = 1 := Ψ.E_mul_self e heE
  have hcomm : Commute x e := Subgroup.mem_centralizer_iff.mp heC x (Set.mem_singleton x)
  obtain ⟨k, hk⟩ := hmod e heC
  have hf : (u * e * u⁻¹) * (u * e * u⁻¹) = 1 := by
    have h : (u * e * u⁻¹) * (u * e * u⁻¹) = u * (e * e) * u⁻¹ := by group
    rw [h, hee]
    group
  rw [hk] at hf
  have hck : Commute (x ^ k) e := hcomm.zpow_left k
  have key : x ^ k * e * (x ^ k * e) = x ^ k * x ^ k * (e * e) := by
    calc x ^ k * e * (x ^ k * e) = x ^ k * (e * (x ^ k * e)) := by rw [mul_assoc]
      _ = x ^ k * ((e * x ^ k) * e) := by rw [mul_assoc e]
      _ = x ^ k * ((x ^ k * e) * e) := by rw [← hck.eq]
      _ = x ^ k * x ^ k * (e * e) := by simp only [mul_assoc]
  have hsq : x ^ k * x ^ k = 1 := by
    have h1 := hf
    rw [key, hee, mul_one] at h1
    exact h1
  have h2k : x ^ (k + k) = 1 := by
    rw [zpow_add]
    exact hsq
  have hdvd : (orderOf x : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.mpr h2k
  rw [hx] at hdvd
  norm_num at hdvd
  have h3k : (3 : ℤ) ∣ k := by omega
  have hxk1 : x ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; exact_mod_cast h3k)
  rw [hk, hxk1, one_mul]

end KuA6Model

end CFSG.GH74.QTGen4.Ku
