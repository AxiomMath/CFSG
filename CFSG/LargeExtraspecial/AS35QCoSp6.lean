
module

public import CFSG.LargeExtraspecial.AS35QCoSp6Base

public import Certificates.Certificate21205

public section

namespace CFSG.LargeExtraspecial.AS35QCo

open Native CFSG.Assembly.LowTwoRank CFSG.Sporadic.Co2Smith
open scoped Matrix

theorem exists_conj_rep (τ : Sp62) (h2 : τ * τ = 1) (h1 : τ ≠ 1) :
    ∃ k < 4, ∃ ρ : Sp62, Rep (repc k) ρ ∧ ∃ m : Sp62, τ = m * ρ * m⁻¹ :=
  Certificates.certificate21205.1 τ h2 h1

theorem exists_bigOrder_rep {k : ℕ} (hk : k = 2 ∨ k = 3) {ρ : Sp62} (hρ : Rep (repc k) ρ) :
    ∃ w : Sp62, ∀ j, 1 ≤ j → j ≤ 4 → (ρ * (w * ρ * w⁻¹)) ^ j ≠ 1 :=
  Certificates.certificate21205.2.1 k hk ρ hρ

theorem false_of_small_rep {k : ℕ} (hk : k = 0 ∨ k = 1) {ρ : Sp62} (hρ : Rep (repc k) ρ)
    {y : Sp62} (hy : y ∈ Subgroup.centralizer ({ρ} : Set Sp62)) (hy1 : y ≠ 1) (hyρ : y ≠ ρ)
    (hsmall : ((fun h : Sp62 => h * y * h⁻¹) ''
      (Subgroup.centralizer ({ρ} : Set Sp62) : Set Sp62)).ncard ≤ 6)
    {h₀ : Sp62} (hh₀ : h₀ ∈ Subgroup.centralizer ({ρ} : Set Sp62))
    (hconj : h₀ * y * h₀⁻¹ = ρ * y) : False :=
  Certificates.certificate21205.2.2 k hk ρ hρ y hy hy1 hyρ hsmall h₀ hh₀ hconj

theorem false_of_small_conj {τ : Sp62} (h2 : τ * τ = 1) (h1 : τ ≠ 1)
    (hprod : ∀ g : Sp62, orderOf (τ * (g * τ * g⁻¹)) ∈ ({1, 2, 3, 4} : Set ℕ))
    {y : Sp62} (hy : y ∈ Subgroup.centralizer ({τ} : Set Sp62)) (hy1 : y ≠ 1) (hyτ : y ≠ τ)
    (hsmall : ((fun h : Sp62 => h * y * h⁻¹) ''
      (Subgroup.centralizer ({τ} : Set Sp62) : Set Sp62)).ncard ≤ 6)
    {h₀ : Sp62} (hh₀ : h₀ ∈ Subgroup.centralizer ({τ} : Set Sp62))
    (hconj : h₀ * y * h₀⁻¹ = τ * y) : False := by
  obtain ⟨k, hk, ρ, hρ, m, rfl⟩ := exists_conj_rep τ h2 h1
  have hbig : k = 2 ∨ k = 3 → False := by
    intro hk23
    obtain ⟨w, hw⟩ := exists_bigOrder_rep hk23 hρ
    have e : m * ρ * m⁻¹ * ((m * w * m⁻¹) * (m * ρ * m⁻¹) * (m * w * m⁻¹)⁻¹) =
        m * (ρ * (w * ρ * w⁻¹)) * m⁻¹ := by group
    have ho := hprod (m * w * m⁻¹)
    rw [e, show m * (ρ * (w * ρ * w⁻¹)) * m⁻¹ = MulAut.conj m (ρ * (w * ρ * w⁻¹)) from rfl,
      MulEquiv.orderOf_eq] at ho
    have hpow := pow_orderOf_eq_one (ρ * (w * ρ * w⁻¹))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho | ho | ho <;> rw [ho] at hpow <;>
      exact hw _ (by norm_num) (by norm_num) hpow
  have hsmallk : k = 0 ∨ k = 1 → False := by
    intro hk01
    have hy' : m⁻¹ * y * m ∈ Subgroup.centralizer ({ρ} : Set Sp62) :=
      conj_mem_centralizer_iff.mp hy
    have hh₀' : m⁻¹ * h₀ * m ∈ Subgroup.centralizer ({ρ} : Set Sp62) :=
      conj_mem_centralizer_iff.mp hh₀
    have himage : (fun h : Sp62 => h * (m⁻¹ * y * m) * h⁻¹) ''
        (Subgroup.centralizer ({ρ} : Set Sp62) : Set Sp62) =
        (fun z => m⁻¹ * z * m) '' ((fun h : Sp62 => h * y * h⁻¹) ''
          (Subgroup.centralizer ({m * ρ * m⁻¹} : Set Sp62) : Set Sp62)) := by
      ext z
      simp only [Set.mem_image, SetLike.mem_coe]
      constructor
      · rintro ⟨h, hh, rfl⟩
        refine ⟨(m * h * m⁻¹) * y * (m * h * m⁻¹)⁻¹, ⟨m * h * m⁻¹, ?_, rfl⟩, by group⟩
        rw [conj_mem_centralizer_iff]
        simpa [mul_assoc] using hh
      · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
        exact ⟨m⁻¹ * h * m, conj_mem_centralizer_iff.mp hh, by group⟩
    have hsmall' : ((fun h : Sp62 => h * (m⁻¹ * y * m) * h⁻¹) ''
        (Subgroup.centralizer ({ρ} : Set Sp62) : Set Sp62)).ncard ≤ 6 := by
      rw [himage, Set.ncard_image_of_injective _ (fun a b e => by simpa using e)]
      exact hsmall
    refine false_of_small_rep hk01 hρ hy' (fun e => hy1 ?_) (fun e => hyτ ?_) hsmall' hh₀' ?_
    · calc y = m * (m⁻¹ * y * m) * m⁻¹ := by group
        _ = 1 := by rw [e]; group
    · calc y = m * (m⁻¹ * y * m) * m⁻¹ := by group
        _ = m * ρ * m⁻¹ := by rw [e]
    · calc m⁻¹ * h₀ * m * (m⁻¹ * y * m) * (m⁻¹ * h₀ * m)⁻¹ = m⁻¹ * (h₀ * y * h₀⁻¹) * m := by
            group
        _ = ρ * (m⁻¹ * y * m) := by rw [hconj]; group
  interval_cases k
  · exact hsmallk (Or.inl rfl)
  · exact hsmallk (Or.inr rfl)
  · exact hbig (Or.inl rfl)
  · exact hbig (Or.inr rfl)

end CFSG.LargeExtraspecial.AS35QCo
