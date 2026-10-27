module

public import CFSG.GH74.GLS.Stage4.RestX2Q1
public import CFSG.GH74.GLS.Stage4.T6Cent
public import CFSG.GH74.GLS.Stage4.T6SylN

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem cent_two_mem_zpowers (h : T6Ctx N u p) (h' : T6Ctx N.swap u p) {d : G}
    (hdz : d * N.z = N.z * d) (hd2 : ∃ k : ℕ, d ^ (2 ^ k) = 1)
    (hdX₁ : ∀ x ∈ N.X₁, d * x * d⁻¹ = x) (hdX₂ : ∀ x ∈ N.X₂, d * x * d⁻¹ = x) :
    d ∈ Subgroup.zpowers N.z := by
  have hloc := h.sec5.loc
  have hz2 := h.ctx.zz
  have hdK := two_cent_X₂_mem_K h hdz hd2 hdX₂
  obtain ⟨k₁, hk₁, k₂, hk₂, hdk⟩ := (mem_sup_iff_of_comm hloc.K_comm d).1 hdK
  have hk₂c : ∀ x ∈ N.X₂, k₂ * x = x * k₂ := by
    intro x hx
    have hxK : x ∈ N.K₂ := by rw [hloc.K₂_eq]; exact Subgroup.mem_sup_left hx
    have h1 := hdX₂ x hx
    have h2 : d * x = x * d := by
      calc d * x = (d * x * d⁻¹) * d := by group
        _ = x * d := by rw [h1]
    have h3 : k₁ * x = x * k₁ := hloc.K_comm k₁ hk₁ x hxK
    rw [hdk] at h2
    apply mul_left_cancel (a := k₁)
    calc k₁ * (k₂ * x) = k₁ * k₂ * x := by group
      _ = x * (k₁ * k₂) := h2
      _ = (x * k₁) * k₂ := by group
      _ = (k₁ * x) * k₂ := by rw [h3]
      _ = k₁ * (x * k₂) := by group
  have hk₁c : ∀ x ∈ N.X₁, k₁ * x = x * k₁ := by
    intro x hx
    have hxK : x ∈ N.K₁ := X₁_le_K₁ h hx
    have h1 := hdX₁ x hx
    have h2 : d * x = x * d := by
      calc d * x = (d * x * d⁻¹) * d := by group
        _ = x * d := by rw [h1]
    have h3 : k₂ * x = x * k₂ := (hloc.K_comm x hxK k₂ hk₂).symm
    rw [hdk] at h2
    apply mul_right_cancel (b := k₂)
    calc k₁ * x * k₂ = k₁ * (x * k₂) := by group
      _ = k₁ * (k₂ * x) := by rw [h3]
      _ = k₁ * k₂ * x := by group
      _ = x * (k₁ * k₂) := h2
      _ = x * k₁ * k₂ := by group
  have h2' : k₂ ∈ N.X₂ ∨ k₂ * N.z ∈ N.X₂ := Cent_K₂_X₂ h k₂ hk₂ hk₂c
  have h1' : k₁ ∈ N.X₁ ∨ k₁ * N.z ∈ N.X₁ := Cent_K₂_X₂ h' k₁ hk₁ hk₁c
  have hzk₂ : N.z * k₂ = k₂ * N.z := (h.zK k₂ (Subgroup.mem_sup_right hk₂)).symm
  have hzk₁ : N.z * k₁ = k₁ * N.z := (h.zK k₁ (Subgroup.mem_sup_left hk₁)).symm
  obtain ⟨a₁, ha₁, a₂, ha₂, hdx⟩ : ∃ a₁ ∈ N.X₁, ∃ a₂ ∈ N.X₂, d = a₁ * a₂ ∨ d = a₁ * a₂ * N.z := by
    rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
    · exact ⟨k₁, h1', k₂, h2', Or.inl hdk⟩
    · refine ⟨k₁, h1', k₂ * N.z, h2', Or.inr ?_⟩
      rw [hdk]
      calc k₁ * k₂ = k₁ * (k₂ * (N.z * N.z)) := by rw [hz2, mul_one]
        _ = k₁ * (k₂ * N.z) * N.z := by group
    · refine ⟨k₁ * N.z, h1', k₂, h2', Or.inr ?_⟩
      rw [hdk]
      calc k₁ * k₂ = k₁ * (k₂ * (N.z * N.z)) := by rw [hz2, mul_one]
        _ = k₁ * (k₂ * N.z) * N.z := by group
        _ = k₁ * (N.z * k₂) * N.z := by rw [hzk₂]
        _ = k₁ * N.z * k₂ * N.z := by group
    · refine ⟨k₁ * N.z, h1', k₂ * N.z, h2', Or.inl ?_⟩
      rw [hdk]
      calc k₁ * k₂ = k₁ * (k₂ * (N.z * N.z)) := by rw [hz2, mul_one]
        _ = k₁ * (k₂ * N.z) * N.z := by group
        _ = k₁ * (N.z * k₂) * N.z := by rw [hzk₂]
        _ = k₁ * N.z * (k₂ * N.z) := by
            calc k₁ * (N.z * k₂) * N.z = k₁ * (N.z * (k₂ * N.z)) := by group
              _ = k₁ * N.z * (k₂ * N.z) := by group
  have hcomm : Commute a₁ a₂ := X₁_X₂_comm h a₁ ha₁ a₂ ha₂
  have hxp : ∃ j : ℕ, (a₁ * a₂) ^ (p ^ j) = 1 := by
    obtain ⟨j₁, hj₁⟩ := X₁_pGroup h ⟨a₁, ha₁⟩
    obtain ⟨j₂, hj₂⟩ := X₂_pGroup h ⟨a₂, ha₂⟩
    have e₁ : a₁ ^ (p ^ j₁) = 1 := by simpa using congrArg Subtype.val hj₁
    have e₂ : a₂ ^ (p ^ j₂) = 1 := by simpa using congrArg Subtype.val hj₂
    refine ⟨j₁ + j₂, ?_⟩
    rw [hcomm.mul_pow, pow_add, pow_mul, e₁, one_pow, mul_comm (p ^ j₁), pow_mul, e₂, one_pow, one_mul]
  obtain ⟨j, hj⟩ := hxp
  obtain ⟨k, hk⟩ := hd2
  have hcop : Nat.Coprime (p ^ j) (2 ^ (k + 1)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes h.prime Nat.prime_two).2 h.p_ne_two)
  have hzc : Commute (a₁ * a₂) N.z := by
    have hK : a₁ * a₂ ∈ N.K₁ ⊔ N.K₂ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (X₁_le_K₁ h ha₁))
        (Subgroup.mem_sup_right (X₂_le_K₂ h ha₂))
    exact (h.zK _ hK)
  have hzpow : N.z ^ (2 ^ (k + 1)) = 1 := by
    have : N.z ^ 2 = 1 := by rw [pow_two]; exact hz2
    rw [pow_succ', pow_mul, this, one_pow]
  have hdk1 : d ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul, hk, one_pow]
  have hx1 : a₁ * a₂ = 1 := by
    have hx2 : (a₁ * a₂) ^ (2 ^ (k + 1)) = 1 := by
      rcases hdx with hdx | hdx
      · rw [← hdx]; exact hdk1
      · rw [hdx, hzc.mul_pow, hzpow, mul_one] at hdk1
        exact hdk1
    have h1 : orderOf (a₁ * a₂) ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
    have h2 : orderOf (a₁ * a₂) ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hx2
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rcases hdx with hdx | hdx
  · rw [hdx, hx1]; exact Subgroup.one_mem _
  · rw [hdx, hx1, one_mul]; exact Subgroup.mem_zpowers _

end CFSG.GH74.GLS.Stage4.Rest.T6.P71
