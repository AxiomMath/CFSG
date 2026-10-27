module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sa
public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

instance neZero_two_pow (m : ℕ) : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩

structure Model {P : Type*} [Group P] (L : Subgroup P) (ι : P) (J : Subgroup P) (m : ℕ) where
  ρ : DihedralGroup (2 ^ m) →* P
  t₀ : P
  two_le : 2 ≤ m
  inj : Function.Injective ρ
  le_J : ∀ x, ρ x ∈ J
  J_le_L : J ≤ L
  t₀_mem : t₀ ∈ L
  J_le : J ≤ centralizer ({ι} : Set P)
  normJ : ∀ c ∈ centralizer ({ι} : Set P) ⊓ L, ∀ x, x ∈ J ↔ c * x * c⁻¹ ∈ J
  inf_cent : J ⊓ centralizer (J : Set P) = ⊥
  comm : ∀ x y, ρ x * (t₀⁻¹ * ρ y * t₀) = (t₀⁻¹ * ρ y * t₀) * ρ x
  gamma : ρ (r (cc m)) * (t₀⁻¹ * ρ (r 1) * t₀) ∈ centralizer (J : Set P)
  sr_not : t₀⁻¹ * ρ (sr 0) * t₀ ∉ J ⊔ centralizer (J : Set P)
  iota : ι = t₀⁻¹ * ρ (r (cc m)) * t₀
  sq : t₀ * t₀ = ι * ρ (r (cc m))
  not_conj : ∀ g ∈ L, g * ι * g⁻¹ ≠ ι * ρ (r (cc m))
  dvd_L : 2 ^ (2 * m + 3) ∣ Nat.card L
  not_dvd_L : ¬ 2 ^ (2 * m + 4) ∣ Nat.card L
  not_dvd_J : ¬ 2 ^ (m + 2) ∣ Nat.card J

namespace Model

variable {P : Type*} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

@[expose] def z₁ : P := M.ρ (r (cc m))

@[expose] def ρ₂ : DihedralGroup (2 ^ m) →* P :=
  (MulAut.conj M.t₀⁻¹).toMonoidHom.comp M.ρ

theorem ρ₂_apply (x : DihedralGroup (2 ^ m)) : M.ρ₂ x = M.t₀⁻¹ * M.ρ x * M.t₀ := by
  simp [ρ₂]

theorem ρ₂_injective : Function.Injective M.ρ₂ :=
  (MulAut.conj M.t₀⁻¹).injective.comp M.inj

@[expose] def D₁ : Subgroup P := M.ρ.range

@[expose] def D₂ : Subgroup P := M.ρ₂.range

theorem D₂_eq : M.D₂ = conjugate M.D₁ M.t₀ := by
  rw [D₂, D₁, ρ₂, MonoidHom.range_comp, conjugate]

theorem z₁_sq : M.z₁ * M.z₁ = 1 := by rw [z₁, ← map_mul, r_cc_sq M.two_le, map_one]

theorem z₁_inv : M.z₁⁻¹ = M.z₁ := inv_eq_of_mul_eq_one_right M.z₁_sq

theorem z₁_ne : M.z₁ ≠ 1 := fun h => r_cc_ne M.two_le (M.inj (by rw [map_one]; exact h))

theorem z₁_mem_J : M.z₁ ∈ J := M.le_J _

theorem z₁_mem_D₁ : M.z₁ ∈ M.D₁ := ⟨_, rfl⟩

theorem iota_eq : ι = M.ρ₂ (r (cc m)) := by rw [M.ρ₂_apply]; exact M.iota

theorem iota_mem_D₂ : ι ∈ M.D₂ := ⟨_, M.iota_eq.symm⟩

theorem iota_comm₂ (x : DihedralGroup (2 ^ m)) : ι * M.ρ₂ x = M.ρ₂ x * ι := by
  have h : M.ρ₂ (r (cc m)) * M.ρ₂ x = M.ρ₂ x * M.ρ₂ (r (cc m)) := by
    rw [← map_mul, ← map_mul, r_cc_central M.two_le]
  rwa [← M.iota_eq] at h

theorem iota_comm₁ (x : DihedralGroup (2 ^ m)) : ι * M.ρ x = M.ρ x * ι :=
  (mem_centralizer_singleton_iff.mp (M.J_le (M.le_J x))).symm

theorem comm₁₂ (x y : DihedralGroup (2 ^ m)) : M.ρ x * M.ρ₂ y = M.ρ₂ y * M.ρ x := by
  rw [M.ρ₂_apply]; exact M.comm x y

include M in
theorem iota_ne : ι ≠ 1 := by
  intro h
  have h1 : M.ρ₂ (r (cc m)) = 1 := by rw [← M.iota_eq]; exact h
  exact r_cc_ne M.two_le (M.ρ₂_injective (by rw [map_one]; exact h1))

include M in
theorem iota_mem_cent : ι ∈ centralizer (J : Set P) := by
  rw [mem_centralizer_iff]
  intro x hx
  exact (mem_centralizer_singleton_iff.mp (M.J_le hx))

theorem iota_comm_z₁ : ι * M.z₁ = M.z₁ * ι := M.iota_comm₁ _

include M in
theorem mem_one_of_mem_J_cent {x : P} (hx : x ∈ J) (hc : x ∈ centralizer (J : Set P)) :
    x = 1 := by
  have : x ∈ J ⊓ centralizer (J : Set P) := ⟨hx, hc⟩
  rwa [M.inf_cent, mem_bot] at this

@[expose] def γ : P := M.z₁ * M.ρ₂ (r 1)

theorem γ_mem : M.γ ∈ centralizer (J : Set P) := by
  rw [γ, M.ρ₂_apply]; exact M.gamma

theorem ρ₂_r_one : M.ρ₂ (r 1) = M.z₁ * M.γ := by
  rw [γ, ← mul_assoc, M.z₁_sq, one_mul]

theorem z₁_comm_ρ₂ (y : DihedralGroup (2 ^ m)) : M.z₁ * M.ρ₂ y = M.ρ₂ y * M.z₁ :=
  M.comm₁₂ _ y

theorem z₁_comm_γ : M.z₁ * M.γ = M.γ * M.z₁ :=
  ((Commute.refl M.z₁).mul_right (M.z₁_comm_ρ₂ (r 1))).eq

theorem z₁_pow_even {k : ℕ} (hk : Even k) : M.z₁ ^ k = 1 := by
  obtain ⟨c, rfl⟩ := hk
  rw [← two_mul, pow_mul, _root_.sq, M.z₁_sq, one_pow]

theorem z₁_pow_odd {k : ℕ} (hk : Odd k) : M.z₁ ^ k = M.z₁ := by
  obtain ⟨c, rfl⟩ := hk
  rw [pow_succ, pow_mul, _root_.sq, M.z₁_sq, one_pow, one_mul]

theorem ρ₂_r (j : ZMod (2 ^ m)) : M.ρ₂ (r j) = M.z₁ ^ j.val * M.γ ^ j.val := by
  rw [← (Commute.mul_pow M.z₁_comm_γ), ← M.ρ₂_r_one, ← map_pow, r_one_pow,
    ZMod.natCast_zmod_val]

include M in
theorem even_two_pow_pred : Even (2 ^ (m - 1)) :=
  (Nat.even_pow' (by have := M.two_le; omega)).mpr even_two

theorem orderOf_γ : orderOf M.γ = 2 ^ m := by
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := M.two_le; omega⟩
  have he : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  have hpow : M.γ ^ 2 ^ m = 1 := by
    have h2 : M.ρ₂ (r 1) ^ 2 ^ m = 1 := by rw [← map_pow, r_one_pow_n, map_one]
    rwa [M.ρ₂_r_one, Commute.mul_pow M.z₁_comm_γ, M.z₁_pow_even he, one_mul] at h2
  have hne : M.γ ^ 2 ^ k ≠ 1 := by
    intro h
    have h1 := M.ρ₂_r (cc m)
    have hk' : m - 1 = k := by omega
    rw [val_cc M.two_le, hk', h, mul_one, M.z₁_pow_even (hk' ▸ M.even_two_pow_pred),
      ← M.iota_eq] at h1
    exact M.iota_ne h1
  have e : 2 ^ m = 2 ^ (k + 1) := by rw [hk]
  rw [e] at hpow ⊢
  exact orderOf_eq_prime_pow hne hpow

end Model

end CFSG.ComponentClassification.GSThmB.P29
