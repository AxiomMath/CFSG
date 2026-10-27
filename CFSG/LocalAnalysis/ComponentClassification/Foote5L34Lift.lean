module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L34Real
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34

public section

namespace CFSG.ComponentClassification.Foote5.L34Real

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

variable {Y₀ : Type} [Group Y₀] {q : Y₀ →* Equiv.Perm (Fin 42)}
  {ψ : MulAut Y₀ →* Equiv.Perm (Fin 42)}

theorem inv_mul_mem_center (hqker : q.ker = center Y₀)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) {α : MulAut Y₀} {y : Y₀}
    (hy : ψ α * q y = q y * ψ α) : y⁻¹ * α y ∈ center Y₀ := by
  rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hψ, hy]
  group

theorem commutator_mem_map_fixed (hqsurj : ∀ s ∈ S, ∃ y, q y = s) (hqker : q.ker = center Y₀)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) (α : MulAut Y₀) {s₁ s₂ : Equiv.Perm (Fin 42)}
    (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) (h₁ : ψ α * s₁ = s₁ * ψ α) (h₂ : ψ α * s₂ = s₂ * ψ α) :
    ⁅s₁, s₂⁆ ∈ (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y₀)).map q := by
  obtain ⟨y₁, rfl⟩ := hqsurj s₁ hs₁
  obtain ⟨y₂, rfl⟩ := hqsurj s₂ hs₂
  have hz₁ := inv_mul_mem_center hqker hψ h₁
  have hz₂ := inv_mul_mem_center hqker hψ h₂
  refine ⟨⁅y₁, y₂⁆, ?_, map_commutatorElement q y₁ y₂⟩
  change α ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆
  rw [map_commutatorElement, show α y₁ = y₁ * (y₁⁻¹ * α y₁) by group,
    show α y₂ = y₂ * (y₂⁻¹ * α y₂) by group, commutatorElement_mul_center_left hz₁,
    commutatorElement_mul_center_right hz₂]

theorem le_map_fixed_of_perfect (hqsurj : ∀ s ∈ S, ∃ y, q y = s) (hqker : q.ker = center Y₀)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) (α : MulAut Y₀) {C : Subgroup (Equiv.Perm (Fin 42))}
    (hC : C ≤ centralizer {ψ α} ⊓ S) (hperf : commutator C = ⊤) :
    C ≤ (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y₀)).map q := by
  have hCC : ⁅C, C⁆ = C := by
    have h := congrArg (Subgroup.map C.subtype) hperf
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  rw [← hCC, commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨h₁, hs₁⟩ := Subgroup.mem_inf.mp (hC hg₁)
  obtain ⟨h₂, hs₂⟩ := Subgroup.mem_inf.mp (hC hg₂)
  rw [mem_centralizer_singleton_iff] at h₁ h₂
  exact commutator_mem_map_fixed hqsurj hqker hψ α hs₁ hs₂ h₁.symm h₂.symm

theorem pow_apply_eq_mul_pow {β : MulAut Y₀} {w d : Y₀} (hd : d = w⁻¹ * β w) (hβd : β d = d)
    (n : ℕ) : (β ^ n) w = w * d ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hβd, show β w = w * d by
      rw [hd]; group, pow_succ']
    group

theorem eq_one_of_fixed_of_odd {β : MulAut Y₀} (hβ : Odd (orderOf β)) {w d : Y₀}
    (hd : d = w⁻¹ * β w) (hβd : β d = d) (hd2 : ∃ k : ℕ, orderOf d = 2 ^ k) : d = 1 := by
  have h := pow_apply_eq_mul_pow hd hβd (orderOf β)
  rw [pow_orderOf_eq_one, MulAut.one_apply, left_eq_mul] at h
  obtain ⟨k, hk⟩ := hd2
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ orderOf β := (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hβ) (even_iff_two_dvd.mpr h2)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem eq_of_two_pow_mem_center {α β : MulAut Y₀} (hα2 : ∀ y, α (α y) = y)
    (hαβ : β * α = α * β) (hβ : Odd (orderOf β))
    (hβZ : ∀ z ∈ center Y₀, α z = z → (∃ k : ℕ, orderOf z = 2 ^ k) → β z = z) {z : Y₀}
    (hz : z ∈ center Y₀) (hz2 : ∃ k : ℕ, orderOf z = 2 ^ k) : β z = z := by
  have hαβy : ∀ y, β (α y) = α (β y) := fun y => by
    rw [← MulAut.mul_apply, hαβ, MulAut.mul_apply]
  have hC : ∀ {a : Y₀}, a ∈ center Y₀ → ∀ b, Commute a b := fun ha b =>
    (mem_center_iff.mp ha b).symm
  have hβZ' : ∀ y ∈ center Y₀, β y ∈ center Y₀ := fun y hy => (map_mem_center_iff β y).2 hy
  have hαZ' : ∀ y ∈ center Y₀, α y ∈ center Y₀ := fun y hy => (map_mem_center_iff α y).2 hy
  have hord : ∀ (γ : MulAut Y₀) (y : Y₀), orderOf (γ y) = orderOf y := fun γ y =>
    orderOf_injective γ.toMonoidHom γ.injective y
  have hd : ∀ {w}, w ∈ center Y₀ → (∃ k : ℕ, orderOf w = 2 ^ k) →
      w⁻¹ * β w ∈ center Y₀ ∧ ∃ k : ℕ, orderOf (w⁻¹ * β w) = 2 ^ k := by
    intro w hw ⟨k, hk⟩
    refine ⟨mul_mem (inv_mem hw) (hβZ' w hw), ?_⟩
    have := exists_two_pow_orderOf_mul_inv (hC (hβZ' w hw) w) (by rw [hord, hk]) hk
    rwa [(hC (hβZ' w hw) w⁻¹).eq] at this
  by_contra hne
  set d₀ := z⁻¹ * β z with hd₀
  obtain ⟨hd₀Z, k, hk⟩ := hd hz hz2
  have hd₀1 : d₀ ≠ 1 := fun h => hne (by rw [hd₀, inv_mul_eq_one] at h; exact h.symm)
  obtain ⟨w, hwZ, hw2, hdα, hd1⟩ : ∃ w ∈ center Y₀, (∃ k : ℕ, orderOf w = 2 ^ k) ∧
      α (w⁻¹ * β w) = w⁻¹ * β w ∧ w⁻¹ * β w ≠ 1 := by
    by_cases hprod : d₀ * α d₀ = 1
    ·
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact hd₀1 hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have he : (z ^ 2 ^ m)⁻¹ * β (z ^ 2 ^ m) = d₀ ^ 2 ^ m := by
        rw [hd₀, (Commute.inv_left (hC hz (β z))).mul_pow, inv_pow, map_pow]
      have hsq : (d₀ ^ 2 ^ m) * (d₀ ^ 2 ^ m) = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ', ← hk, pow_orderOf_eq_one]
      refine ⟨z ^ 2 ^ m, pow_mem hz _, ?_, ?_, ?_⟩
      · obtain ⟨j, hj⟩ := hz2
        have hdvd : orderOf (z ^ 2 ^ m) ∣ 2 ^ j := by
          rw [← hj]
          exact orderOf_pow_dvd _
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        exact ⟨i, hi⟩
      · rw [he, map_pow, eq_inv_of_mul_eq_one_right hprod, inv_pow]
        exact inv_eq_of_mul_eq_one_right hsq
      · rw [he]
        intro h1
        have hdvd := orderOf_dvd_of_pow_eq_one h1
        rw [hk] at hdvd
        have := Nat.le_of_dvd (by positivity) hdvd
        rw [pow_succ] at this
        have hpos : 0 < 2 ^ m := by positivity
        omega
    ·
      have he : (z * α z)⁻¹ * β (z * α z) = d₀ * α d₀ := by
        rw [hd₀, map_mul, map_mul, map_inv, hαβy, mul_inv_rev,
          (hC (inv_mem (hαZ' z hz)) z⁻¹).eq]
        have h2 := (hC (hβZ' z hz) (α z)⁻¹).eq
        calc z⁻¹ * (α z)⁻¹ * (β z * α (β z)) = z⁻¹ * ((α z)⁻¹ * β z) * α (β z) := by group
          _ = z⁻¹ * (β z * (α z)⁻¹) * α (β z) := by rw [h2]
          _ = z⁻¹ * β z * ((α z)⁻¹ * α (β z)) := by group
      refine ⟨z * α z, mul_mem hz (hαZ' z hz), ?_, ?_, by rw [he]; exact hprod⟩
      · obtain ⟨j, hj⟩ := hz2
        have := exists_two_pow_orderOf_mul_inv (hC hz (α z)⁻¹) hj
          (by rw [orderOf_inv, hord, hj])
        rwa [inv_inv] at this
      · rw [he, map_mul, hα2]
        exact (hC (hαZ' d₀ hd₀Z) d₀).eq
  obtain ⟨hdZ, hd2⟩ := hd hwZ hw2
  exact hd1 (eq_one_of_fixed_of_odd hβ rfl (hβZ _ hdZ hdα hd2) hd2)

variable [Finite Y₀]

theorem exists_lift_two_pow (hqsurj : ∀ s ∈ S, ∃ y, q y = s) {s : Equiv.Perm (Fin 42)}
    (hs : s ∈ S) (hs8 : s ^ 8 = 1) : ∃ y, q y = s ∧ ∃ k : ℕ, orderOf y = 2 ^ k := by
  obtain ⟨y₀, hy₀⟩ := hqsurj s hs
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₀).ne'
  refine ⟨y₀ ^ (b * b), ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := hb
    have h8 : (2 * c + 1) * (2 * c + 1) = 8 * (c * (c + 1) / 2) + 1 := by
      have := Nat.even_mul_succ_self c
      obtain ⟨e, he⟩ := this
      rw [he]
      have : (e + e) / 2 = e := by omega
      rw [this]
      ring_nf
      nlinarith [he]
    rw [map_pow, hy₀, h8, pow_succ, pow_mul, hs8, one_pow, one_mul]
  · have hdvd : orderOf (y₀ ^ (b * b)) ∣ 2 ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, show b * b * 2 ^ a = (2 ^ a * b) * b by ring, pow_mul, ← hab,
        pow_orderOf_eq_one, one_pow]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨i, hi⟩

theorem conj_comm_mem_map_fixed (hqsurj : ∀ s ∈ S, ∃ y, q y = s) (hqker : q.ker = center Y₀)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) {α β : MulAut Y₀} (hα2 : ∀ y, α (α y) = y)
    (hαβ : β * α = α * β) (hβ : Odd (orderOf β))
    (hβZ : ∀ z ∈ center Y₀, α z = z → (∃ k : ℕ, orderOf z = 2 ^ k) → β z = z)
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ S) (hsα : ψ α * s = s * ψ α) (hs8 : s ^ 8 = 1) :
    s⁻¹ * ψ β * s * (ψ β)⁻¹ ∈ (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y₀)).map q := by
  obtain ⟨y, rfl, hy2⟩ := exists_lift_two_pow hqsurj hs hs8
  set z := y⁻¹ * α y with hzdef
  have hzZ : z ∈ center Y₀ := inv_mul_mem_center hqker hψ hsα
  have hαy : α y = y * z := by rw [hzdef]; group
  have hz2 : ∃ k : ℕ, orderOf z = 2 ^ k := by
    have hc : Commute (α y) y := by
      rw [Commute, SemiconjBy, hαy, mul_assoc, (mem_center_iff.mp hzZ y).symm]
    obtain ⟨k, hk⟩ := hy2
    have := exists_two_pow_orderOf_mul_inv hc
      (by rw [show orderOf (α y) = orderOf y from orderOf_injective α.toMonoidHom α.injective y]
          exact hk) hk
    rwa [show α y * y⁻¹ = z by rw [hαy, mem_center_iff.mp hzZ y, mul_inv_cancel_right]] at this
  have hβz := eq_of_two_pow_mem_center hα2 hαβ hβ hβZ hzZ hz2
  refine ⟨y⁻¹ * β y, ?_, ?_⟩
  · change α (y⁻¹ * β y) = y⁻¹ * β y
    have hαβy : α (β y) = β (α y) := by rw [← MulAut.mul_apply, ← hαβ, MulAut.mul_apply]
    rw [map_mul, map_inv, hαβy, hαy, map_mul, hβz]
    have := mem_center_iff.mp hzZ
    calc (y * z)⁻¹ * (β y * z) = z⁻¹ * (y⁻¹ * β y * z) := by group
      _ = z⁻¹ * (z * (y⁻¹ * β y)) := by rw [this]
      _ = y⁻¹ * β y := by group
  · rw [map_mul, map_inv, hψ]
    group

end CFSG.ComponentClassification.Foote5.L34Real
