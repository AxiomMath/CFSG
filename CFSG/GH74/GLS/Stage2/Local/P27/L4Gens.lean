module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Grp

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.L4

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

section Aux

variable {G : Type} [Group G]

theorem gens_mem_zpowers_iff {z x : G} (hz2 : z * z = 1) : x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
    have hk : z ^ k = z ^ (k % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [hk, h, zpow_zero]
    · right; rw [hk, h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem gens_exists_pow [Finite G] {ρ x : G} (hx : x ∈ zpowers ρ) : ∃ k : ℕ, x = ρ ^ k := by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff x ρ).1 (mem_powers_iff_mem_zpowers.2 hx)
  exact ⟨k, hk.symm⟩

theorem gens_mem_sup {P₁ : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hwn : ∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁) {x : G} (hx : x ∈ P₁ ⊔ zpowers w) :
    x ∈ P₁ ∨ ∃ p ∈ P₁, x = p * w :=
  (Psp4.mem_sup_zpowers_iff hwn (by rw [hw2]; exact one_mem _)).1 hx

theorem gens_sq_mem {P₁ : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hwn : ∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁) {x : G} (hx : x ∈ P₁ ⊔ zpowers w) : x * x ∈ P₁ := by
  rcases gens_mem_sup hw2 hwn hx with h | ⟨p, hp, rfl⟩
  · exact mul_mem h h
  · have : p * w * (p * w) = p * (w * p * w⁻¹) * (w * w) := by group
    rw [this, hw2, mul_one]
    exact mul_mem hp (hwn p hp)

theorem gens_no_order_card [Finite G] {P : Subgroup G} {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (eQ : ↥P ≃* QuaternionGroup N) {ρ : G} (hρ : ρ ∈ P) (hord : orderOf ρ = 4 * N) : False := by
  obtain ⟨a₀, b₀, ha₀, hb₀, hQG, -⟩ := quat_gens eQ
  have hcard : Nat.card ↥P = 4 * N := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have heq : zpowers ρ = P := by
    apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hρ)
    rw [Nat.card_zpowers, hord, hcard]
  have ha' : a₀ ∈ zpowers ρ := heq ▸ ha₀
  have hb' : b₀ ∈ zpowers ρ := heq ▸ hb₀
  have hcomm : b₀ * a₀ = a₀ * b₀ := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb'
    exact (Commute.zpow_zpow_self ρ j i).eq
  have h1 : a₀⁻¹ * b₀ = a₀ * b₀ := by rw [← hQG.bcomm, hcomm]
  have h2 : a₀⁻¹ = a₀ := mul_right_cancel h1
  have h3 : a₀ ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 1 [← h2]; exact inv_mul_cancel a₀
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hQG.ord] at h4
  have := Nat.le_of_dvd (by omega) h4
  omega

theorem gens_orderOf_eq {ρ z : G} {m : ℕ} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h : ρ ^ (2 ^ m) = z) : orderOf ρ = 2 ^ (m + 1) := by
  refine orderOf_eq_prime_pow (p := 2) (n := m) (by rw [h]; exact hz1) ?_
  rw [pow_succ, pow_mul, h, pow_two, hz2]

theorem gens_core [Finite G] {P₁ : Subgroup G} {z w : G} {e : ℕ}
    (eQ : ↥P₁ ≃* QuaternionGroup (2 ^ (e + 1)))
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzP : z ∈ P₁)
    (hzc : ∀ x ∈ P₁, x * z = z * x)
    (hzuniq : ∀ x ∈ P₁, x * x = 1 → x ≠ 1 → x = z)
    (hzw : z * w = w * z)
    (hw2 : w * w = 1) (hwP : w ∉ P₁) (hwn : ∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁)
    (φ : ↥(P₁ ⊔ zpowers w) →* DihedralGroup (2 ^ (e + 2))) (hφ : Function.Surjective φ)
    (hker : ∀ x : ↥(P₁ ⊔ zpowers w), φ x = 1 ↔ ((x : G) = 1 ∨ (x : G) = z)) :
    ∃ c d : G, c ∈ P₁ ∧ d ∈ P₁ ∧ QG c d (2 ^ (e + 1)) ∧
      (∀ x ∈ P₁, ∃ k : ℕ, x = c ^ k ∨ x = c ^ k * d) ∧ z = c ^ (2 ^ (e + 1)) ∧
      w * c * w⁻¹ = c⁻¹ ∧ w * d * w⁻¹ = z * c⁻¹ * d := by
  have hw1 : w ≠ 1 := fun h => hwP (h ▸ one_mem P₁)
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwQ : w ∈ P₁ ⊔ zpowers w := mem_sup_right (mem_zpowers w)
  have : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have hfib : ∀ x y : ↥(P₁ ⊔ zpowers w), φ x = φ y → (x : G) = y ∨ (x : G) = y * z := by
    intro x y hxy
    have h1 : φ (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    rcases (hker _).1 h1 with h | h
    · left
      have h' : (y : G)⁻¹ * x = 1 := h
      exact (inv_mul_eq_one.1 h').symm
    · right
      have h' : (y : G)⁻¹ * x = z := h
      rw [← h']; group
  obtain ⟨R, hR⟩ := hφ (DihedralGroup.r 1)
  have hφpow : ∀ k : ℕ, φ (R ^ k) = DihedralGroup.r (k : ZMod (2 ^ (e + 2))) := fun k => by
    rw [map_pow, hR, DihedralGroup.r_one_pow]
  have hρQ : (R : G) ∈ P₁ ⊔ zpowers w := R.2
  set ρ : G := (R : G) with hρ
  have hρ2N : ρ ^ 2 ^ (e + 2) = z := by
    have h1 : φ (R ^ 2 ^ (e + 2)) = 1 := by
      rw [hφpow, ZMod.natCast_self, DihedralGroup.one_def]
    rcases (hker _).1 h1 with h | h
    · exfalso
      have hρ1 : ρ ^ 2 ^ (e + 2) = 1 := h
      have hsqρ : ρ * ρ ∈ P₁ := gens_sq_mem hw2 hwn hρQ
      have hvP : ρ ^ 2 ^ (e + 1) ∈ P₁ := by
        have : ρ ^ 2 ^ (e + 1) = (ρ * ρ) ^ 2 ^ e := by
          rw [← pow_two, ← pow_mul, ← pow_succ']
        rw [this]; exact pow_mem hsqρ _
      have hv2 : ρ ^ 2 ^ (e + 1) * ρ ^ 2 ^ (e + 1) = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ']; exact hρ1
      have hne : φ (R ^ 2 ^ (e + 1)) ≠ 1 := by
        rw [hφpow, DihedralGroup.one_def]
        intro h
        have h' : ((2 ^ (e + 1) : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
          injection h
        rw [ZMod.natCast_eq_zero_iff] at h'
        have h3 := Nat.le_of_dvd (by positivity) h'
        rw [pow_succ 2 (e + 1)] at h3
        have : 0 < 2 ^ (e + 1) := by positivity
        omega
      have hv1 : ρ ^ 2 ^ (e + 1) ≠ 1 := fun h => hne ((hker _).2 (Or.inl h))
      have hvz := hzuniq _ hvP hv2 hv1
      exact hne ((hker _).2 (Or.inr hvz))
    · exact h
  have hρord : orderOf ρ = 2 ^ (e + 3) := gens_orderOf_eq hz2 hz1 hρ2N
  have hzρ : z ∈ zpowers ρ := by rw [← hρ2N]; exact pow_mem (mem_zpowers ρ) _
  have hzQ : ∀ x ∈ P₁ ⊔ zpowers w, x * z = z * x := by
    intro x hx
    rcases gens_mem_sup hw2 hwn hx with h | ⟨p, hp, rfl⟩
    · exact hzc x h
    · calc p * w * z = p * (w * z) := mul_assoc _ _ _
        _ = p * (z * w) := by rw [hzw]
        _ = p * z * w := (mul_assoc _ _ _).symm
        _ = z * p * w := by rw [hzc p hp]
        _ = z * (p * w) := mul_assoc _ _ _
  have hcomm : Commute ρ z := hzQ ρ hρQ
  have hρP : ρ ∉ P₁ := by
    intro h
    refine gens_no_order_card (N := 2 ^ (e + 1)) ?_ eQ h ?_
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hρord]; ring
  obtain ⟨p, hpP, hρp⟩ : ∃ p ∈ P₁, ρ = p * w := by
    rcases gens_mem_sup hw2 hwn hρQ with h | h
    · exact absurd h hρP
    · exact h
  have hdP : ρ * w ∈ P₁ := by
    have : ρ * w = p := by rw [hρp, mul_assoc, hw2, mul_one]
    rw [this]; exact hpP
  have hwρ : w ∉ zpowers ρ := by
    intro h
    obtain ⟨k, hk⟩ := gens_exists_pow h
    have hk2 : ρ ^ k * ρ ^ k = 1 := by rw [← hk]; exact hw2
    have hord' : orderOf ρ = 2 * 2 ^ (e + 2) := by rw [hρord]; ring
    rcases Psp4.eq_one_or_pow_half hord' hk2 with h1 | h1
    · exact hw1 (hk.trans h1)
    · exact hwP (by rw [hk, h1, hρ2N]; exact hzP)
  obtain ⟨j, hj⟩ : ∃ j : ZMod (2 ^ (e + 2)), φ ⟨w, hwQ⟩ = DihedralGroup.sr j := by
    rcases hφw : φ ⟨w, hwQ⟩ with i | j
    · exfalso
      have h1 : φ ⟨w, hwQ⟩ = φ (R ^ i.val) := by
        rw [hφpow, ZMod.natCast_zmod_val, hφw]
      rcases hfib _ _ h1 with h | h
      · exact hwρ (by rw [show w = ρ ^ i.val from h]; exact pow_mem (mem_zpowers ρ) _)
      · exact hwρ (by
          rw [show w = ρ ^ i.val * z from h]
          exact mul_mem (pow_mem (mem_zpowers ρ) _) hzρ)
    · exact ⟨j, rfl⟩
  have hconj : (w * ρ * w⁻¹ = ρ⁻¹) ∨ (w * ρ * w⁻¹ = ρ⁻¹ * z) := by
    have h1 : φ (⟨w, hwQ⟩ * R * ⟨w, hwQ⟩⁻¹) = φ R⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, hj, hR]
      rw [DihedralGroup.inv_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr]
      congr 1; ring
    exact hfib _ _ h1
  have hX : w * ρ * w⁻¹ = ρ⁻¹ * z := by
    rcases hconj with h | h
    · exfalso
      have hd2 : (ρ * w) * (ρ * w) = 1 := by
        calc ρ * w * (ρ * w) = ρ * (w * ρ * w⁻¹) * (w * w) := by group
          _ = 1 := by rw [h, hw2]; group
      have hd1 : ρ * w ≠ 1 := by
        intro h1
        apply hwρ
        have h2 : ρ = w⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [hwinv] at h2
        rw [← h2]; exact mem_zpowers ρ
      have hdz := hzuniq _ hdP hd2 hd1
      apply hwρ
      have h3 : w = ρ⁻¹ * z := by rw [← hdz]; group
      rw [h3]
      exact mul_mem (inv_mem (mem_zpowers ρ)) hzρ
    · exact h
  set c : G := ρ ^ 2 with hc
  set d : G := ρ * w with hd
  have hcP : c ∈ P₁ := by rw [hc, pow_two]; exact gens_sq_mem hw2 hwn hρQ
  have hcz : c ^ 2 ^ (e + 1) = z := by
    rw [hc, ← pow_mul, ← pow_succ']; exact hρ2N
  have hcord : orderOf c = 2 * 2 ^ (e + 1) := by
    rw [gens_orderOf_eq hz2 hz1 hcz]; ring
  have hwc : w * c * w⁻¹ = c⁻¹ := by
    calc w * c * w⁻¹ = (w * ρ * w⁻¹) ^ 2 := by rw [hc, conj_pow]
      _ = (ρ⁻¹ * z) ^ 2 := by rw [hX]
      _ = (ρ⁻¹) ^ 2 * z ^ 2 := hcomm.inv_left.mul_pow 2
      _ = c⁻¹ := by rw [pow_two z, hz2, mul_one, hc, inv_pow]
  have hwd : w * d * w⁻¹ = z * c⁻¹ * d := by
    calc w * d * w⁻¹ = (w * ρ * w⁻¹) * w := by rw [hd]; group
      _ = (ρ⁻¹ * z) * w := by rw [hX]
      _ = (z * ρ⁻¹) * w := by rw [hcomm.inv_left.eq]
      _ = z * c⁻¹ * d := by rw [hd, hc]; group
  have hQG : QG c d (2 ^ (e + 1)) := by
    refine ⟨hcord, ?_, ?_⟩
    · rw [hcz]
      have hwρw : w * ρ * w = ρ⁻¹ * z := by rw [hwinv] at hX; exact hX
      calc d * d = ρ * (w * ρ * w) := by rw [hd]; group
        _ = ρ * (ρ⁻¹ * z) := by rw [hwρw]
        _ = z := by group
    · have hwc' : w * c = c⁻¹ * w := (mul_inv_eq_iff_eq_mul).1 hwc
      calc d * c = ρ * (w * c) := by rw [hd]; group
        _ = ρ * (c⁻¹ * w) := by rw [hwc']
        _ = c⁻¹ * d := by rw [hd, hc]; group
  have hdC : d ∉ zpowers c := by
    intro h
    apply hwρ
    have hcρ : c ∈ zpowers ρ := by rw [hc]; exact pow_mem (mem_zpowers ρ) 2
    have hdρ : d ∈ zpowers ρ := (zpowers_le.2 hcρ) h
    have h3 : w = ρ⁻¹ * d := by rw [hd]; group
    rw [h3]
    exact mul_mem (inv_mem (mem_zpowers ρ)) hdρ
  have hspan : ∀ x ∈ P₁, ∃ k : ℕ, x = c ^ k ∨ x = c ^ k * d := by
    have hCle : zpowers c ≤ P₁ := (zpowers_le).2 hcP
    have hPcard : Nat.card ↥P₁ = 2 ^ (e + 3) := by
      rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]; ring
    have hC'card : Nat.card ↥((zpowers c).subgroupOf P₁) = 2 ^ (e + 2) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hCle).toEquiv, Nat.card_zpowers, hcord]; ring
    have hidx : ((zpowers c).subgroupOf P₁).index = 2 := by
      have h := ((zpowers c).subgroupOf P₁).card_mul_index
      rw [hC'card, hPcard] at h
      have h' : 2 ^ (e + 2) * ((zpowers c).subgroupOf P₁).index = 2 ^ (e + 2) * 2 := by
        rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
    intro x hx
    by_cases hxC : x ∈ zpowers c
    · obtain ⟨k, hk⟩ := gens_exists_pow hxC
      exact ⟨k, Or.inl hk⟩
    · have hxd : (⟨x, hx⟩ : ↥P₁) * ⟨d, hdP⟩⁻¹ ∈ (zpowers c).subgroupOf P₁ := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        refine iff_of_false ?_ ?_
        · rwa [Subgroup.mem_subgroupOf]
        · rw [Subgroup.mem_subgroupOf]
          intro h
          exact hdC (by simpa using h)
      have h1 : x * d⁻¹ ∈ zpowers c := by
        rwa [Subgroup.mem_subgroupOf] at hxd
      obtain ⟨k, hk⟩ := gens_exists_pow h1
      refine ⟨k, Or.inr ?_⟩
      rw [← hk]; group
  exact ⟨c, d, hcP, hdP, hQG, hspan, hcz.symm, hwc, hwd⟩

end Aux

theorem exists_adapted_gens {G : Type} [Group G] [Finite G] {P₁ : Subgroup G} {z w : G} {a : ℕ}
    (hquat : IVK.IsQuaternionTwoGroup ↥P₁ a)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzP : z ∈ P₁)
    (hzc : ∀ x ∈ P₁, x * z = z * x)
    (hzuniq : ∀ x ∈ P₁, x * x = 1 → x ≠ 1 → x = z)
    (hzw : z * w = w * z)
    (hw2 : w * w = 1) (hwP : w ∉ P₁) (hwn : ∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁)
    (hdih : ∃ (D : Type) (_ : Group D) (f : ↥(P₁ ⊔ zpowers w) →* D),
      Function.Surjective f ∧ f.ker = (zpowers z).subgroupOf (P₁ ⊔ zpowers w) ∧
        IVK.IsDihedralTwoGroup D a) :
    ∃ c d : G, c ∈ P₁ ∧ d ∈ P₁ ∧ CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q.QG c d (2 ^ (a - 2)) ∧
      (∀ x ∈ P₁, ∃ k : ℕ, x = c ^ k ∨ x = c ^ k * d) ∧ z = c ^ (2 ^ (a - 2)) ∧
      w * c * w⁻¹ = c⁻¹ ∧ w * d * w⁻¹ = z * c⁻¹ * d := by
  obtain ⟨ha3, ⟨eQ⟩⟩ := hquat
  obtain ⟨D, instD, f, hfsurj, hfker, h2a, k, hk, hk2, ⟨ι⟩⟩ := hdih
  obtain ⟨e, rfl⟩ : ∃ e, a = e + 3 := ⟨a - 3, by omega⟩
  have hk' : k = 2 ^ (e + 2) := by
    have : 2 ^ (e + 3) = 2 * 2 ^ (e + 2) := by ring
    omega
  subst hk'
  have hsub : e + 3 - 2 = e + 1 := by omega
  rw [hsub] at eQ ⊢
  have hker : ∀ x : ↥(P₁ ⊔ zpowers w), (ι.toMonoidHom.comp f) x = 1 ↔
      ((x : G) = 1 ∨ (x : G) = z) := by
    intro x
    have h1 : (ι.toMonoidHom.comp f) x = 1 ↔ f x = 1 := by
      show ι (f x) = 1 ↔ f x = 1
      exact map_eq_one_iff ι ι.injective
    rw [h1, ← MonoidHom.mem_ker, hfker, Subgroup.mem_subgroupOf, gens_mem_zpowers_iff hz2]
  exact gens_core eQ hz2 hz1 hzP hzc hzuniq hzw hw2 hwP hwn (ι.toMonoidHom.comp f)
    (ι.surjective.comp hfsurj) hker

end CFSG.GH74.GLS.Stage2.Local.P27.L4
