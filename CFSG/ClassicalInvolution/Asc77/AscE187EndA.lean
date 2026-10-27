module

public import CFSG.ClassicalInvolution.Asc77.AscE187Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

structure GoodInv (H : Subgroup G) (t δ : G) : Prop where
  ne_one : δ ≠ 1
  sq : δ * δ = 1
  comm_t : δ * t = t * δ
  cent : Subgroup.centralizer ({δ} : Set G) ≤ H

theorem orderOf_eq_two_of_sq {δ : G} (h1 : δ ≠ 1) (h2 : δ * δ = 1) : orderOf δ = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h2) h1

theorem isPGroup_two_sup_zpowers {d₁ d₂ : G} (h₁ : d₁ ≠ 1) (h₁₂ : d₁ * d₁ = 1) (h₂ : d₂ ≠ 1)
    (h₂₂ : d₂ * d₂ = 1) (hc : d₁ * d₂ = d₂ * d₁) :
    IsPGroup 2 (↥(Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂)) := by
  have hp₁ : IsPGroup 2 (Subgroup.zpowers d₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_two_of_sq h₁ h₁₂]; norm_num)
  have hp₂ : IsPGroup 2 (Subgroup.zpowers d₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_two_of_sq h₂ h₂₂]; norm_num)
  refine hp₁.to_sup_of_normal_right' hp₂ ?_
  rw [Subgroup.zpowers_le, mem_normalizer_iff_conjSub_eq]
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  have e : (MulAut.conj d₁).toMonoidHom d₂ = d₂ := by
    show d₁ * d₂ * d₁⁻¹ = d₂
    rw [hc]
    group
  rw [e]

theorem eq_or_eq_inv_of_orderOf_four {u x : G} (hu : orderOf u = 4) (hx : x ∈ Subgroup.zpowers u)
    (hx4 : orderOf x = 4) : x = u ∨ x = u⁻¹ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h4 : u ^ 4 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hmod : u ^ (m % 4) = u ^ m := by
    have := zpow_mod_orderOf u m
    rwa [hu] at this
  have hlt : 0 ≤ m % 4 ∧ m % 4 < 4 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  rw [← hmod] at hx4 ⊢
  have hc : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases hc with h | h | h | h
  · rw [h, zpow_zero, orderOf_one] at hx4
    omega
  · left
    rw [h, zpow_one]
  · exfalso
    rw [h] at hx4
    have hsq : (u ^ (2 : ℤ)) * (u ^ (2 : ℤ)) = 1 := by
      rw [← zpow_add]
      norm_num
      exact_mod_cast h4
    have := orderOf_dvd_of_pow_eq_one (show (u ^ (2 : ℤ)) ^ 2 = 1 by rw [pow_two]; exact hsq)
    rw [hx4] at this
    omega
  · right
    rw [h]
    have : u ^ (3 : ℤ) * u = 1 := by
      rw [← zpow_add_one]
      norm_num
      exact_mod_cast h4
    exact eq_inv_of_mul_eq_one_left this

theorem E187C.endgame_all_of [Finite G] {Ω : Set (Subgroup G)}
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    {H : Subgroup G} {t : G} {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (ht : IsUniqueInvolution K₁ t) (hbad : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (n₁ : conjSub d₁ K₁ = K₁) (n₂ : conjSub d₂ K₁ = K₁) : False := by
  classical
  set D : Subgroup G := Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂ with hDdef
  have hD : IsPGroup 2 D := isPGroup_two_sup_zpowers g₁.ne_one g₁.sq g₂.ne_one g₂.sq hc
  have hd₁D : d₁ ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers d₁)
  have hd₂D : d₂ ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers d₂)
  have hDN : D ≤ Subgroup.normalizer (K₁ : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_iff_conjSub_eq.mpr n₁
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_iff_conjSub_eq.mpr n₂
  obtain ⟨Q, hQ, hQD⟩ := exists_sylow_normalized hD hDN
  have hQR : Q ∈ RSet Ω := mem_RSet_of_isSylow2In hK₁ hQ
  have h8 : 8 ≤ Nat.card Q := h8R hQR
  have htQ : t ∈ Q := mem_of_isUniqueInvolution_of_isPGroup ht hQ.1 hQ.2.1 (by omega)
  have hQt : IsUniqueInvolution Q t :=
    ⟨htQ, ht.ne_one, ht.sq, fun y hy hy2 => ht.unique y (hQ.1 hy) hy2⟩
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := fun d hd =>
    mem_normalizer_iff_conjSub_eq.mpr (hQD d hd)
  have hPp : IsPGroup 2 ↥(D ⊔ Q) := hD.to_sup_of_normal_right' hQ.2.1 hDQ
  have hTn : ∀ x ∈ D ⊔ Q, conjSub x Q = Q := by
    intro x hx
    have hle : D ⊔ Q ≤ Subgroup.normalizer (Q : Set G) := sup_le hDQ Subgroup.le_normalizer
    exact mem_normalizer_iff_conjSub_eq.mp (hle hx)
  obtain ⟨A, hAQ, hAcyc, hAcard, hAinv⟩ :=
    exists_invariant_cyclic_order_four hPp le_sup_right hTn hQt (by omega)
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := ↥A)
  have hu4 : orderOf (u : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu, hAcard]
  have huA : (u : G) ∈ A := u.2
  have hAz : ∀ x ∈ A, x ∈ Subgroup.zpowers (u : G) := by
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hu ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hnH : (u : G) ∉ H := hbad _ (hQ.1 (hAQ huA)) hu4
  have hact : ∀ δ ∈ D, δ * u * δ⁻¹ = u ∨ δ * u * δ⁻¹ = (u : G)⁻¹ := by
    intro δ hδ
    have hmem : δ * (u : G) * δ⁻¹ ∈ A := by
      have := conj_mem_conjSub (n := δ) huA
      rwa [hAinv δ (Subgroup.mem_sup_left hδ)] at this
    exact eq_or_eq_inv_of_orderOf_four hu4 (hAz _ hmem) (by rw [orderOf_conj_mul_inv_eq, hu4])
  have hcen : ∀ δ, GoodInv H t δ → δ * u * δ⁻¹ = (u : G) → False := by
    intro δ hg h
    apply hnH
    apply hg.cent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rcases hact d₁ hd₁D with h1 | h1
  · exact hcen d₁ g₁ h1
  rcases hact d₂ hd₂D with h2 | h2
  · exact hcen d₂ g₂ h2
  refine hcen (d₁ * d₂) g₃ ?_
  have e : d₁ * d₂ * (u : G) * (d₁ * d₂)⁻¹ = d₁ * (d₂ * u * d₂⁻¹) * d₁⁻¹ := by group
  rw [e, h2]
  have : d₁ * (u : G)⁻¹ * d₁⁻¹ = (d₁ * u * d₁⁻¹)⁻¹ := by group
  rw [this, h1, inv_inv]

theorem endgame_all [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} (hp : p ≠ 2)
    (hΩ : HypOmegaMod p f Ω) {H : Subgroup G} {t : G} {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (ht : IsUniqueInvolution K₁ t) (hbad : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (n₁ : conjSub d₁ K₁ = K₁) (n₂ : conjSub d₂ K₁ = K₁) : False :=
  E187C.endgame_all_of (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ) hK₁ ht hbad g₁ g₂ g₃ hc n₁ n₂

end CFSG.ClassicalInvolution.Asc77
