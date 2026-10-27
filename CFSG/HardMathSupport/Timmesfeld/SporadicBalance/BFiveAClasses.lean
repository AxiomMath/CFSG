module

public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

@[expose] def BFiveTwoBCover : Prop :=
  ∀ s : B, orderOf s = 5 → ∃ t : B, BabyInv 1 t ∧ t ∈ Subgroup.centralizer ({s} : Set B)

section Lift

variable {H K : Type*} [Group H] [Group K]

theorem exists_conj_eq_of_map_eq [Finite H] {p : ℕ} (hp : p.Prime) (F : H →* K)
    (hN : ¬ p ∣ Nat.card F.ker) {y₁ y₂ : H} (h₁ : orderOf y₁ = p) (h₂ : orderOf y₂ = p)
    (h : F y₁ = F y₂) : ∃ g : H, g * y₂ * g⁻¹ = y₁ := by
  have : Fact p.Prime := ⟨hp⟩
  set L : Subgroup H := (Subgroup.zpowers (F y₁)).comap F with hL
  have hy1L : y₁ ∈ L := Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)
  have hy2L : y₂ ∈ L := Subgroup.mem_comap.2 (h ▸ Subgroup.mem_zpowers _)
  set FL : ↥L →* K := F.comp L.subtype with hFL
  have hkerdvd : Nat.card FL.ker ∣ Nat.card F.ker := by
    rw [hFL, ← MonoidHom.comap_ker]
    exact Subgroup.card_comap_dvd_of_injective _ _ L.subtype_injective
  have hker : ¬ p ∣ Nat.card FL.ker := fun hd => hN (hd.trans hkerdvd)
  have hrange : FL.range ≤ Subgroup.zpowers (F y₁) := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hFy : orderOf (F y₁) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ← h₁, pow_orderOf_eq_one, map_one]
  have hrdvd : Nat.card FL.range ∣ p := by
    have := Subgroup.card_dvd_of_le hrange
    rw [Nat.card_zpowers] at this
    exact this.trans hFy
  have hcardL := Subgroup.card_ker_mul_card_range FL
  have hpL : p ∣ Nat.card ↥L := by
    have := orderOf_dvd_natCard (⟨y₁, hy1L⟩ : ↥L)
    rwa [Subgroup.orderOf_mk, h₁] at this
  have hfac : (Nat.card ↥L).factorization p = 1 := by
    have ha0 : Nat.card FL.ker ≠ 0 := Nat.card_pos.ne'
    rcases (Nat.dvd_prime hp).1 hrdvd with hb | hb
    · rw [← hcardL, hb, mul_one] at hpL
      exact absurd hpL hker
    · rw [← hcardL, hb, Nat.factorization_mul ha0 hp.ne_zero, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hker, hp.factorization_self, zero_add]
  set S₁ : Subgroup ↥L := Subgroup.zpowers ⟨y₁, hy1L⟩ with hS₁def
  set S₂ : Subgroup ↥L := Subgroup.zpowers ⟨y₂, hy2L⟩ with hS₂def
  have hS₁ : Nat.card S₁ = p ^ (Nat.card ↥L).factorization p := by
    rw [hfac, pow_one, hS₁def, Nat.card_zpowers, Subgroup.orderOf_mk, h₁]
  have hS₂ : Nat.card S₂ = p ^ (Nat.card ↥L).factorization p := by
    rw [hfac, pow_one, hS₂def, Nat.card_zpowers, Subgroup.orderOf_mk, h₂]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L (Sylow.ofCard S₂ hS₂) (Sylow.ofCard S₁ hS₁)
  have hmem : ∀ y : ↥L, g * y * g⁻¹ ∈ S₁ ↔ y ∈ S₂ := by
    intro y
    have e : S₁ = ((g • Sylow.ofCard S₂ hS₂ : Sylow p ↥L) : Subgroup ↥L) := by
      rw [hg]
      rfl
    rw [e, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv]
    have e2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e2]
    rfl
  have h2 : g * ⟨y₂, hy2L⟩ * g⁻¹ ∈ S₁ := (hmem _).2 (Subgroup.mem_zpowers _)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h2
  have hj' : y₁ ^ j = (g : H) * y₂ * (g : H)⁻¹ := by
    have := congrArg Subtype.val hj
    simpa using this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show F g ∈ Subgroup.zpowers (F y₁) from g.2)
  have hFj : F (y₁ ^ j) = F y₁ := by
    have hc : Commute (F y₁ ^ k) (F y₁) := (Commute.refl (F y₁)).zpow_left k
    rw [hj', map_mul, map_mul, map_inv, ← h]
    change F (L.subtype g) * F y₁ * (F (L.subtype g))⁻¹ = F y₁
    rw [show F (L.subtype g) = F y₁ ^ k from hk.symm, hc.eq, mul_inv_cancel_right]
  have he : y₁ ^ j * y₁⁻¹ ∈ F.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hFj, mul_inv_cancel]
  have hep : (y₁ ^ j * y₁⁻¹) ^ p = 1 := by
    rw [← zpow_sub_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h₁,
      pow_orderOf_eq_one, one_zpow]
  have he1 : y₁ ^ j * y₁⁻¹ = 1 := by
    by_contra hne
    have ho : orderOf (y₁ ^ j * y₁⁻¹) = p := orderOf_eq_prime hep hne
    have hd := orderOf_dvd_natCard (⟨_, he⟩ : ↥F.ker)
    rw [Subgroup.orderOf_mk, ho] at hd
    exact hN hd
  exact ⟨g, by rw [← hj']; exact mul_inv_eq_one.1 he1⟩

theorem exists_conj_eq_of_map_conj [Finite H] {p : ℕ} (hp : p.Prime) (F : H →* K)
    (hF : Function.Surjective F) (hN : ¬ p ∣ Nat.card F.ker) {y₁ y₂ : H}
    (h₁ : orderOf y₁ = p) (h₂ : orderOf y₂ = p) {k : K} (h : k * F y₂ * k⁻¹ = F y₁) :
    ∃ g : H, g * y₂ * g⁻¹ = y₁ := by
  obtain ⟨c, hc⟩ := hF k
  have h₂' : orderOf (c * y₂ * c⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h₂]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_map_eq hp F hN h₁ h₂'
    (by rw [map_mul, map_mul, map_inv, hc, h])
  exact ⟨g * c, by rw [← hg]; group⟩

end Lift

theorem exists_conj_pow_of_conj_pow {M : Type*} [Group M] {L σ τ g₁ g₂ : M}
    (hL : orderOf L = 5) {a b : ℕ} (ha : ¬ 5 ∣ a) (hb : ¬ 5 ∣ b) (h₁ : g₁ * σ * g₁⁻¹ = L ^ a)
    (h₂ : g₂ * τ * g₂⁻¹ = L ^ b) : ∃ c : ℕ, ¬ 5 ∣ c ∧ ∃ k : M, k * τ ^ c * k⁻¹ = σ := by
  refine ⟨a * b ^ 3, ?_, g₁⁻¹ * g₂, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_five).1 hd with hd' | hd'
    · exact ha hd'
    · exact hb (Nat.prime_five.dvd_of_dvd_pow hd')
  · have e1 : g₂ * τ ^ (a * b ^ 3) * g₂⁻¹ = L ^ (b * (a * b ^ 3)) := by
      rw [← conj_pow, h₂, ← pow_mul]
    have e2 : L ^ (b * (a * b ^ 3)) = L ^ a := by
      rw [pow_eq_pow_iff_modEq, hL]
      have hr : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have hr0 : b % 5 ≠ 0 := fun h0 => hb (Nat.dvd_of_mod_eq_zero h0)
      have ha5 : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
      show (b * (a * b ^ 3)) % 5 = a % 5
      rw [Nat.mul_mod, Nat.mul_mod a, Nat.pow_mod]
      interval_cases (b % 5) <;> interval_cases (a % 5) <;> simp_all
    calc (g₁⁻¹ * g₂) * τ ^ (a * b ^ 3) * (g₁⁻¹ * g₂)⁻¹
        = g₁⁻¹ * (g₂ * τ ^ (a * b ^ 3) * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * L ^ a * g₁ := by rw [e1, e2]
      _ = σ := by rw [← h₁]; group

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
