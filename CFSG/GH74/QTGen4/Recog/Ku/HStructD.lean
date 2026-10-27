module

public import CFSG.GH74.QTGen4.Recog.Ku.Hyp

public section

namespace CFSG.GH74.QTGen4.Ku

theorem kuPerm_card_fin3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem kuMulZMod2_card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem kuPerm_pow_six : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide

theorem kuPerm_sq_of_two_pow {σ : Equiv.Perm (Fin 3)} {k : ℕ} (hk : σ ^ (2 ^ k) = 1) :
    σ ^ 2 = 1 := by
  have hd6 : orderOf σ ∣ 6 := orderOf_dvd_of_pow_eq_one (kuPerm_pow_six σ)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hj] at hd6
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · have h2 := pow_dvd_pow 2 (show j ≤ 1 by omega)
    simpa using h2
  · exfalso
    have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 hj2).trans hd6
    norm_num at h4

set_option maxRecDepth 10000 in
theorem kuPerm_eq_one_of_conj_sq : ∀ σ : Equiv.Perm (Fin 3), σ ^ 2 = 1 →
    (∀ τ : Equiv.Perm (Fin 3), (σ * (τ * σ * τ⁻¹)) ^ 2 = 1) → σ = 1 := by
  decide

@[expose] def kuKer {G : Type} [Group G] {H : Subgroup G}
    (φ : ↥H →* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) : Subgroup ↥H :=
  ((MonoidHom.fst (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).ker).comap φ

theorem card_kuKer {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : Nat.card H = 384)
    {φ : ↥H →* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)} (hφs : Function.Surjective φ) :
    Nat.card (kuKer φ) = 64 := by
  have hidx : (MonoidHom.fst (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).ker.index = 6 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr Prod.fst_surjective,
      Nat.card_congr Subgroup.topEquiv.toEquiv, kuPerm_card_fin3]
  have hidx' : (kuKer φ).index = 6 := by
    unfold kuKer
    rw [Subgroup.index_comap_of_surjective _ hφs]
    exact hidx
  have h1 := Subgroup.index_mul_card (H := kuKer φ)
  rw [hidx', hH] at h1
  omega

namespace KuHyp

variable {G : Type} [Group G] {T M H P : Subgroup G} {z : G}

theorem card_H_aux (h : KuHyp G T M H P z) : Nat.card H = 384 := by
  obtain ⟨φ, hφs, hker⟩ := h.hQuot
  have hq : Nat.card (↥H ⧸ φ.ker) = 12 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      Nat.card_prod, kuPerm_card_fin3, kuMulZMod2_card]
  have hP := h.pExtra.2.1
  have hk : Nat.card φ.ker = 32 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.pH).toEquiv]
    norm_num [hP]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hq, hk]

theorem card_pCore_H_aux [Finite G] (h : KuHyp G T M H P z) :
    Nat.card (CFSG.Open.pCoreOf 2 H) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, -⟩ := h.hQuot
  let π : Equiv.Perm (Fin 3) × Multiplicative (ZMod 2) →* Equiv.Perm (Fin 3) :=
    MonoidHom.fst (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))
  have hK : Nat.card (kuKer φ) = 64 := card_kuKer h.card_H_aux hφs
  have hKn : (kuKer φ).Normal := by
    unfold kuKer
    infer_instance
  have hKp : IsPGroup 2 (kuKer φ) := IsPGroup.iff_card.mpr ⟨6, by rw [hK]; norm_num⟩
  have hKle : kuKer φ ≤ CFSG.Open.pCore 2 H :=
    CFSG.LieType.BorelTits.le_pCore 2 hKn hKp
  have hN : (CFSG.Open.pCore 2 H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hG : ∀ x ∈ CFSG.Open.pCore 2 H, π (φ x) ^ 2 = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2) ⟨x, hx⟩
    have hak : x ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h1 : φ x ^ (2 ^ k) = 1 := by rw [← map_pow φ x, hak, map_one]
    have h3 : π (φ x) ^ (2 ^ k) = 1 := by rw [← map_pow π (φ x), h1, map_one]
    exact kuPerm_sq_of_two_pow h3
  have hpK : CFSG.Open.pCore 2 H ≤ kuKer φ := by
    intro a ha
    have hσ : π (φ a) ^ 2 = 1 := hG a ha
    have hall : ∀ τ : Equiv.Perm (Fin 3), (π (φ a) * (τ * π (φ a) * τ⁻¹)) ^ 2 = 1 := by
      intro τ
      obtain ⟨k, hk⟩ := hφs (τ, 1)
      have hkτ : π (φ k) = τ := by rw [hk]; rfl
      have hkinv : π (φ k⁻¹) = τ⁻¹ := by
        have h : φ k * φ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        have h' := congrArg π h
        rw [map_mul, map_one, hkτ] at h'
        exact eq_inv_of_mul_eq_one_right h'
      have hb : k * a * k⁻¹ ∈ CFSG.Open.pCore 2 H := hN.conj_mem a ha k
      have hab : a * (k * a * k⁻¹) ∈ CFSG.Open.pCore 2 H :=
        (CFSG.Open.pCore 2 H).mul_mem ha hb
      have h1 := hG _ hab
      have e : π (φ (a * (k * a * k⁻¹))) = π (φ a) * (τ * π (φ a) * τ⁻¹) := by
        simp only [map_mul, hkτ, hkinv]
      rw [e] at h1
      exact h1
    have hid : π (φ a) = 1 := kuPerm_eq_one_of_conj_sq (π (φ a)) hσ hall
    unfold kuKer
    exact Subgroup.mem_comap.mpr (MonoidHom.mem_ker.mpr hid)
  have hEq : CFSG.Open.pCore 2 H = kuKer φ := le_antisymm hpK hKle
  have hcard : Nat.card (CFSG.Open.pCoreOf 2 H) = Nat.card (CFSG.Open.pCore 2 H) :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective (CFSG.Open.pCore 2 H) H.subtype Subtype.val_injective).toEquiv).symm
  rw [hcard, hEq, hK]

end KuHyp

end CFSG.GH74.QTGen4.Ku
