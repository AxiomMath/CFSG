module

public import CFSG.LocalAnalysis.Mason73.L4Inverted
public import CFSG.LocalAnalysis.Mason73.L4SelfCentralizing
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem factorization_two_card_of_l4Sylow (hn : 2 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) :
    (Nat.card G).factorization 2 = 3 * n + 1 := by
  obtain ⟨e⟩ := hP
  have h := P.card_eq_multiplicity
  rw [Nat.card_congr e.toEquiv, card_L4Model hn] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem exists_injective_of_isPGroup_of_l4Sylow (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) {H : Subgroup G} (hH : IsPGroup 2 H) :
    ∃ ι : H →* L4Model n, Function.Injective ι := by
  obtain ⟨e⟩ := hP
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  refine ⟨(e.toMonoidHom.comp (Sylow.equiv Q P).toMonoidHom).comp (Subgroup.inclusion hQ), ?_⟩
  exact e.injective.comp ((Sylow.equiv Q P).injective.comp (Subgroup.inclusion_injective hQ))

theorem false_of_mul_self_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (U : Subgroup G)
    (hU2 : ∀ x ∈ U, x * x = 1) (hU : Nat.card U = 2 ^ 5) : False := by
  have hpg : IsPGroup 2 U := IsPGroup.of_card hU
  obtain ⟨ι, hι⟩ := exists_injective_of_isPGroup_of_l4Sylow P hP hpg
  have h16 := card_le_sixteen_of_mul_self hn ι.range (by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hU2 x x.2), map_one])
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hι, Subgroup.card_top, hU] at h16
  norm_num at h16

theorem false_of_inverted_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) {R S : G} {k j : ℕ}
    (hR : orderOf R = 2 ^ k) (hS : orderOf S = 2 ^ j) (hSR : S * R * S⁻¹ = R⁻¹) (hk : n < k) :
    False := by
  set H : Subgroup G := Subgroup.zpowers S ⊔ Subgroup.zpowers R
  have hRp : IsPGroup 2 (Subgroup.zpowers R) := IsPGroup.of_card (by rw [Nat.card_zpowers, hR])
  have hSp : IsPGroup 2 (Subgroup.zpowers S) := IsPGroup.of_card (by rw [Nat.card_zpowers, hS])
  have hSR' : S⁻¹ * R * S = R⁻¹ := by
    have h1 : R = S⁻¹ * R⁻¹ * S := by
      rw [← hSR]
      group
    calc S⁻¹ * R * S = (S⁻¹ * R⁻¹ * S)⁻¹ := by group
      _ = R⁻¹ := by rw [← h1]
  have hconj' : ∀ m : ℤ, S⁻¹ * R ^ m * S = R ^ (-m) := by
    intro m
    have := map_zpow (MulAut.conj S⁻¹) R m
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hSR', inv_zpow']
  have hnorm : Subgroup.zpowers S ≤ Subgroup.normalizer (Subgroup.zpowers R : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      refine Subgroup.mem_zpowers_iff.2 ⟨-m, ?_⟩
      rw [← inv_zpow', ← hSR, conj_zpow]
    · rintro ⟨m, hm⟩
      refine Subgroup.mem_zpowers_iff.2 ⟨-m, ?_⟩
      rw [← hconj' m, show R ^ m = S * x * S⁻¹ from hm]
      group
  have hH : IsPGroup 2 H := IsPGroup.to_sup_of_normal_right' hSp hRp hnorm
  obtain ⟨ι, hι⟩ := exists_injective_of_isPGroup_of_l4Sylow P hP hH
  have hRH : R ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers R)
  have hSH : S ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers S)
  have hconj : ι ⟨S, hSH⟩ * ι ⟨R, hRH⟩ * (ι ⟨S, hSH⟩)⁻¹ = (ι ⟨R, hRH⟩)⁻¹ := by
    have h' : (⟨S, hSH⟩ : H) * ⟨R, hRH⟩ * (⟨S, hSH⟩ : H)⁻¹ = (⟨R, hRH⟩ : H)⁻¹ := Subtype.ext hSR
    simpa only [map_mul, map_inv] using congrArg ι h'
  have hpow := pow_two_pow_eq_one_of_conj_eq_inv hn hconj
  have hord : orderOf (ι ⟨R, hRH⟩) = 2 ^ k := by
    rw [orderOf_injective ι hι, Subgroup.orderOf_mk, hR]
  have hdvd : 2 ^ k ∣ 2 ^ n := hord ▸ orderOf_dvd_of_pow_eq_one hpow
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hdvd
  omega

theorem false_of_injective_zmod_four_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n))
    (φ : Multiplicative (Fin 4 → ZMod 4) →* G) (hφ : Function.Injective φ) : False := by
  have hpg : IsPGroup 2 φ.range := by
    refine IsPGroup.of_card (n := 8) ?_
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφ, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    norm_num
  obtain ⟨ι, hι⟩ := exists_injective_of_isPGroup_of_l4Sylow P hP hpg
  exact not_injective_zmod_four_pow hn (ι.comp φ.rangeRestrict)
    (hι.comp (MonoidHom.rangeRestrict_injective_iff.2 hφ))

variable {M : Type} [Group M]

theorem false_of_elementary_abelian_of_l4Sylow_of_mulEquiv (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (e : G ≃* M) (U : Subgroup M)
    [CFSG.IsElementaryAbelian 2 U] (hU : Nat.card U = 2 ^ 5) : False := by
  refine false_of_mul_self_of_l4Sylow hn P hP (U.map e.symm.toMonoidHom) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, show x * x = 1 by
      rw [← pow_two]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hU]

theorem false_of_inverted_of_l4Sylow_of_mulEquiv (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (e : G ≃* M) {R S : M} {k j : ℕ}
    (hR : orderOf R = 2 ^ k) (hS : orderOf S = 2 ^ j) (hSR : S * R * S⁻¹ = R⁻¹) (hk : n < k) :
    False :=
  false_of_inverted_of_l4Sylow hn P hP (R := e.symm R) (S := e.symm S)
    (by rw [MulEquiv.orderOf_eq, hR]) (by rw [MulEquiv.orderOf_eq, hS])
    (by simpa only [map_mul, map_inv] using congrArg e.symm hSR) hk

theorem false_of_injective_zmod_four_of_l4Sylow_of_mulEquiv (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (e : G ≃* M)
    (φ : Multiplicative (Fin 4 → ZMod 4) →* M) (hφ : Function.Injective φ) : False :=
  false_of_injective_zmod_four_of_l4Sylow hn P hP (e.symm.toMonoidHom.comp φ)
    (e.symm.injective.comp hφ)

end CFSG.LocalAnalysis.Mason73
