module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Three
public import CFSG.GroupTheory.TwoWeightCard

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GroupTheory.TwoWeights

theorem data_of_mem {G : Type*} [Group G] (N : Subgroup G) {a u₁ u₂ u₃ x y : G}
    (D : Data a u₁ u₂ u₃ x y) (ha : a ∈ N) (h₁ : u₁ ∈ N) (h₂ : u₂ ∈ N) (h₃ : u₃ ∈ N)
    (hx : x ∈ N) (hy : y ∈ N) :
    Data (⟨a, ha⟩ : N) ⟨u₁, h₁⟩ ⟨u₂, h₂⟩ ⟨u₃, h₃⟩ ⟨x, hx⟩ ⟨y, hy⟩ :=
  ⟨Subtype.ext (by simpa using D.a_a), Subtype.ext (by simpa using D.u₁_u₁),
    Subtype.ext (by simpa using D.u₂_u₂), Subtype.ext (by simpa using D.u₃_u₃),
    Subtype.ext (by simpa using D.u₁_u₂), Subtype.ext (by simpa using D.u₁_u₃),
    Subtype.ext (by simpa using D.u₁_a), Subtype.ext (by simpa using D.u₂_u₃),
    Subtype.ext (by simpa using D.u₂_a), Subtype.ext (by simpa using D.u₃_a),
    Subtype.ext (by simpa using D.a_x), Subtype.ext (by simpa using D.a_y),
    Subtype.ext (by simpa using D.x_u₁), Subtype.ext (by simpa using D.x_u₂),
    Subtype.ext (by simpa using D.x_u₃), Subtype.ext (by simpa using D.xi_u₁),
    Subtype.ext (by simpa using D.xi_u₂), Subtype.ext (by simpa using D.xi_u₃),
    Subtype.ext (by simpa using D.y_u₁), Subtype.ext (by simpa using D.y_u₂),
    Subtype.ext (by simpa using D.y_u₃), Subtype.ext (by simpa using D.yi_u₁),
    Subtype.ext (by simpa using D.yi_u₂), Subtype.ext (by simpa using D.yi_u₃),
    Subtype.ext (by simpa using D.xx), Subtype.ext (by simpa using D.yy),
    Subtype.ext (by simpa using D.xy4)⟩

theorem isSylowOf_top_of_card {X : Type*} [Group X] [Finite X] {T₀ : Subgroup X}
    (hT₀ : IsPGroup 2 ↥T₀) {k : ℕ} (hk : 2 ^ k ≤ Nat.card T₀)
    (hX2 : ¬ 2 ^ (k + 1) ∣ Nat.card X) : IsSylowOf 2 T₀ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hT₀
  have hdvd : 2 ^ j ∣ Nat.card X := by
    rw [← hj]
    exact Subgroup.card_subgroup_dvd_card T₀
  have hXpos : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hjv : j ≤ (Nat.card X).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hXpos).1 hdvd
  have hkj : k ≤ j := by
    rw [hj] at hk
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hk
  have hvk : (Nat.card X).factorization 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    exact hX2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hXpos).2 (by omega))
  refine isSylowOf_of_card le_top ?_
  rw [hj, show Nat.card (⊤ : Subgroup X) = Nat.card X from Nat.card_congr Subgroup.topEquiv.toEquiv,
    show j = (Nat.card X).factorization 2 by omega]

theorem threeCfg_top_of_syl8 {Y : Type} [Group Y] [Finite Y] {G : Type*} [Group G] [Finite G]
    (Θ : G ≃* MulAut Y) {T W : Subgroup (MulAut Y)} (hcfg : SylCfg Y T W) {k : ℕ}
    (hk : Nat.card ↥T = 2 ^ k) (hG2 : ¬ 2 ^ (k + 1) ∣ Nat.card G) : ThreeCfg (⊤ : Subgroup G) := by
  have : Finite (MulAut Y) := finite_mulAut' Y
  have hcardA : Nat.card (MulAut Y) = Nat.card G := (Nat.card_congr Θ.toEquiv).symm
  have hsyl : IsSylowOf 2 T ⊤ :=
    isSylowOf_top_of_card hcfg.t2 (le_of_eq hk.symm) (by rw [hcardA]; exact hG2)
  have h1 : ThreeCfg (⊤ : Subgroup (MulAut Y)) :=
    ⟨T, W, hsyl, hcfg.w3, hcfg.w_ne, hcfg.t_norm⟩
  have h2 := threeCfg_map Θ.symm h1
  rwa [Subgroup.map_top_of_surjective _ Θ.symm.surjective] at h2

theorem card_eq_two_pow {X : Type*} [Group X] [Finite X] {T₀ : Subgroup X}
    (hT₀ : IsPGroup 2 ↥T₀) {k : ℕ} (hk : 2 ^ k ≤ Nat.card T₀)
    (hX2 : ¬ 2 ^ (k + 1) ∣ Nat.card X) : Nat.card T₀ = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hT₀
  have hdvd : 2 ^ j ∣ Nat.card X := by
    rw [← hj]
    exact Subgroup.card_subgroup_dvd_card T₀
  have hkj : k ≤ j := by
    rw [hj] at hk
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hk
  have hjk : j ≤ k := by
    by_contra hlt
    push Not at hlt
    exact hX2 ((Nat.pow_dvd_pow 2 hlt).trans hdvd)
  rw [hj, le_antisymm hjk hkj]

theorem not_threeCfg_of_data {X : Type*} [Group X] [Finite X] {τ u₁ u₂ u₃ x y : X}
    (D : Data τ u₁ u₂ u₃ x y) {T₀ : Subgroup X} (hT₀ : IsPGroup 2 ↥T₀)
    (hτc : ∀ t ∈ T₀, t * τ = τ * t) (hτ : τ ∈ T₀) (hu₁ : u₁ ∈ T₀) (hu₂ : u₂ ∈ T₀)
    (hu₃ : u₃ ∈ T₀) (hx : x ∈ T₀) (hy : y ∈ T₀) {k : ℕ} (hk : 2 ^ k ≤ Nat.card T₀)
    (hX2 : ¬ 2 ^ (k + 1) ∣ Nat.card X) (h3 : ¬ 3 ^ 8 ∣ Nat.card X)
    (hA : ∀ E : Subgroup X, IsPGroup 3 ↥E → E ≠ ⊥ → E ≤ centralizer ({τ} : Set X) →
      ¬ T₀ ≤ normalizer (E : Set X)) :
    ¬ ThreeCfg (⊤ : Subgroup X) := by
  rintro ⟨P, W, hP, hW3, hWne, hPW⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : IsSylowOf 2 T₀ ⊤ := isSylowOf_top_of_card hT₀ hk hX2
  obtain ⟨κ, -, hκ⟩ := hS.exists_mem_conj hP
  set c : X →* X := (MulAut.conj κ).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj κ).injective
  set W' : Subgroup X := W.comap c with hW'
  have hW'3 : IsPGroup 3 ↥W' := by
    refine IsPGroup.comap_of_ker_isPGroup hW3 c ?_
    rw [(MonoidHom.ker_eq_bot_iff c).2 hcinj]
    exact IsPGroup.of_card (by simp : Nat.card ↥(⊥ : Subgroup X) = 3 ^ 0)
  have hmemc : ∀ z, z ∈ W' ↔ κ * z * κ⁻¹ ∈ W := fun z => by
    simp [hW', hc, MulAut.conj_apply]
  have hW'ne : W' ≠ ⊥ := by
    intro hb
    apply hWne
    rw [eq_bot_iff]
    intro w hw
    have hw' : κ⁻¹ * w * κ ∈ W' := by
      rw [hmemc]
      have : κ * (κ⁻¹ * w * κ) * κ⁻¹ = w := by group
      rw [this]
      exact hw
    rw [hb, Subgroup.mem_bot] at hw'
    have h2 : w = κ * (κ⁻¹ * w * κ) * κ⁻¹ := by group
    rw [h2, hw']
    simp
  have hT₀W' : T₀ ≤ normalizer (W' : Set X) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hp : κ * t * κ⁻¹ ∈ P := by
      rw [hκ]
      have : κ⁻¹ * (κ * t * κ⁻¹) * κ = t := by group
      rw [this]
      exact ht
    have h1 := Subgroup.mem_normalizer_iff.mp (hPW hp) (κ * z * κ⁻¹)
    rw [hmemc, hmemc]
    have e : κ * (t * z * t⁻¹) * κ⁻¹ =
        (κ * t * κ⁻¹) * (κ * z * κ⁻¹) * (κ * t * κ⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  by_cases hC : W' ⊓ centralizer ({τ} : Set X) = ⊥
  · exact h3 (star_core D hu₁ hu₂ hu₃ hτ hx hy hW'3 hW'ne hT₀W' hC)
  · refine hA (W' ⊓ centralizer ({τ} : Set X)) (hW'3.to_inf_left) hC inf_le_right ?_
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hn := Subgroup.mem_normalizer_iff.mp (hT₀W' ht) z
    have hcen : ∀ z', z' ∈ centralizer ({τ} : Set X) ↔
        t * z' * t⁻¹ ∈ centralizer ({τ} : Set X) := by
      intro z'
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      have ht' := hτc t ht
      constructor
      · intro h
        calc t * z' * t⁻¹ * τ = t * z' * (t⁻¹ * τ) := by group
          _ = t * z' * (τ * t⁻¹) := by
            congr 1
            calc t⁻¹ * τ = t⁻¹ * (τ * t) * t⁻¹ := by group
              _ = t⁻¹ * (t * τ) * t⁻¹ := by rw [ht']
              _ = τ * t⁻¹ := by group
          _ = t * (z' * τ) * t⁻¹ := by group
          _ = t * (τ * z') * t⁻¹ := by rw [h]
          _ = τ * (t * z' * t⁻¹) := by
            calc t * (τ * z') * t⁻¹ = (t * τ) * z' * t⁻¹ := by group
              _ = (τ * t) * z' * t⁻¹ := by rw [ht']
              _ = τ * (t * z' * t⁻¹) := by group
      · intro h
        have h2 : z' = t⁻¹ * (t * z' * t⁻¹) * t := by group
        have h3 : τ = t⁻¹ * τ * t := by
          calc τ = t⁻¹ * (t * τ) := by group
            _ = t⁻¹ * (τ * t) := by rw [ht']
            _ = t⁻¹ * τ * t := by group
        calc z' * τ = (t⁻¹ * (t * z' * t⁻¹) * t) * (t⁻¹ * τ * t) := by rw [← h2, ← h3]
          _ = t⁻¹ * ((t * z' * t⁻¹) * τ) * t := by group
          _ = t⁻¹ * (τ * (t * z' * t⁻¹)) * t := by rw [h]
          _ = (t⁻¹ * τ * t) * (t⁻¹ * (t * z' * t⁻¹) * t) := by group
          _ = τ * z' := by rw [← h3, ← h2]
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hn, hcen z]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
