module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Sylow

import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace GL83.I243.Inner

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let f : H × K →* G :=
    MonoidHom.noncommCoprod H.subtype K.subtype (fun h k => hHK h h.2 k k.2)
  have hr : f.range = H ⊔ K :=
    (MonoidHom.noncommCoprod_range _ _ _).trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  rw [← hr] at hx
  obtain ⟨⟨h, k⟩, rfl⟩ := hx
  exact ⟨h, h.2, k, k.2, rfl⟩

theorem mul_comm_of_mem_sup {B C : Subgroup G} (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    {x y : G} (hx : x ∈ B ⊔ C) (hy : y ∈ B ⊔ C) : x * y = y * x := by
  obtain ⟨b₁, hb₁, c₁, hc₁, rfl⟩ := exists_mul_of_mem_sup hBC hx
  obtain ⟨b₂, hb₂, c₂, hc₂, rfl⟩ := exists_mul_of_mem_sup hBC hy
  have hb₁b₂ : Commute b₁ b₂ := hB b₁ hb₁ b₂ hb₂
  have hb₁c₂ : Commute b₁ c₂ := hBC b₁ hb₁ c₂ hc₂
  have hc₁b₂ : Commute c₁ b₂ := (hBC b₂ hb₂ c₁ hc₁).symm
  have hc₁c₂ : Commute c₁ c₂ := hC c₁ hc₁ c₂ hc₂
  exact (Commute.mul_left (hb₁b₂.mul_right hb₁c₂) (hc₁b₂.mul_right hc₁c₂)).eq

theorem card_sup_mul_card_inf {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  let f : H × K →* G :=
    MonoidHom.noncommCoprod H.subtype K.subtype (fun h k => hHK h h.2 k k.2)
  have hr : f.range = H ⊔ K :=
    (MonoidHom.noncommCoprod_range _ _ _).trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ K) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun y => ⟨(⟨⟨y, y.2.1⟩, ⟨(y : G)⁻¹, K.inv_mem y.2.2⟩⟩ : H × K), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : (x.1.1 : G) * (x.1.2 : G) = 1 := x.2
      have : (x.1.1 : G) = (x.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left hx
      rw [this]
      exact K.inv_mem x.1.2.2
    · show (y : G) * (y : G)⁻¹ = 1
      exact mul_inv_cancel _
    · rintro ⟨⟨h, k⟩, hk⟩
      have hx : (h : G) * (k : G) = 1 := hk
      have h1 : (h : G) = (k : G)⁻¹ := eq_inv_of_mul_eq_one_left hx
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        show (h : G)⁻¹ = (k : G)
        rw [h1, inv_inv]
    · intro y
      rfl
  have h := Subgroup.card_ker_mul_card_range f
  rw [Nat.card_prod, hr, hker] at h
  rw [mul_comm]
  exact h

theorem le_sup_of_card_le [Finite G] {p : ℕ} (hp : 0 < p) {T B C : Subgroup G}
    (hTC : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t) (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hBle : B ≤ T ⊔ C) (hT : Nat.card T ≤ p ^ 3) (hB : p ^ 3 ≤ Nat.card B)
    (hTinf : p ≤ Nat.card ↥(T ⊓ C)) (hBinf : Nat.card ↥(B ⊓ C) ≤ p) : T ≤ B ⊔ C := by
  have h1 := card_sup_mul_card_inf hBC
  have h2 := card_sup_mul_card_inf hTC
  have hcard : Nat.card ↥(T ⊔ C) ≤ Nat.card ↥(B ⊔ C) := by
    refine Nat.le_of_mul_le_mul_right ?_ hp
    calc Nat.card ↥(T ⊔ C) * p ≤ Nat.card ↥(T ⊔ C) * Nat.card ↥(T ⊓ C) :=
          Nat.mul_le_mul_left _ hTinf
      _ = Nat.card T * Nat.card C := h2
      _ ≤ p ^ 3 * Nat.card C := Nat.mul_le_mul_right _ hT
      _ ≤ Nat.card B * Nat.card C := Nat.mul_le_mul_right _ hB
      _ = Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C) := h1.symm
      _ ≤ Nat.card ↥(B ⊔ C) * p := Nat.mul_le_mul_left _ hBinf
  exact le_sup_left.trans (Subgroup.eq_of_le_of_card_ge (sup_le hBle le_sup_right) hcard).ge

theorem exists_zpow_mul_zpow (x : G) {m n : ℕ} (h : Nat.Coprime m n) :
    ∃ a b : ℤ, x = (x ^ m) ^ a * (x ^ n) ^ b := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  refine ⟨a, b, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
  have : (m : ℤ) * a + (n : ℤ) * b = 1 := by linarith
  rw [this, zpow_one]

theorem exists_pow_mem_sylow_of_mem_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    ∃ n : ℕ, ¬ p ∣ n ∧ g ^ n ∈ (P : Subgroup G) := by
  have : (P.subtype Subgroup.le_normalizer).Normal := Subgroup.normal_in_normalizer
  refine ⟨((P.subtype Subgroup.le_normalizer : Sylow p _) :
      Subgroup (Subgroup.normalizer (P : Set G))).index,
    (P.subtype Subgroup.le_normalizer).not_dvd_index, ?_⟩
  have h := Subgroup.pow_index_mem
    ((P.subtype Subgroup.le_normalizer : Sylow p _) : Subgroup (Subgroup.normalizer (P : Set G)))
    (⟨g, hg⟩ : Subgroup.normalizer (P : Set G))
  rw [Sylow.coe_subtype] at h
  simpa [Subgroup.mem_subgroupOf] using h

theorem exists_pow_mem_of_sylow_map [Finite G] {p : ℕ} [Fact p.Prime] {K T : Subgroup G}
    (P : Sylow p K) (hP : (P : Subgroup K).map K.subtype = T) {k : G} (hk : k ∈ K)
    (hnorm : ∀ y ∈ K, y ∈ T ↔ k * y * k⁻¹ ∈ T) :
    ∃ n : ℕ, ¬ p ∣ n ∧ k ^ n ∈ T := by
  have hmem : ∀ h : K, h ∈ (P : Subgroup K) ↔ (h : G) ∈ T := by
    intro h
    rw [← hP]
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hg : (⟨k, hk⟩ : K) ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmem, hmem]
    exact hnorm h h.2
  obtain ⟨n, hn, hpow⟩ := exists_pow_mem_sylow_of_mem_normalizer P hg
  refine ⟨n, hn, ?_⟩
  have := (hmem _).mp hpow
  simpa using this

theorem card_le_of_sylow_map [Finite G] {p : ℕ} [Fact p.Prime] {K T : Subgroup G}
    (P : Sylow p K) (hP : (P : Subgroup K).map K.subtype = T) (hK4 : ¬ p ^ 4 ∣ Nat.card K) :
    Nat.card T ≤ p ^ 3 := by
  have hp := (Fact.out : p.Prime)
  rw [← hP, Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity]
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card K).factorization p ≤ 3 := by
    by_contra h
    push Not at h
    exact hK4 ((hp.pow_dvd_iff_le_factorization hK0).mpr h)
  exact Nat.pow_le_pow_right hp.pos h3

end GL83.I243.Inner
