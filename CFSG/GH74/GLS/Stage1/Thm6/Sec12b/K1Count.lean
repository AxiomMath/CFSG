module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Dihedral
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_8Aux

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G]

theorem card_le_ncard_mul_of_conj_mem [Finite G] (H : Subgroup G) (w : G) (X : Set G)
    (hX : ∀ h ∈ H, h * w * h⁻¹ ∈ X) :
    Nat.card H ≤ X.ncard * Nat.card (H ⊓ Subgroup.centralizer {w} : Subgroup G) := by
  have h := ncard_conj_mul_card_inf_centralizer H w
  have hsub : {y | ∃ n ∈ H, n * w * n⁻¹ = y} ⊆ X := by
    rintro y ⟨n, hn, rfl⟩
    exact hX n hn
  have hle := Set.ncard_le_ncard hsub (Set.toFinite X)
  calc Nat.card H = _ := h.symm
    _ ≤ X.ncard * Nat.card (H ⊓ Subgroup.centralizer {w} : Subgroup G) :=
      Nat.mul_le_mul_right _ hle

theorem ncard_sdiff_pair_le [Finite G] {B : Subgroup G} {z : G} (hB : Nat.card B ≤ 4)
    (hzB : z ∈ B) (hz1 : z ≠ 1) : ((B : Set G) \ {1, z}).ncard ≤ 2 := by
  have hsub : ({1, z} : Set G) ⊆ (B : Set G) := by
    intro e he
    rcases he with rfl | rfl
    · exact B.one_mem
    · exact hzB
  have hc : (B : Set G).ncard = Nat.card B := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [Set.ncard_sdiff hsub, Set.ncard_pair hz1.symm, hc]
  omega

theorem card_le_two_mul_of_conj_mem [Finite G] (H : Subgroup G) (w : G) {B : Subgroup G} {z : G}
    (hB : Nat.card B ≤ 4) (hzB : z ∈ B) (hz1 : z ≠ 1)
    (hX : ∀ h ∈ H, h * w * h⁻¹ ∈ B ∧ h * w * h⁻¹ ≠ 1 ∧ h * w * h⁻¹ ≠ z) :
    Nat.card H ≤ 2 * Nat.card (H ⊓ Subgroup.centralizer {w} : Subgroup G) := by
  have h1 := card_le_ncard_mul_of_conj_mem H w ((B : Set G) \ {1, z}) (by
    intro h hh
    obtain ⟨hb, h1, hz⟩ := hX h hh
    refine ⟨hb, ?_⟩
    rintro (e | e)
    · exact h1 e
    · exact hz e)
  exact h1.trans (Nat.mul_le_mul_right _ (ncard_sdiff_pair_le hB hzB hz1))

theorem Hconj_centralizer_sub (g : G) (H : Subgroup G) :
    Hconj g (Subgroup.centralizer (H : Set G)) = Subgroup.centralizer (Hconj g H : Set G) := by
  ext a
  simp only [mem_Hconj, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h b hb
    have h1 := h _ hb
    have h2 : g * (b * a) * g⁻¹ = g * (a * b) * g⁻¹ := by
      calc g * (b * a) * g⁻¹ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (g * b * g⁻¹) := h1
        _ = g * (a * b) * g⁻¹ := by group
    exact conj_inj g h2
  · intro h b hb
    have hb' : g * (g⁻¹ * b * g) * g⁻¹ ∈ H := by
      have : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [this]; exact hb
    have h1 := h _ hb'
    calc b * (g * a * g⁻¹) = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by rw [h1]
      _ = (g * a * g⁻¹) * b := by group

theorem Hconj_normalizer_le (g : G) (H : Subgroup G) :
    Hconj g (Subgroup.normalizer (H : Set G)) ≤ Subgroup.normalizer (Hconj g H : Set G) := by
  intro a ha
  rw [mem_Hconj, Subgroup.mem_normalizer_iff] at ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  simp only [mem_Hconj]
  have e : g * (a * b * a⁻¹) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
  rw [e]
  exact ha (g * b * g⁻¹)

theorem Hconj_normalizer (g : G) (H : Subgroup G) :
    Hconj g (Subgroup.normalizer (H : Set G)) = Subgroup.normalizer (Hconj g H : Set G) := by
  apply le_antisymm (Hconj_normalizer_le g H)
  have h1 := Hconj_normalizer_le g⁻¹ (Hconj g H)
  rw [Hconj_inv_Hconj] at h1
  have h2 := Hconj_le_Hconj (g := g) h1
  rwa [Hconj_Hconj_inv] at h2

theorem Hconj_self_of_mem {T : Subgroup G} {t : G} (ht : t ∈ T) : Hconj t T = T := by
  ext a
  rw [mem_Hconj]
  constructor
  · intro h
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) h) ht
    simpa [mul_assoc] using this
  · intro h
    exact T.mul_mem (T.mul_mem ht h) (T.inv_mem ht)

theorem DihData.card_inf_centralizer_refl_le [Finite G] {D : Subgroup G} {ρ s : G} {j : ℕ}
    (h : DihData D ρ s j) (i : ℤ) :
    Nat.card (D ⊓ Subgroup.centralizer {s * ρ ^ i} : Subgroup G) ≤ 4 := by
  classical
  have hsub : ((D ⊓ Subgroup.centralizer {s * ρ ^ i} : Subgroup G) : Set G) ⊆
      (({1, ρ ^ DihData.zc j, s * ρ ^ i, s * ρ ^ i * ρ ^ DihData.zc j} : Finset G) : Set G) := by
    rintro g ⟨hgD, hgc⟩
    have hgd : g * (s * ρ ^ i) = (s * ρ ^ i) * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
    obtain ⟨k, rfl | rfl⟩ := h.elem g hgD
    · have e1 : ρ ^ k * (s * ρ ^ i) = s * ρ ^ (i - k) := by
        rw [← mul_assoc, h.zpow_s, mul_assoc, ← zpow_add]
        congr 2
        ring
      have e2 : s * ρ ^ i * ρ ^ k = s * ρ ^ (i + k) := by
        rw [mul_assoc, ← zpow_add]
      rw [e1, e2] at hgd
      have e3 : ρ ^ (i - k) = ρ ^ (i + k) := mul_left_cancel hgd
      rw [h.zpow_eq_iff] at e3
      have hsq : ρ ^ k * ρ ^ k = 1 := by
        rw [← zpow_add, h.zpow_eq_one_iff]
        have e4 : (i - k) - (i + k) = -(k + k) := by ring
        rw [e4] at e3
        exact (dvd_neg).1 e3
      rcases h.zpow_sq_cases k hsq with e | e <;> simp [e]
    · have e1 : s * ρ ^ k * (s * ρ ^ i) = ρ ^ (i - k) := by
        calc s * ρ ^ k * (s * ρ ^ i) = s * (ρ ^ k * s) * ρ ^ i := by simp only [mul_assoc]
          _ = s * (s * ρ ^ (-k)) * ρ ^ i := by rw [h.zpow_s]
          _ = (s * s) * (ρ ^ (-k) * ρ ^ i) := by simp only [mul_assoc]
          _ = ρ ^ (i - k) := by
            rw [h.s_sq, one_mul, ← zpow_add]
            congr 1
            ring
      have e2 : s * ρ ^ i * (s * ρ ^ k) = ρ ^ (k - i) := by
        calc s * ρ ^ i * (s * ρ ^ k) = s * (ρ ^ i * s) * ρ ^ k := by simp only [mul_assoc]
          _ = s * (s * ρ ^ (-i)) * ρ ^ k := by rw [h.zpow_s]
          _ = (s * s) * (ρ ^ (-i) * ρ ^ k) := by simp only [mul_assoc]
          _ = ρ ^ (k - i) := by
            rw [h.s_sq, one_mul, ← zpow_add]
            congr 1
            ring
      rw [e1, e2, h.zpow_eq_iff] at hgd
      have hsq : ρ ^ (k - i) * ρ ^ (k - i) = 1 := by
        rw [← zpow_add, h.zpow_eq_one_iff]
        have e4 : (i - k) - (k - i) = -((k - i) + (k - i)) := by ring
        rw [e4] at hgd
        exact (dvd_neg).1 hgd
      have hg : s * ρ ^ k = s * ρ ^ i * ρ ^ (k - i) := by
        rw [mul_assoc, ← zpow_add]
        congr 2
        ring
      rcases h.zpow_sq_cases (k - i) hsq with e | e
      · rw [hg, e, mul_one]; simp
      · rw [hg, e]; simp
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : Nat.card (D ⊓ Subgroup.centralizer {s * ρ ^ i} : Subgroup G) =
      ((D ⊓ Subgroup.centralizer {s * ρ ^ i} : Subgroup G) : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  have h4 : ({1, ρ ^ DihData.zc j, s * ρ ^ i, s * ρ ^ i * ρ ^ DihData.zc j} : Finset G).card ≤ 4 :=
    Finset.card_le_four
  omega

theorem card_inf_centralizer_le_of_sup [Finite G] {T D : Subgroup G} {x d : G} (hx2 : x * x = 1)
    (hxc : ∀ t ∈ T, x * t = t * x) (hDT : D ≤ T) (hT : D ⊔ Subgroup.zpowers x = T)
    (hDx : D ⊓ Subgroup.zpowers x = ⊥) (hdT : d ∈ T) :
    Nat.card (T ⊓ Subgroup.centralizer {d} : Subgroup G) ≤
      2 * Nat.card (D ⊓ Subgroup.centralizer {d} : Subgroup G) := by
  have hzc : ∀ b ∈ Subgroup.zpowers x, ∀ t ∈ T, b * t = t * b := by
    intro b hb t ht
    rcases zpowers_sq_cases hx2 hb with rfl | rfl
    · simp
    · exact hxc t ht
  have hc' : ∀ a ∈ D, ∀ b ∈ Subgroup.zpowers x, a * b = b * a :=
    fun a ha b hb => (hzc b hb a (hDT ha)).symm
  have hc : ∀ a ∈ D ⊓ Subgroup.centralizer {d}, ∀ b ∈ Subgroup.zpowers x, a * b = b * a :=
    fun a ha b hb => hc' a ha.1 b hb
  have hle : T ⊓ Subgroup.centralizer {d} ≤
      (D ⊓ Subgroup.centralizer {d}) ⊔ Subgroup.zpowers x := by
    rintro t ⟨htT, htc⟩
    rw [← hT] at htT
    obtain ⟨e, he, b, hb, rfl⟩ := mem_sup_of_commute hc' htT
    have hbc : b * d = d * b := hzc b hb d hdT
    have hec : e * d = d * e := by
      have h1 : (e * b) * d = d * (e * b) := Subgroup.mem_centralizer_singleton_iff.1 htc
      have h2 : (e * d) * b = (d * e) * b := by
        calc (e * d) * b = e * (d * b) := by group
          _ = e * (b * d) := by rw [hbc]
          _ = (e * b) * d := by group
          _ = d * (e * b) := h1
          _ = (d * e) * b := by group
      exact mul_right_cancel h2
    exact Subgroup.mul_mem_sup ⟨he, Subgroup.mem_centralizer_singleton_iff.2 hec⟩ hb
  have hd : (D ⊓ Subgroup.centralizer {d}) ⊓ Subgroup.zpowers x = ⊥ :=
    le_bot_iff.1 (hDx ▸ inf_le_inf_right _ inf_le_left)
  have hx : Nat.card (Subgroup.zpowers x) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hx2)
  calc Nat.card (T ⊓ Subgroup.centralizer {d} : Subgroup G)
      ≤ Nat.card ((D ⊓ Subgroup.centralizer {d}) ⊔ Subgroup.zpowers x : Subgroup G) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card (D ⊓ Subgroup.centralizer {d} : Subgroup G) * Nat.card (Subgroup.zpowers x) :=
        card_sup_of_commute hc hd
    _ ≤ Nat.card (D ⊓ Subgroup.centralizer {d} : Subgroup G) * 2 := Nat.mul_le_mul_left _ hx
    _ = 2 * Nat.card (D ⊓ Subgroup.centralizer {d} : Subgroup G) := by ring

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
