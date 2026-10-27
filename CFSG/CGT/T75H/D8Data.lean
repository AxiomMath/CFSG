module

public import CFSG.CGT.T75H.Sylow
public import CFSG.CGT.Timmesfeld75.Sec68Basic

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem inv_mul_mem_of_not_mem_of_relIndex {K L : Subgroup G} (hrel : L.relIndex K = 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (haL : a ∉ L) (hbL : b ∉ L) : a⁻¹ * b ∈ L := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K) hrel
    (a := (⟨a, ha⟩ : K)⁻¹) (b := ⟨b, hb⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haL hbL)
  exact Subgroup.mem_subgroupOf.1 key

theorem eq_of_card_four {K L : Subgroup G} (hLK : L ≤ K) (hL : Nat.card L = 2)
    (hK : Nat.card K = 4) {a b : G} (hL' : ∀ t ∈ L, t = 1 ∨ t = a) (hb : b ∈ K) (hbL : b ∉ L) :
    ∀ t ∈ K, t = 1 ∨ t = a ∨ t = b ∨ t = b * a := by
  have hrel : L.relIndex K = 2 := by
    have h1 := Subgroup.card_mul_index (L.subgroupOf K)
    have h2 : Nat.card (L.subgroupOf K) = Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv
    rw [h2, hL, hK] at h1
    unfold Subgroup.relIndex
    omega
  intro t ht
  by_cases htL : t ∈ L
  · rcases hL' t htL with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have := inv_mul_mem_of_not_mem_of_relIndex hrel hb ht hbL htL
    rcases hL' _ this with h | h
    · right; right; left
      exact (inv_mul_eq_one.1 h).symm
    · right; right; right
      rw [← h]
      group

structure D8Data (T T₁ : Subgroup G) (ℓ a b y : G) : Prop where
  sec3 : Sec3 T T₁
  hℓ : ℓ ∈ normIn T₁ T
  hℓ1 : ℓ ≠ 1
  ha : a ∈ normIn T T₁
  ha1 : a ≠ 1
  hb : b ∈ T
  hbL : b ∉ normIn T T₁
  hy : y ∈ T₁
  hyL : y ∉ normIn T₁ T
  hL : ∀ t ∈ normIn T T₁, t = 1 ∨ t = a
  hL₁ : ∀ t ∈ normIn T₁ T, t = 1 ∨ t = ℓ
  hT : ∀ t ∈ T, t = 1 ∨ t = a ∨ t = b ∨ t = b * a
  hT₁ : ∀ t ∈ T₁, t = 1 ∨ t = ℓ ∨ t = y ∨ t = y * ℓ

theorem exists_d8Data [Finite G] (hc : Sec6Ctx T T₁ 2 1) :
    ∃ ℓ a b y : G, D8Data T T₁ ℓ a b y := by
  have hS3 := hc.sec3
  have hP := hc.hy.pair
  have hT4 : Nat.card T = 4 := by simpa using hc.hT
  obtain ⟨ℓ, hℓ, hℓ1⟩ : ∃ ℓ ∈ normIn T₁ T, ℓ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hS3.cfg.ne₁ (eq_bot_iff.2 (fun y hy => Subgroup.mem_bot.2 (hcon y hy)))
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ normIn T T₁, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hS3.cfg.ne (eq_bot_iff.2 (fun y hy => Subgroup.mem_bot.2 (hcon y hy)))
  have hL : ∀ t ∈ normIn T T₁, t = 1 ∨ t = a := fun t ht => by
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    · exact Or.inr (eq_of_card_two (card_normIn_two hc) ht ha ht1 ha1)
  have hL₁ : ∀ t ∈ normIn T₁ T, t = 1 ∨ t = ℓ := fun t ht => by
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    · exact Or.inr (eq_of_card_two (card_normIn_swap_two hc) ht hℓ ht1 hℓ1)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (hS3.cfg.normIn_lt hP.conj)
  have hcT₁ : ∃ x : G, T = conjSubgroup x T₁ := by
    obtain ⟨x, hx⟩ := hP.conj
    refine ⟨x⁻¹, ?_⟩
    rw [hx, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  obtain ⟨y, hy, hyL⟩ := IsConcreteLE.exists_of_lt (hS3.cfg.symm.normIn_lt hcT₁)
  have hT₁4 : Nat.card T₁ = 4 := by
    obtain ⟨x, hx⟩ := hP.conj
    rw [hx, card_conjSubgroup, hT4]
  exact ⟨ℓ, a, b, y, ⟨hS3, hℓ, hℓ1, ha, ha1, hb, hbL, hy, hyL, hL, hL₁,
    eq_of_card_four (normIn_le T T₁) (card_normIn_two hc) hT4 hL hb hbL,
    eq_of_card_four (normIn_le T₁ T) (card_normIn_swap_two hc) hT₁4 hL₁ hy hyL⟩⟩

namespace D8Data

variable {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)

include D

theorem hℓN : ℓ ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 D.hℓ).2

theorem hℓT₁ : ℓ ∈ T₁ := (mem_normIn.1 D.hℓ).1

theorem haT : a ∈ T := (mem_normIn.1 D.ha).1

theorem haN : a ∈ Subgroup.normalizer (T₁ : Set G) := (mem_normIn.1 D.ha).2

theorem ℓℓ : ℓ * ℓ = 1 := elemAbelian_mul_self D.sec3.cfg.wc₁.1 D.hℓT₁

theorem aa : a * a = 1 := elemAbelian_mul_self D.sec3.cfg.wc.1 D.haT

theorem bb : b * b = 1 := elemAbelian_mul_self D.sec3.cfg.wc.1 D.hb

theorem yy : y * y = 1 := elemAbelian_mul_self D.sec3.cfg.wc₁.1 D.hy

theorem inv_ℓ : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right D.ℓℓ

theorem inv_a : a⁻¹ = a := inv_eq_of_mul_eq_one_right D.aa

theorem inv_b : b⁻¹ = b := inv_eq_of_mul_eq_one_right D.bb

theorem inv_y : y⁻¹ = y := inv_eq_of_mul_eq_one_right D.yy

theorem comm_aℓ : a * ℓ = ℓ * a := D.sec3.cfg.comm_L_L₁ D.ha D.hℓ

theorem ℓ_not_mem : ℓ ∉ T := fun h => by
  have h' : ℓ ∈ T ⊓ T₁ := ⟨h, D.hℓT₁⟩
  rw [D.sec3.cfg.inf, Subgroup.mem_bot] at h'
  exact D.hℓ1 h'

theorem cent_ℓ {t : G} (ht : t ∈ T) (hc : t * ℓ = ℓ * t) : t = 1 ∨ t = a := by
  have h : t ∈ T ⊓ Subgroup.centralizer ({ℓ} : Set G) :=
    ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  rw [D.sec3.cfg.inf_centralizer_eq_normIn D.hℓ D.hℓ1] at h
  exact D.hL t h

theorem cent_a {x : G} (hx : x ∈ T₁) (hc : x * a = a * x) : x = 1 ∨ x = ℓ := by
  have h : x ∈ T₁ ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  rw [D.sec3.cfg.symm.inf_centralizer_eq_normIn D.ha D.ha1] at h
  exact D.hL₁ x h

theorem invol_class {z : G} (hz : z ∈ sStar T T₁) (hzz : z * z = 1) (hzT : z ∉ T) :
    z = ℓ ∨ z = ℓ * a := by
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨u, hu, t, ht, rfl⟩ := exists_mul_of_mem_sup_normIn hL₁N hz
  rcases D.hL₁ u hu with hu1 | hu1 <;> rw [hu1] at hzz hzT ⊢
  · exact absurd (by simpa using ht) hzT
  · have htt : t * t = 1 := elemAbelian_mul_self D.sec3.cfg.wc.1 ht
    have h1 : ℓ * t = (ℓ * t)⁻¹ := eq_inv_of_mul_eq_one_left hzz
    have h2 : (ℓ * t)⁻¹ = t * ℓ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right htt, D.inv_ℓ]
    rw [h2] at h1
    rcases D.cent_ℓ ht h1.symm with rfl | rfl
    · left; simp
    · right; rfl

theorem conj_ℓ_b : b * ℓ * b = ℓ * a := by
  have hbS : b ∈ sStar T T₁ := le_sStar_left D.hb
  have hℓS : ℓ ∈ sStar T T₁ := normIn_le_sStar D.hℓ
  have hw : b * ℓ * b ∈ sStar T T₁ :=
    (sStar T T₁).mul_mem ((sStar T T₁).mul_mem hbS hℓS) hbS
  have hww : (b * ℓ * b) * (b * ℓ * b) = 1 := by
    calc (b * ℓ * b) * (b * ℓ * b) = b * ℓ * (b * b) * ℓ * b := by group
      _ = b * (ℓ * ℓ) * b := by rw [D.bb]; group
      _ = 1 := by rw [D.ℓℓ, mul_one, D.bb]
  have hwT : b * ℓ * b ∉ T := fun h => by
    have : ℓ ∈ T := by
      have e : ℓ = b⁻¹ * (b * ℓ * b) * b⁻¹ := by group
      rw [e]
      exact T.mul_mem (T.mul_mem (T.inv_mem D.hb) h) (T.inv_mem D.hb)
    exact D.ℓ_not_mem this
  rcases D.invol_class hw hww hwT with h | h
  · exfalso
    apply D.hbL
    have hbc : b * ℓ = ℓ * b := by
      have : b * ℓ * b = ℓ := h
      calc b * ℓ = b * ℓ * b * b⁻¹ := by group
        _ = ℓ * b⁻¹ := by rw [this]
        _ = ℓ * b := by rw [D.inv_b]
    rcases D.cent_ℓ D.hb hbc with h1 | h1
    · rw [h1]; exact (normIn T T₁).one_mem
    · rw [h1]; exact D.ha
  · exact h

theorem conj_b_ℓ : ℓ * b * ℓ = b * a := by
  have hv : ℓ * b * ℓ⁻¹ ∈ T := conj_mem_of_mem_normalizer D.hℓN D.hb
  rw [D.inv_ℓ] at hv
  rcases D.hT _ hv with h | h | h | h
  · exfalso
    apply D.hbL
    have : b = 1 := by
      calc b = ℓ * (ℓ * b * ℓ) * ℓ := by
            rw [← mul_assoc, ← mul_assoc, D.ℓℓ, one_mul, mul_assoc, D.ℓℓ, mul_one]
        _ = 1 := by rw [h]; simp [D.ℓℓ]
    rw [this]; exact (normIn T T₁).one_mem
  · exfalso
    apply D.hbL
    have haℓ : ℓ * a = a * ℓ := D.comm_aℓ.symm
    have : b = a := by
      calc b = ℓ * (ℓ * b * ℓ) * ℓ := by
            rw [← mul_assoc, ← mul_assoc, D.ℓℓ, one_mul, mul_assoc, D.ℓℓ, mul_one]
        _ = ℓ * a * ℓ := by rw [h]
        _ = a * (ℓ * ℓ) := by rw [haℓ]; group
        _ = a := by rw [D.ℓℓ, mul_one]
    rw [this]; exact D.ha
  · exfalso
    apply D.hbL
    have hbc : b * ℓ = ℓ * b := by
      calc b * ℓ = ℓ * (ℓ * b * ℓ) := by
            rw [← mul_assoc, ← mul_assoc, D.ℓℓ, one_mul]
        _ = ℓ * b := by rw [h]
    rcases D.cent_ℓ D.hb hbc with h1 | h1
    · rw [h1]; exact (normIn T T₁).one_mem
    · rw [h1]; exact D.ha
  · exact h

theorem conj_a_y : a * y * a = y * ℓ := by
  have hv : a * y * a⁻¹ ∈ T₁ := conj_mem_of_mem_normalizer D.haN D.hy
  rw [D.inv_a] at hv
  rcases D.hT₁ _ hv with h | h | h | h
  · exfalso
    apply D.hyL
    have : y = 1 := by
      calc y = a * (a * y * a) * a := by
            rw [← mul_assoc, ← mul_assoc, D.aa, one_mul, mul_assoc, D.aa, mul_one]
        _ = 1 := by rw [h]; simp [D.aa]
    rw [this]; exact (normIn T₁ T).one_mem
  · exfalso
    apply D.hyL
    have hℓa : a * ℓ = ℓ * a := D.comm_aℓ
    have : y = ℓ := by
      calc y = a * (a * y * a) * a := by
            rw [← mul_assoc, ← mul_assoc, D.aa, one_mul, mul_assoc, D.aa, mul_one]
        _ = a * ℓ * a := by rw [h]
        _ = ℓ * (a * a) := by rw [hℓa]; group
        _ = ℓ := by rw [D.aa, mul_one]
    rw [this]; exact D.hℓ
  · exfalso
    apply D.hyL
    have hyc : y * a = a * y := by
      calc y * a = a * (a * y * a) := by
            rw [← mul_assoc, ← mul_assoc, D.aa, one_mul]
        _ = a * y := by rw [h]
    rcases D.cent_a D.hy hyc with h1 | h1
    · rw [h1]; exact (normIn T₁ T).one_mem
    · rw [h1]; exact D.hℓ
  · exact h

end D8Data

end CFSG.CGT.T75H
