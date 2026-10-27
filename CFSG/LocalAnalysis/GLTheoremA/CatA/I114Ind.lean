module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Cent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

@[expose] def Cent (L : Subgroup Y) (g : Y) : Prop := ∀ l ∈ L, l * g = g * l

theorem cent_mul {L : Subgroup Y} {g h : Y} (hg : Cent L g) (hh : Cent L h) :
    Cent L (g * h) := by
  intro l hl
  rw [← mul_assoc, hg l hl, mul_assoc, hh l hl, ← mul_assoc]

theorem cent_inv {L : Subgroup Y} {g : Y} (hg : Cent L g) : Cent L g⁻¹ := by
  intro l hl
  have h1 := hg l hl
  calc l * g⁻¹ = g⁻¹ * (g * l) * g⁻¹ := by group
    _ = g⁻¹ * (l * g) * g⁻¹ := by rw [h1]
    _ = g⁻¹ * l := by group

theorem cent_of_elemCommute {A C : Subgroup Y} (h : ElemCommute A C) {c : Y} (hc : c ∈ C) :
    Cent A c :=
  fun a ha => h a ha c hc

theorem cent_of_le {L L' : Subgroup Y} (h : L ≤ L') {g : Y} (hg : Cent L' g) : Cent L g :=
  fun l hl => hg l (h hl)

theorem zpow_eq_one_of_cent {y : Y} (hy : orderOf y = 3) (L : Subgroup Y)
    (hnc : ∃ z ∈ L, z * y ≠ y * z) {i : ℤ} (hi : Cent L (y ^ i)) : y ^ i = 1 := by
  obtain ⟨q, hq⟩ := three_dvd_of_centralizes hy L hnc i hi
  have h3 : y ^ (3 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa using h
  rw [hq, zpow_mul, h3, one_zpow]

theorem orderOf_conj3 {y : Y} (hy : orderOf y = 3) (g : Y) : orderOf (g * y * g⁻¹) = 3 := by
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have h3 : (g * y * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow]
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    rw [h]
    group
  have hne : g * y * g⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this, h]
    group
  exact orderOf_eq_prime h3 hne

theorem conj_mem_cj {K : Subgroup Y} {y : Y} (g : Y) (hy : y ∈ K) : g * y * g⁻¹ ∈ cj g K := by
  rw [mem_cj]
  have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rw [e]
  exact hy

theorem noncentral_conj {K : Subgroup Y} {y : Y} (g : Y) (hnc : ∃ z ∈ K, z * y ≠ y * z) :
    ∃ z ∈ cj g K, z * (g * y * g⁻¹) ≠ (g * y * g⁻¹) * z := by
  obtain ⟨z₀, hz₀K, hz₀⟩ := hnc
  refine ⟨g * z₀ * g⁻¹, conj_mem_cj g hz₀K, fun h => hz₀ ?_⟩
  calc z₀ * y = g⁻¹ * (g * z₀ * g⁻¹ * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹ * (g * z₀ * g⁻¹)) * g := by rw [h]
    _ = y * z₀ := by group

theorem commute_K₂_K₃ {K : Subgroup Y} {x : Y} (hKK₂ : ElemCommute K (cj x K)) :
    ElemCommute (cj x K) (cj (x * x) K) := by
  have h := commutes_cj x hKK₂
  rwa [← cj_mul] at h

theorem E_eq_one {K : Subgroup Y} {x y : Y} (hyK : y ∈ K) (hKK₂ : ElemCommute K (cj x K))
    (hKK₃ : ElemCommute K (cj (x * x) K)) (hy3 : orderOf y = 3) (hnc : ∃ z ∈ K, z * y ≠ y * z)
    (hy₁3 : orderOf (x * y * x⁻¹) = 3)
    (hnc₁ : ∃ z ∈ cj x K, z * (x * y * x⁻¹) ≠ (x * y * x⁻¹) * z)
    (hy₂3 : orderOf ((x * x) * y * (x * x)⁻¹) = 3)
    (hnc₂ : ∃ z ∈ cj (x * x) K, z * ((x * x) * y * (x * x)⁻¹) ≠ ((x * x) * y * (x * x)⁻¹) * z)
    {g : Y}
    (hgE : g ∈ Subgroup.zpowers y ⊔ (Subgroup.zpowers (x * y * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)))
    (hgK : Cent K g) (hgK₂ : Cent (cj x K) g) (hgK₃ : Cent (cj (x * x) K) g) : g = 1 := by
  have hy₁K : x * y * x⁻¹ ∈ cj x K := conj_mem_cj x hyK
  have hy₂K : (x * x) * y * (x * x)⁻¹ ∈ cj (x * x) K := conj_mem_cj (x * x) hyK
  have f23 : ElemCommute (cj x K) (cj (x * x) K) := commute_K₂_K₃ hKK₂
  have fK : ElemCommute K (cj x K ⊔ cj (x * x) K) := commutes_sup_right hKK₂ hKK₃
  have hzz : ElemCommute (Subgroup.zpowers (x * y * x⁻¹))
      (Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) :=
    fun a ha c hc => f23 a (Subgroup.zpowers_le.2 hy₁K ha) c (Subgroup.zpowers_le.2 hy₂K hc)
  have hMs : Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹) ≤
      cj x K ⊔ cj (x * x) K :=
    sup_le_sup (Subgroup.zpowers_le.2 hy₁K) (Subgroup.zpowers_le.2 hy₂K)
  have hzM : ElemCommute (Subgroup.zpowers y)
      (Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) :=
    fun a ha c hc => fK a (Subgroup.zpowers_le.2 hyK ha) c (hMs hc)
  obtain ⟨a, ha, m, hm, hgam⟩ := mem_sup_of_commutes hzM g hgE
  have hmK : Cent K m := cent_of_elemCommute fK (hMs hm)
  have haK : Cent K a := by
    have e : a = g * m⁻¹ := by rw [hgam]; group
    rw [e]
    exact cent_mul hgK (cent_inv hmK)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ha
  have ha1 : a = 1 := by
    rw [← hi] at haK ⊢
    exact zpow_eq_one_of_cent hy3 K hnc haK
  rw [ha1, one_mul] at hgam
  have hmK₂ : Cent (cj x K) m := by rw [← hgam]; exact hgK₂
  have hmK₃ : Cent (cj (x * x) K) m := by rw [← hgam]; exact hgK₃
  obtain ⟨b, hb, c, hc, hmbc⟩ := mem_sup_of_commutes hzz m hm
  have hcK₂ : Cent (cj x K) c := cent_of_elemCommute f23 (Subgroup.zpowers_le.2 hy₂K hc)
  have hbK₂ : Cent (cj x K) b := by
    have e : b = m * c⁻¹ := by rw [hmbc]; group
    rw [e]
    exact cent_mul hmK₂ (cent_inv hcK₂)
  have hb1 : b = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← hj] at hbK₂ ⊢
    exact zpow_eq_one_of_cent hy₁3 (cj x K) hnc₁ hbK₂
  rw [hb1, one_mul] at hmbc
  have hcK₃ : Cent (cj (x * x) K) c := by rw [← hmbc]; exact hmK₃
  have hc1 : c = 1 := by
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [← hl] at hcK₃ ⊢
    exact zpow_eq_one_of_cent hy₂3 (cj (x * x) K) hnc₂ hcK₃
  rw [hgam, hmbc, hc1]

theorem ms_data {K : Subgroup Y} {x y : Y} (hyK : y ∈ K) (hKK₂ : ElemCommute K (cj x K))
    (hKK₃ : ElemCommute K (cj (x * x) K)) :
    ElemCommute (Subgroup.zpowers (x * y * x⁻¹)) (Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) ∧
    ElemCommute (Subgroup.zpowers y)
      (Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) := by
  have hy₁K : x * y * x⁻¹ ∈ cj x K := conj_mem_cj x hyK
  have hy₂K : (x * x) * y * (x * x)⁻¹ ∈ cj (x * x) K := conj_mem_cj (x * x) hyK
  have f23 : ElemCommute (cj x K) (cj (x * x) K) := commute_K₂_K₃ hKK₂
  have fK : ElemCommute K (cj x K ⊔ cj (x * x) K) := commutes_sup_right hKK₂ hKK₃
  have hMs : Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹) ≤
      cj x K ⊔ cj (x * x) K :=
    sup_le_sup (Subgroup.zpowers_le.2 hy₁K) (Subgroup.zpowers_le.2 hy₂K)
  refine ⟨fun a ha c hc => f23 a (Subgroup.zpowers_le.2 hy₁K ha) c (Subgroup.zpowers_le.2 hy₂K hc),
    fun a ha c hc => fK a (Subgroup.zpowers_le.2 hyK ha) c (hMs hc)⟩

theorem card_ms_eq [Finite Y] {K : Subgroup Y} {x y : Y} (hKK₂ : ElemCommute K (cj x K))
    (hKK₃ : ElemCommute K (cj (x * x) K)) (hy₁3 : orderOf (x * y * x⁻¹) = 3)
    (hnc₁ : ∃ z ∈ cj x K, z * (x * y * x⁻¹) ≠ (x * y * x⁻¹) * z)
    (hy₂3 : orderOf ((x * x) * y * (x * x)⁻¹) = 3)
    (hy : y ∈ K) :
    Nat.card ↥(Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) = 9 := by
  have hyK := hy
  obtain ⟨hzz, -⟩ := ms_data hyK hKK₂ hKK₃
  have hy₁K : x * y * x⁻¹ ∈ cj x K := conj_mem_cj x hyK
  have hy₂K : (x * x) * y * (x * x)⁻¹ ∈ cj (x * x) K := conj_mem_cj (x * x) hyK
  have f23 : ElemCommute (cj x K) (cj (x * x) K) := commute_K₂_K₃ hKK₂
  have hinter : Subgroup.zpowers (x * y * x⁻¹) ⊓ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgA, hgC⟩ := hg
    have hcC : Cent (cj x K) g := cent_of_elemCommute f23 (Subgroup.zpowers_le.2 hy₂K hgC)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgA
    rw [Subgroup.mem_bot, ← hj]
    rw [← hj] at hcC
    exact zpow_eq_one_of_cent hy₁3 (cj x K) hnc₁ hcC
  have h1 := card_sup_mul_card_inf_of_le_normalizer (A := Subgroup.zpowers (x * y * x⁻¹))
    (B := Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) (commutes_normalizer hzz)
  rw [hinter, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hy₁3, hy₂3] at h1
  omega

theorem card_E_eq [Finite Y] {K : Subgroup Y} {x y : Y} (hyK : y ∈ K)
    (hKK₂ : ElemCommute K (cj x K)) (hKK₃ : ElemCommute K (cj (x * x) K))
    (hy3 : orderOf y = 3) (hnc : ∃ z ∈ K, z * y ≠ y * z)
    (hy₁3 : orderOf (x * y * x⁻¹) = 3)
    (hnc₁ : ∃ z ∈ cj x K, z * (x * y * x⁻¹) ≠ (x * y * x⁻¹) * z)
    (hy₂3 : orderOf ((x * x) * y * (x * x)⁻¹) = 3)
    (hnc₂ : ∃ z ∈ cj (x * x) K, z * ((x * x) * y * (x * x)⁻¹) ≠ ((x * x) * y * (x * x)⁻¹) * z) :
    Nat.card ↥(Subgroup.zpowers y ⊔ (Subgroup.zpowers (x * y * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y * (x * x)⁻¹))) = 27 := by
  obtain ⟨-, hzM⟩ := ms_data hyK hKK₂ hKK₃
  have hMs : Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹) ≤
      cj x K ⊔ cj (x * x) K :=
    sup_le_sup (Subgroup.zpowers_le.2 (conj_mem_cj x hyK)) (Subgroup.zpowers_le.2 (conj_mem_cj (x * x) hyK))
  have fK : ElemCommute K (cj x K ⊔ cj (x * x) K) := commutes_sup_right hKK₂ hKK₃
  have hinter : Subgroup.zpowers y ⊓ (Subgroup.zpowers (x * y * x⁻¹) ⊔
      Subgroup.zpowers ((x * x) * y * (x * x)⁻¹)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgA, hgC⟩ := hg
    have hcK : Cent K g := cent_of_elemCommute fK (hMs hgC)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgA
    rw [Subgroup.mem_bot, ← hj]
    rw [← hj] at hcK
    exact zpow_eq_one_of_cent hy3 K hnc hcK
  have h1 := card_sup_mul_card_inf_of_le_normalizer (A := Subgroup.zpowers y)
    (B := Subgroup.zpowers (x * y * x⁻¹) ⊔ Subgroup.zpowers ((x * x) * y * (x * x)⁻¹))
    (commutes_normalizer hzM)
  rw [hinter, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy3,
    card_ms_eq hKK₂ hKK₃ hy₁3 hnc₁ hy₂3 hyK] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.I114
