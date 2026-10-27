module

public import CFSG.CGT.T75H.D8Data

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def Cbar (T T₁ S : Subgroup G) : Subgroup G :=
  S ⊓ Subgroup.centralizer ((T ⊔ T₁ : Subgroup G) : Set G)

theorem mem_Cbar_iff {S : Subgroup G} {c : G} :
    c ∈ Cbar T T₁ S ↔ c ∈ S ∧ (∀ t ∈ T, t * c = c * t) ∧ (∀ x ∈ T₁, x * c = c * x) := by
  unfold Cbar
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hS, hC⟩
    rw [Subgroup.mem_centralizer_iff] at hC
    exact ⟨hS, fun t ht => hC t (Subgroup.mem_sup_left ht),
      fun x hx => hC x (Subgroup.mem_sup_right hx)⟩
  · rintro ⟨hS, hT, hT₁⟩
    refine ⟨hS, ?_⟩
    have hle : T ⊔ T₁ ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.2 (hT t ht))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hT₁ x hx))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem sStar_le_sup : sStar T T₁ ≤ T ⊔ T₁ :=
  sup_le le_sup_left ((normIn_le T₁ T).trans le_sup_right)

theorem comm_sStar_Cbar {S : Subgroup G} {d c : G} (hd : d ∈ sStar T T₁)
    (hc : c ∈ Cbar T T₁ S) : d * c = c * d :=
  Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 d (sStar_le_sup hd)

theorem comm_of_conj {c x : G} (h : c * x * c⁻¹ = x) : x * c = c * x := by
  calc x * c = (c * x * c⁻¹) * c := by rw [h]
    _ = c * x := by group

namespace D8Data

variable {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)

include D

theorem comm_ab : a * b = b * a := elemAbelian_mul_comm D.sec3.cfg.wc.1 D.haT D.hb

theorem comm_of_ab {c : G} (ha : a * c = c * a) (hb : b * c = c * b) :
    ∀ t ∈ T, t * c = c * t := by
  intro t ht
  rcases D.hT t ht with rfl | rfl | rfl | rfl
  · simp
  · exact ha
  · exact hb
  · calc b * a * c = b * (a * c) := by group
      _ = b * (c * a) := by rw [ha]
      _ = (b * c) * a := by group
      _ = (c * b) * a := by rw [hb]
      _ = c * (b * a) := by group

theorem comm_of_ℓy {c : G} (hℓ : ℓ * c = c * ℓ) (hy : y * c = c * y) :
    ∀ t ∈ T₁, t * c = c * t := by
  intro t ht
  rcases D.hT₁ t ht with rfl | rfl | rfl | rfl
  · simp
  · exact hℓ
  · exact hy
  · calc y * ℓ * c = y * (ℓ * c) := by group
      _ = y * (c * ℓ) := by rw [hℓ]
      _ = (y * c) * ℓ := by group
      _ = (c * y) * ℓ := by rw [hy]
      _ = c * (y * ℓ) := by group

variable {S : Subgroup G}

theorem stage1 (hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (T : Set G)) (hSS : sStar T T₁ ≤ S)
    (hSnorm : ∀ s ∈ S, ∀ z ∈ sStar T T₁, s * z * s⁻¹ ∈ sStar T T₁) :
    ∀ s ∈ S, ∃ e ∈ sStar T T₁, e⁻¹ * s ∈ S ∧ (e⁻¹ * s) * ℓ = ℓ * (e⁻¹ * s) := by
  intro s hs
  have hz : s * ℓ * s⁻¹ ∈ sStar T T₁ := hSnorm s hs ℓ (normIn_le_sStar D.hℓ)
  have hzz : (s * ℓ * s⁻¹) * (s * ℓ * s⁻¹) = 1 := by
    calc (s * ℓ * s⁻¹) * (s * ℓ * s⁻¹) = s * (ℓ * ℓ) * s⁻¹ := by group
      _ = 1 := by rw [D.ℓℓ]; group
  have hzT : s * ℓ * s⁻¹ ∉ T := fun h => D.ℓ_not_mem (by
    have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem (hSN s hs)) h
    have e : ℓ = s⁻¹ * (s * ℓ * s⁻¹) * s⁻¹⁻¹ := by group
    rw [e]
    exact this)
  rcases D.invol_class hz hzz hzT with h | h
  · refine ⟨1, (sStar T T₁).one_mem, by simpa using hs, ?_⟩
    simp only [inv_one, one_mul]
    calc s * ℓ = (s * ℓ * s⁻¹) * s := by group
      _ = ℓ * s := by rw [h]
  · have hbS : b ∈ sStar T T₁ := le_sStar_left D.hb
    refine ⟨b, hbS, S.mul_mem (S.inv_mem (hSS hbS)) hs, ?_⟩
    have hbℓ : b * ℓ * a = ℓ * b := by
      have h1 : b * ℓ * b = ℓ * a := D.conj_ℓ_b
      calc b * ℓ * a = (b * ℓ * b) * (b⁻¹ * a) := by group
        _ = (ℓ * a) * (b * a) := by rw [h1, D.inv_b]
        _ = ℓ * (a * b) * a := by group
        _ = ℓ * (b * a) * a := by rw [D.comm_ab]
        _ = ℓ * b * (a * a) := by group
        _ = ℓ * b := by rw [D.aa, mul_one]
    calc (b⁻¹ * s) * ℓ = b⁻¹ * (s * ℓ * s⁻¹) * s := by group
      _ = b⁻¹ * (ℓ * a) * s := by rw [h]
      _ = (b * ℓ * a) * s := by rw [D.inv_b]; group
      _ = (ℓ * b) * s := by rw [hbℓ]
      _ = ℓ * (b⁻¹ * s) := by rw [D.inv_b]; group

theorem conj_ℓ_a : ℓ⁻¹ * a * ℓ = a := by
  calc ℓ⁻¹ * a * ℓ = ℓ * a * ℓ := by rw [D.inv_ℓ]
    _ = (a * ℓ) * ℓ := by rw [← D.comm_aℓ]
    _ = a * (ℓ * ℓ) := by group
    _ = a := by rw [D.ℓℓ, mul_one]

theorem stage2 (hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (T : Set G)) (hSS : sStar T T₁ ≤ S) :
    ∀ s ∈ S, s * ℓ = ℓ * s → ∃ e ∈ sStar T T₁, e⁻¹ * s ∈ S ∧ (e⁻¹ * s) * ℓ = ℓ * (e⁻¹ * s) ∧
      ∀ t ∈ T, t * (e⁻¹ * s) = (e⁻¹ * s) * t := by
  intro s hs hsℓ
  have hsN := hSN s hs
  have hsℓ' : s⁻¹ * ℓ = ℓ * s⁻¹ := by
    calc s⁻¹ * ℓ = s⁻¹ * (ℓ * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * ℓ) * s⁻¹ := by rw [hsℓ]
      _ = ℓ * s⁻¹ := by group
  have hsa : s * a * s⁻¹ = a := by
    have hmem : s * a * s⁻¹ ∈ T := conj_mem_of_mem_normalizer hsN D.haT
    have hcomm : (s * a * s⁻¹) * ℓ = ℓ * (s * a * s⁻¹) := by
      calc (s * a * s⁻¹) * ℓ = s * a * (s⁻¹ * ℓ) := by group
        _ = s * a * (ℓ * s⁻¹) := by rw [hsℓ']
        _ = s * (a * ℓ) * s⁻¹ := by group
        _ = s * (ℓ * a) * s⁻¹ := by rw [D.comm_aℓ]
        _ = (s * ℓ) * a * s⁻¹ := by group
        _ = (ℓ * s) * a * s⁻¹ := by rw [hsℓ]
        _ = ℓ * (s * a * s⁻¹) := by group
    rcases D.cent_ℓ hmem hcomm with h | h
    · exfalso
      apply D.ha1
      calc a = s⁻¹ * (s * a * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hsa' : s * a = a * s := by
    calc s * a = (s * a * s⁻¹) * s := by group
      _ = a * s := by rw [hsa]
  have hsa'' : s⁻¹ * a * s = a := by
    calc s⁻¹ * a * s = s⁻¹ * (a * s) := by group
      _ = s⁻¹ * (s * a) := by rw [hsa']
      _ = a := by group
  have hmemb : s * b * s⁻¹ ∈ T := conj_mem_of_mem_normalizer hsN D.hb
  rcases D.hT _ hmemb with h | h | h | h
  · exfalso
    apply D.hbL
    have : b = 1 := by
      calc b = s⁻¹ * (s * b * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    rw [this]; exact (normIn T T₁).one_mem
  · exfalso
    apply D.hbL
    have : b = a := by
      calc b = s⁻¹ * (s * b * s⁻¹) * s := by group
        _ = s⁻¹ * a * s := by rw [h]
        _ = a := hsa''
    rw [this]; exact D.ha
  ·
    refine ⟨1, (sStar T T₁).one_mem, by simpa using hs, by simpa using hsℓ, ?_⟩
    simp only [inv_one, one_mul]
    exact D.comm_of_ab (c := s) hsa'.symm (comm_of_conj h)
  ·
    have hℓS : ℓ ∈ S := hSS (normIn_le_sStar D.hℓ)
    refine ⟨ℓ, normIn_le_sStar D.hℓ, S.mul_mem (S.inv_mem hℓS) hs, ?_, ?_⟩
    · calc (ℓ⁻¹ * s) * ℓ = ℓ⁻¹ * (s * ℓ) := mul_assoc _ _ _
        _ = ℓ⁻¹ * (ℓ * s) := by rw [hsℓ]
        _ = ℓ * (ℓ⁻¹ * s) := by rw [D.inv_ℓ]
    · have hcaℓ : (ℓ⁻¹ * s) * a * (ℓ⁻¹ * s)⁻¹ = a := by
        calc (ℓ⁻¹ * s) * a * (ℓ⁻¹ * s)⁻¹ = ℓ⁻¹ * (s * a * s⁻¹) * ℓ := by group
          _ = ℓ⁻¹ * a * ℓ := by rw [hsa]
          _ = a := D.conj_ℓ_a
      have hcb : (ℓ⁻¹ * s) * b * (ℓ⁻¹ * s)⁻¹ = b := by
        calc (ℓ⁻¹ * s) * b * (ℓ⁻¹ * s)⁻¹ = ℓ⁻¹ * (s * b * s⁻¹) * ℓ := by group
          _ = ℓ⁻¹ * (b * a) * ℓ := by rw [h]
          _ = (ℓ⁻¹ * b * ℓ) * (ℓ⁻¹ * a * ℓ) := by group
          _ = (b * a) * a := by rw [D.conj_ℓ_a, D.inv_ℓ, D.conj_b_ℓ]
          _ = b := by
              calc b * a * a = b * (a * a) := by group
                _ = b := by rw [D.aa, mul_one]
      exact D.comm_of_ab (c := ℓ⁻¹ * s) (comm_of_conj hcaℓ) (comm_of_conj hcb)

theorem stage3 (hSS : sStar T T₁ ≤ S) :
    ∀ s ∈ S, s * ℓ = ℓ * s → (∀ t ∈ T, t * s = s * t) →
      ∃ e ∈ sStar T T₁, e⁻¹ * s ∈ Cbar T T₁ S := by
  intro s hs hsℓ hsT
  have hsℓ' : s⁻¹ * ℓ = ℓ * s⁻¹ := by
    calc s⁻¹ * ℓ = s⁻¹ * (ℓ * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * ℓ) * s⁻¹ := by rw [hsℓ]
      _ = ℓ * s⁻¹ := by group
  have hsℓ'' : s * ℓ * s⁻¹ = ℓ := by
    calc s * ℓ * s⁻¹ = (ℓ * s) * s⁻¹ := by rw [hsℓ]
      _ = ℓ := by group
  have hsN₁ : conjSubgroup s T₁ = T₁ := by
    refine (D.sec3.cfg.wc₁.2 ℓ D.hℓT₁ D.hℓ1).2 s (fun x hx => ?_)
    have hz : s⁻¹ * x * s ∈ T₁ := mem_conjSubgroup.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzℓ : (s⁻¹ * x * s) * ℓ = ℓ * (s⁻¹ * x * s) :=
      elemAbelian_mul_comm D.sec3.cfg.wc₁.1 hz D.hℓT₁
    calc x * ℓ = s * ((s⁻¹ * x * s) * ℓ) * s⁻¹ := by
          calc x * ℓ = s * (s⁻¹ * x * s) * s⁻¹ * ℓ := by group
            _ = s * (s⁻¹ * x * s) * (s⁻¹ * ℓ) := by group
            _ = s * (s⁻¹ * x * s) * (ℓ * s⁻¹) := by rw [hsℓ']
            _ = s * ((s⁻¹ * x * s) * ℓ) * s⁻¹ := by group
      _ = s * (ℓ * (s⁻¹ * x * s)) * s⁻¹ := by rw [hzℓ]
      _ = (s * ℓ) * (s⁻¹ * x * s) * s⁻¹ := by group
      _ = (ℓ * s) * (s⁻¹ * x * s) * s⁻¹ := by rw [hsℓ]
      _ = ℓ * x := by group
  have hmem : s * y * s⁻¹ ∈ T₁ := by
    have : s * y * s⁻¹ ∈ conjSubgroup s T₁ := by
      rw [mem_conjSubgroup]
      have e : s⁻¹ * (s * y * s⁻¹) * s = y := by group
      rw [e]; exact D.hy
    rwa [hsN₁] at this
  rcases D.hT₁ _ hmem with h | h | h | h
  · exfalso
    apply D.hyL
    have : y = 1 := by
      calc y = s⁻¹ * (s * y * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    rw [this]; exact (normIn T₁ T).one_mem
  · exfalso
    apply D.hyL
    have : y = ℓ := by
      calc y = s⁻¹ * (s * y * s⁻¹) * s := by group
        _ = s⁻¹ * ℓ * s := by rw [h]
        _ = ℓ := by
            calc s⁻¹ * ℓ * s = (ℓ * s⁻¹) * s := by rw [hsℓ']
              _ = ℓ := by group
    rw [this]; exact D.hℓ
  ·
    refine ⟨1, (sStar T T₁).one_mem, ?_⟩
    simp only [inv_one, one_mul]
    rw [mem_Cbar_iff]
    exact ⟨hs, hsT, D.comm_of_ℓy (c := s) hsℓ.symm (comm_of_conj h)⟩
  ·
    have haS : a ∈ S := hSS (le_sStar_left D.haT)
    refine ⟨a, le_sStar_left D.haT, ?_⟩
    rw [mem_Cbar_iff]
    refine ⟨S.mul_mem (S.inv_mem haS) hs, fun t ht => ?_, ?_⟩
    · have hat : t * a = a * t := elemAbelian_mul_comm D.sec3.cfg.wc.1 ht D.haT
      calc t * (a⁻¹ * s) = (t * a⁻¹) * s := by group
        _ = (a⁻¹ * t) * s := by rw [D.inv_a, hat]
        _ = a⁻¹ * (t * s) := by group
        _ = a⁻¹ * (s * t) := by rw [hsT t ht]
        _ = (a⁻¹ * s) * t := by group
    · have hcℓ : (a⁻¹ * s) * ℓ * (a⁻¹ * s)⁻¹ = ℓ := by
        calc (a⁻¹ * s) * ℓ * (a⁻¹ * s)⁻¹ = a⁻¹ * (s * ℓ * s⁻¹) * a := by group
          _ = a⁻¹ * ℓ * a := by rw [hsℓ'']
          _ = ℓ := by
              calc a⁻¹ * ℓ * a = a * ℓ * a := by rw [D.inv_a]
                _ = ℓ * a * a := by rw [D.comm_aℓ]
                _ = ℓ * (a * a) := by group
                _ = ℓ := by rw [D.aa, mul_one]
      have hcy : (a⁻¹ * s) * y * (a⁻¹ * s)⁻¹ = y := by
        calc (a⁻¹ * s) * y * (a⁻¹ * s)⁻¹ = a⁻¹ * (s * y * s⁻¹) * a := by group
          _ = a⁻¹ * (y * ℓ) * a := by rw [h]
          _ = (a⁻¹ * y * a) * (a⁻¹ * ℓ * a) := by group
          _ = (y * ℓ) * ℓ := by
              rw [D.inv_a, D.conj_a_y]
              congr 1
              calc a * ℓ * a = ℓ * a * a := by rw [D.comm_aℓ]
                _ = ℓ * (a * a) := by group
                _ = ℓ := by rw [D.aa, mul_one]
          _ = y := by
              calc y * ℓ * ℓ = y * (ℓ * ℓ) := by group
                _ = y := by rw [D.ℓℓ, mul_one]
      exact D.comm_of_ℓy (c := a⁻¹ * s) (comm_of_conj hcℓ) (comm_of_conj hcy)

theorem exists_split (hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (T : Set G))
    (hSS : sStar T T₁ ≤ S) (hSnorm : ∀ s ∈ S, ∀ z ∈ sStar T T₁, s * z * s⁻¹ ∈ sStar T T₁) :
    ∀ s ∈ S, ∃ d ∈ sStar T T₁, ∃ c ∈ Cbar T T₁ S, s = d * c := by
  intro s hs
  obtain ⟨e₁, he₁, hs₁, hc₁⟩ := D.stage1 hSN hSS hSnorm s hs
  obtain ⟨e₂, he₂, hs₂, hc₂, hT₂⟩ := D.stage2 hSN hSS (e₁⁻¹ * s) hs₁ hc₁
  obtain ⟨e₃, he₃, hc⟩ := D.stage3 hSS (e₂⁻¹ * (e₁⁻¹ * s)) hs₂ hc₂ hT₂
  refine ⟨e₁ * e₂ * e₃, (sStar T T₁).mul_mem ((sStar T T₁).mul_mem he₁ he₂) he₃,
    e₃⁻¹ * (e₂⁻¹ * (e₁⁻¹ * s)), hc, by group⟩

theorem sStar_inf_Cbar : sStar T T₁ ⊓ Cbar T T₁ S = ⊥ := by
  rw [eq_bot_iff]
  rintro d ⟨hd, hc⟩
  obtain ⟨hdS, hdT, hdT₁⟩ := mem_Cbar_iff.1 hc
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨u, hu, t, ht, rfl⟩ := exists_mul_of_mem_sup_normIn hL₁N hd
  rw [Subgroup.mem_bot]
  rcases D.hL₁ u hu with hu1 | hu1
  · subst hu1
    have hct : t * ℓ = ℓ * t := by
      have := hdT₁ ℓ D.hℓT₁
      simpa using this.symm
    rcases D.cent_ℓ ht hct with h1 | h1
    · rw [h1]; simp
    · exfalso
      have hya : y * a = a * y := by
        have := hdT₁ y D.hy
        rw [h1] at this
        simpa using this
      have h1 := D.conj_a_y
      have h2 : a * y * a = y := by
        calc a * y * a = (a * y) * a := rfl
          _ = (y * a) * a := by rw [← hya]
          _ = y * (a * a) := by group
          _ = y := by rw [D.aa, mul_one]
      rw [h2] at h1
      exact D.hℓ1 (by
        have : y * 1 = y * ℓ := by rw [mul_one]; exact h1
        exact (mul_left_cancel this).symm)
  · exfalso
    rw [hu1] at hdT
    have h := hdT b D.hb
    have hbt : t * b = b * t := elemAbelian_mul_comm D.sec3.cfg.wc.1 ht D.hb
    have h2 : b * ℓ * t = ℓ * b * t := by
      calc b * ℓ * t = b * (ℓ * t) := by group
        _ = (ℓ * t) * b := h
        _ = ℓ * (t * b) := by group
        _ = ℓ * (b * t) := by rw [hbt]
        _ = ℓ * b * t := by group
    have h3 : b * ℓ = ℓ * b := mul_right_cancel h2
    rcases D.cent_ℓ D.hb h3 with h4 | h4
    · exact D.hbL (by rw [h4]; exact (normIn T T₁).one_mem)
    · exact D.hbL (by rw [h4]; exact D.ha)

end D8Data

end CFSG.CGT.T75H
