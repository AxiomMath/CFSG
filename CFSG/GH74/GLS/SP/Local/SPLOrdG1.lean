module

public import CFSG.GH74.GLS.SP.Local.SPLL34c

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section G1

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

@[expose] def SPLNot3.Kt (D : SPLNot3 G) : Subgroup G := D.K ⊔ zpowers D.t

omit [Finite G] in
theorem z_comm_K₁ (hs : SPLSetup D.toSPLNot0) {k : G} (hk : k ∈ D.K₁) : D.z * k = k * D.z :=
  (hs.comps.cz₁ hk).symm

theorem t_conj_z (hs : SPLSetup D.toSPLNot0) : D.t * D.z * D.t⁻¹ = D.z := by
  have h := z_comm_t D hs
  calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [← h]
    _ = D.z := by group

omit [Finite G] in
theorem zpow_z_cases (hs : SPLSetup D.toSPLNot0) (j : ℤ) : D.z ^ j = 1 ∨ D.z ^ j = D.z := by
  have hzz := z_mul_z D hs
  rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, zpow_two, hzz, one_zpow]
  · right
    have h2 : D.z ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, hzz, one_zpow]
    rw [zpow_add_one, h2, one_mul]

theorem kt_involution (hs : SPLSetup D.toSPLNot0) {κ : G} (hκ : κ ∈ D.K)
    (h : (κ * D.t) * (κ * D.t) = 1) :
    ∃ g ∈ D.K₁, κ * D.t = g * D.t * g⁻¹ ∨ κ * D.t = g * (D.t * D.z) * g⁻¹ := by
  have htt := t_mul_t D hs
  have hti : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right htt
  have hzt := z_comm_t D hs
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := mem_sup_of_commute hs.comps.comm hκ
  obtain ⟨a, ha_def⟩ : ∃ a : G, a = D.t * k₁ * D.t⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : G, b = D.t * k₂ * D.t⁻¹ := ⟨_, rfl⟩
  have ha : a ∈ D.K₂ := by rw [ha_def]; exact t_conj_K₁ D hs k₁ hk₁
  have hb : b ∈ D.K₁ := by rw [hb_def]; exact t_conj_K₂ D hs k₂ hk₂
  have h1 : k₁ * k₂ * a * b = 1 := by
    have e : (k₁ * k₂ * D.t) * (k₁ * k₂ * D.t) = k₁ * k₂ * a * b * (D.t * D.t) := by
      rw [ha_def, hb_def]; group
    rw [h, htt, mul_one] at e
    exact e.symm
  have hc1 : b * k₂ = k₂ * b := hs.comps.comm b hb k₂ hk₂
  have hc2 : b * a = a * b := hs.comps.comm b hb a ha
  have h2 : (k₁ * b) * (k₂ * a) = 1 := by
    calc (k₁ * b) * (k₂ * a) = k₁ * (b * k₂) * a := by group
      _ = k₁ * (k₂ * b) * a := by rw [hc1]
      _ = k₁ * k₂ * (b * a) := by group
      _ = k₁ * k₂ * (a * b) := by rw [hc2]
      _ = k₁ * k₂ * a * b := by group
      _ = 1 := h1
  have hmem1 : k₁ * b ∈ D.K₁ := D.K₁.mul_mem hk₁ hb
  have hmem2 : k₁ * b ∈ D.K₂ := by
    have : k₁ * b = (k₂ * a)⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this]
    exact D.K₂.inv_mem (D.K₂.mul_mem hk₂ ha)
  have hmemz : k₁ * b ∈ zpowers D.z := by
    rw [← hs.comps.inf_eq]; exact ⟨hmem1, hmem2⟩
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmemz
  have hb' : b = k₁⁻¹ * D.z ^ j := by
    calc b = k₁⁻¹ * (k₁ * b) := by group
      _ = k₁⁻¹ * D.z ^ j := by rw [hj]
  have hzj_t : D.t * D.z ^ j = D.z ^ j * D.t :=
    (Commute.zpow_right (show Commute D.t D.z from hzt.symm) j).eq
  have hk₂b : k₂ = D.t * b * D.t := by
    rw [hb_def, hti]
    calc k₂ = (D.t * D.t) * k₂ * (D.t * D.t) := by rw [htt]; group
      _ = D.t * (D.t * k₂ * D.t) * D.t := by group
  have hz1 : (k₁ : G) * D.z ^ j = D.z ^ j * k₁ :=
    (Commute.zpow_right (show Commute k₁ D.z from (z_comm_K₁ D hs hk₁).symm) j).eq
  have hres : k₁ * k₂ * D.t = k₁ * (D.t * D.z ^ j) * k₁⁻¹ := by
    rw [hk₂b, hb']
    calc k₁ * (D.t * (k₁⁻¹ * D.z ^ j) * D.t) * D.t
        = k₁ * D.t * k₁⁻¹ * D.z ^ j * (D.t * D.t) := by
          have e : D.t * D.z ^ j = D.z ^ j * D.t := hzj_t
          calc k₁ * (D.t * (k₁⁻¹ * D.z ^ j) * D.t) * D.t
              = k₁ * D.t * k₁⁻¹ * (D.z ^ j * D.t) * D.t := by group
            _ = k₁ * D.t * k₁⁻¹ * (D.t * D.z ^ j) * D.t := by rw [e]
            _ = k₁ * D.t * k₁⁻¹ * D.z ^ j * (D.t * D.t) := by
                rw [e]; group
      _ = k₁ * D.t * k₁⁻¹ * D.z ^ j := by rw [htt, mul_one]
      _ = k₁ * (D.t * D.z ^ j) * k₁⁻¹ := by
          have hk : k₁⁻¹ * D.z ^ j = D.z ^ j * k₁⁻¹ := by
            calc k₁⁻¹ * D.z ^ j = k₁⁻¹ * (D.z ^ j * k₁) * k₁⁻¹ := by group
              _ = k₁⁻¹ * (k₁ * D.z ^ j) * k₁⁻¹ := by rw [hz1]
              _ = D.z ^ j * k₁⁻¹ := by group
          calc k₁ * D.t * k₁⁻¹ * D.z ^ j = k₁ * D.t * (k₁⁻¹ * D.z ^ j) := by group
            _ = k₁ * D.t * (D.z ^ j * k₁⁻¹) := by rw [hk]
            _ = k₁ * (D.t * D.z ^ j) * k₁⁻¹ := by group
  refine ⟨k₁, hk₁, ?_⟩
  rcases zpow_z_cases D hs j with hj1 | hj1
  · left
    rw [hres, hj1, mul_one]
  · right
    rw [hres, hj1]

theorem exists_conj_mem_S {x : G} (hx : orderOf x = 2) :
    ∃ g : G, g * x * g⁻¹ ∈ (D.S : Subgroup G) := by
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P D.S
  refine ⟨g, ?_⟩
  have hxP : x ∈ (P : Subgroup G) := hP (mem_zpowers x)
  have : g * x * g⁻¹ ∈ ((g • P : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hxP, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hg] at this
  exact this

theorem S_le_Kt (hs : SPLSetup D.toSPLNot0) : (D.S : Subgroup G) ≤ D.Kt := by
  have htt := t_mul_t D hs
  intro s hsS
  rcases mem_K_or_mul_of_index_two (D.S : Subgroup G) D.K D.t hs.syl.t_mem (t_not_mem_K D hs)
      hs.syl.index s hsS with h | h
  · exact Subgroup.mem_sup_left h
  · have : s = (s * D.t) * D.t := by
      calc s = s * (D.t * D.t) := by rw [htt, mul_one]
        _ = (s * D.t) * D.t := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (mem_zpowers _))

theorem inv_classes (hs : SPLSetup D.toSPLNot0) {x : G} (hx : orderOf x = 2) :
    IsConj D.t x ∨ IsConj D.z x := by
  have htt := t_mul_t D hs
  obtain ⟨g, hg⟩ := exists_conj_mem_S D hx
  have hconj : IsConj (g * x * g⁻¹) x := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hs2 : orderOf (g * x * g⁻¹) = 2 := by rw [orderOf_conj']; exact hx
  rcases mem_K_or_mul_of_index_two (D.S : Subgroup G) D.K D.t hs.syl.t_mem (t_not_mem_K D hs)
      hs.syl.index _ hg with h | h
  · by_cases hz : g * x * g⁻¹ = D.z
    · right
      rw [← hz]; exact hconj
    · left
      exact (hs.syl.inv_K h hs2 hz).trans hconj
  · have hκ : (g * x * g⁻¹ * D.t) * D.t = g * x * g⁻¹ := by
      calc (g * x * g⁻¹ * D.t) * D.t = g * x * g⁻¹ * (D.t * D.t) := by group
        _ = g * x * g⁻¹ := by rw [htt, mul_one]
    have hinv : (g * x * g⁻¹ * D.t) * D.t * ((g * x * g⁻¹ * D.t) * D.t) = 1 := by
      rw [hκ]
      have := pow_orderOf_eq_one (g * x * g⁻¹)
      rw [hs2, pow_two] at this
      exact this
    obtain ⟨g', -, hg'⟩ := kt_involution D hs h hinv
    rw [hκ] at hg'
    rcases hg' with h1 | h1
    · left
      exact (isConj_iff.mpr ⟨g', h1.symm⟩).trans hconj
    · right
      have h2 : IsConj D.z (g * x * g⁻¹) := by
        have h3 : IsConj (D.t * D.z) (g * x * g⁻¹) := isConj_iff.mpr ⟨g', h1.symm⟩
        exact hs.syl.tz_conj.trans h3
      exact h2.trans hconj

omit [Finite G] in
theorem K_le_C (hs : SPLSetup D.toSPLNot0) : D.K ≤ D.C := by
  intro k hk
  exact mem_centralizer_singleton_iff.mpr (z_cen_K D hs k hk).symm

theorem Kt_le_C (hs : SPLSetup D.toSPLNot0) : D.Kt ≤ D.C := by
  refine sup_le (K_le_C D hs) ?_
  rw [zpowers_le]
  exact t_mem_Cz hs

theorem t_le_normalizer_K (hs : SPLSetup D.toSPLNot0) : zpowers D.t ≤ normalizer (D.K : Set G) := by
  rw [zpowers_le, mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact t_normalizes_K hs x hx
  · intro hx
    have := t_normalizes_K hs _ hx
    have htt := t_mul_t D hs
    have e : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = x := by
      calc D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * x * (D.t * D.t)⁻¹ := by group
        _ = x := by rw [htt]; group
    rwa [e] at this

theorem F_normalizes_Kt (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ∀ y ∈ D.F, ∀ x ∈ D.Kt, y * x * y⁻¹ ∈ D.Kt := by
  intro y hy x hx
  obtain ⟨κ, hκ, τ, hτ, rfl⟩ := mem_sup_of_le_normalizer (t_le_normalizer_K D hs) hx
  have hyt : y * D.t = D.t * y := mem_centralizer_singleton_iff.mp (hc.F_eq hy)
  have hyτ : y * τ * y⁻¹ = τ := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hτ
    have hcomm : Commute y D.t := hyt
    rw [(hcomm.zpow_right j).eq]; group
  have hyκ : y * κ * y⁻¹ ∈ D.K := hs.comps.conj_sup_mem (F_le_C hs hy) hκ
  have e : y * (κ * τ) * y⁻¹ = (y * κ * y⁻¹) * τ := by
    calc y * (κ * τ) * y⁻¹ = (y * κ * y⁻¹) * (y * τ * y⁻¹) := by group
      _ = (y * κ * y⁻¹) * τ := by rw [hyτ]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyκ) (Subgroup.mem_sup_right hτ)

theorem odd_mem_K_of_mem_Kt (hs : SPLSetup D.toSPLNot0) {f : G} (hf : f ∈ D.Kt)
    (hodd : Odd (orderOf f)) : f ∈ D.K := by
  have htt := t_mul_t D hs
  obtain ⟨κ, hκ, τ, hτ, rfl⟩ := mem_sup_of_le_normalizer (t_le_normalizer_K D hs) hf
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hτ
  rcases Int.even_or_odd' i with ⟨m, rfl | rfl⟩
  · have : D.t ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, htt, one_zpow]
    rw [this, mul_one]; exact hκ
  · have h1 : D.t ^ (2 * m + 1) = D.t := by
      have : D.t ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, htt, one_zpow]
      rw [zpow_add_one, this, one_mul]
    rw [h1] at hodd ⊢
    have hsq : (κ * D.t) ^ 2 ∈ D.K := by
      have e : (κ * D.t) ^ 2 = κ * (D.t * κ * D.t⁻¹) := by
        rw [pow_two]
        calc κ * D.t * (κ * D.t) = κ * (D.t * κ * D.t⁻¹) * (D.t * D.t) := by group
          _ = κ * (D.t * κ * D.t⁻¹) := by rw [htt, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ hκ (t_normalizes_K hs κ hκ)
    exact mem_of_pow_mem_of_coprime D.K (Nat.coprime_two_left.mpr hodd) hsq (pow_orderOf_eq_one _)

theorem F_inf_Kt (hs : SPLSetup D.toSPLNot0) : D.F ⊓ D.Kt = ⊥ := by
  rw [eq_bot_iff]
  rintro f ⟨hfF, hfKt⟩
  have hfK : f ∈ D.K := odd_mem_K_of_mem_Kt D hs hfKt (F_odd D.toSPLNot0 hfF)
  have := F_inf_K_eq (D := D.toSPLNot0) hs
  have h : f ∈ D.F ⊓ D.K := ⟨hfF, hfK⟩
  rw [this] at h
  exact h

theorem inv_C_le_Kt (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {c : G} (hcC : c ∈ D.C)
    (hc2 : c * c = 1) : c ∈ D.Kt := by
  obtain ⟨k, hk, s, hsS, y, hyF, rfl⟩ := hs.gen c hcC
  have hks : k * s ∈ D.Kt := Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (S_le_Kt D hs hsS)
  have hy2 : y * y ∈ D.Kt := by
    have e : y * y = ((k * s) * (y * (k * s) * y⁻¹))⁻¹ := by
      have h' : (k * s) * (y * (k * s) * y⁻¹) * (y * y) = 1 := by
        calc (k * s) * (y * (k * s) * y⁻¹) * (y * y) = (k * s * y) * (k * s * y) := by group
          _ = 1 := hc2
      exact (eq_inv_of_mul_eq_one_right h')
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hks (F_normalizes_Kt D hs hc y hyF _ hks))
  have hy2F : y * y ∈ D.F := Subgroup.mul_mem _ hyF hyF
  have hy2one : y * y = 1 := by
    have : y * y ∈ D.F ⊓ D.Kt := ⟨hy2F, hy2⟩
    rw [F_inf_Kt D hs] at this
    exact Subgroup.mem_bot.mp this
  have hy1 : y = 1 := by
    have hodd := F_odd D.toSPLNot0 hyF
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2one)
    have : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp this
  rw [hy1, mul_one]
  exact hks

theorem C_eq_Kt_sup_F (hs : SPLSetup D.toSPLNot0) : D.C = D.Kt ⊔ D.F := by
  apply le_antisymm
  · intro c hcC
    obtain ⟨k, hk, s, hsS, y, hyF, rfl⟩ := hs.gen c hcC
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hk)) (Subgroup.mem_sup_left (S_le_Kt D hs hsS)))
      (Subgroup.mem_sup_right hyF)
  · exact sup_le (Kt_le_C D hs) (F_le_C hs)

theorem F_le_normalizer_Kt (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    D.F ≤ normalizer (D.Kt : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact F_normalizes_Kt D hs hc y hy x hx
  · intro hx
    have := F_normalizes_Kt D hs hc y⁻¹ (D.F.inv_mem hy) _ hx
    have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem card_C (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥D.C = Nat.card ↥D.Kt * Nat.card ↥D.F := by
  have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (F_le_normalizer_Kt D hs hc)
  rw [inf_comm, F_inf_Kt D hs, Subgroup.card_bot, mul_one] at h
  rw [C_eq_Kt_sup_F D hs]
  exact h

theorem card_Kt (hs : SPLSetup D.toSPLNot0) : Nat.card ↥D.Kt = 2 * Nat.card ↥D.K := by
  have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (t_le_normalizer_K D hs)
  have hinf : D.K ⊓ zpowers D.t = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgK, hgt⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hgt
    have htt := t_mul_t D hs
    rcases Int.even_or_odd' i with ⟨m, rfl | rfl⟩
    · have : D.t ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, htt, one_zpow]
      rw [this]; exact Subgroup.one_mem _
    · exfalso
      have : D.t ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, htt, one_zpow]
      rw [zpow_add_one, this, one_mul] at hgK
      exact t_not_mem_K D hs hgK
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hs.syl.t_ord] at h
  show Nat.card ↥(D.K ⊔ zpowers D.t) = _
  rw [h, mul_comm]

theorem card_K₁_eq (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    2 * Nat.card ↥D.I = Nat.card ↥D.K₁ := by
  have hK₁ := card_K₁ (D := D.toSPLNot0) hs
  have hI := card_I D hs hc
  have hev : 2 ∣ D.q * (D.q ^ 2 - 1) := by
    obtain ⟨m, hm⟩ := hs.odd_q
    have : D.q ^ 2 - 1 = (2 * m) * (2 * m + 2) := by
      have h2 : D.q ^ 2 = (2 * m) * (2 * m + 2) + 1 := by rw [hm]; ring
      omega
    rw [this]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_mul_right 2 m) _) _
  rw [hK₁, hI]; exact Nat.mul_div_cancel' hev

theorem card_K (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥D.K = 2 * Nat.card ↥D.I ^ 2 := by
  have h := hs.comps.card_sup hs.syl.z_inv
  have hK₂ : Nat.card ↥D.K₂ = Nat.card ↥D.K₁ := by
    rw [← hs.syl.t_swap]
    exact (card_map_conj D.K₁ D.t)
  have hI2 := card_K₁_eq D hs hc
  show Nat.card ↥(D.K₁ ⊔ D.K₂) = _
  rw [hK₂, ← hI2] at h
  nlinarith [h]

end G1

end CFSG.GH74.GLS.SP.Local
