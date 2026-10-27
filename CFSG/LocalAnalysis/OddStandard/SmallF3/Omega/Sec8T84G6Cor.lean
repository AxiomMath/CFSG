module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Cl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec8t84g6_mem_sup_zpowers_iff {A : Subgroup G} {t : G} (ht : t ^ 2 = 1)
    (htc : t ∈ centralizer (A : Set G)) {x : G} :
    x ∈ A ⊔ zpowers t ↔ x ∈ A ∨ ∃ a ∈ A, x = t * a := by
  constructor
  · intro hx
    have hle : zpowers t ≤ normalizer (A : Set G) :=
      zpowers_le.mpr (centralizer_le_normalizer _ htc)
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A _ hle] at hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    have ht' : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ht]
    rw [zpow_eq_zpow_emod k ht']
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hk, zpow_zero, mul_one]
      exact ha
    · right
      refine ⟨a, ha, ?_⟩
      rw [hk, zpow_one]
      exact mem_centralizer_iff.mp htc a ha
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Subgroup.mem_sup_left h
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers t))
        (Subgroup.mem_sup_left ha)

theorem sec8t84g6_step [Finite G] {A : Subgroup G} {t : G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (ht : t * t = 1) (htA : t ∉ A) (htc : ∀ a ∈ A, a * t = t * a) :
    CFSG.Open.IsElemAbelian 2 (A ⊔ zpowers t : Subgroup G) ∧
      2 * Nat.card A ≤ Nat.card (A ⊔ zpowers t : Subgroup G) ∧
      ∀ x : G, x ∈ (A ⊔ zpowers t : Subgroup G) ↔ x ∈ A ∨ ∃ a ∈ A, x = t * a := by
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
  have htc' : t ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact htc a ha
  have hmem := fun x : G => sec8t84g6_mem_sup_zpowers_iff (A := A) ht2 htc' (x := x)
  have hcomm : ∀ x ∈ (A ⊔ zpowers t : Subgroup G), ∀ y ∈ (A ⊔ zpowers t : Subgroup G),
      x * y = y * x := by
    intro x hx y hy
    have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
    rcases (hmem x).mp hx with hx | ⟨a, ha, rfl⟩ <;> rcases (hmem y).mp hy with hy | ⟨b, hb, rfl⟩
    · exact hAc x hx y hy
    · calc x * (t * b) = (x * t) * b := by group
        _ = (t * x) * b := by rw [htc x hx]
        _ = t * (x * b) := by group
        _ = t * (b * x) := by rw [hAc x hx b hb]
        _ = t * b * x := by group
    · calc t * a * y = t * (a * y) := by group
        _ = t * (y * a) := by rw [hAc a ha y hy]
        _ = (t * y) * a := by group
        _ = (y * t) * a := by rw [htc y hy]
        _ = y * (t * a) := by group
    · calc t * a * (t * b) = t * (a * t) * b := by group
        _ = t * (t * a) * b := by rw [htc a ha]
        _ = (t * t) * (a * b) := by group
        _ = a * b := by rw [ht, one_mul]
        _ = b * a := hAc a ha b hb
        _ = (t * t) * (b * a) := by rw [ht, one_mul]
        _ = t * (t * b) * a := by group
        _ = t * (b * t) * a := by rw [← htc b hb]
        _ = t * b * (t * a) := by group
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩, ?_, hmem⟩
  · rcases (hmem x).mp hx with hx | ⟨a, ha, rfl⟩
    · exact hA.2 x hx
    · have haa : a ^ 2 = 1 := hA.2 a ha
      calc (t * a) ^ 2 = t * a * (t * a) := by rw [pow_two]
        _ = t * (a * t) * a := by group
        _ = t * (t * a) * a := by rw [htc a ha]
        _ = (t * t) * (a * a) := by group
        _ = 1 := by rw [ht, one_mul, ← pow_two, haa]
  · have hlt : A < (A ⊔ zpowers t : Subgroup G) := lt_of_le_of_ne le_sup_left fun h =>
      htA (h ▸ Subgroup.mem_sup_right (mem_zpowers t))
    have hcardlt : Nat.card A < Nat.card (A ⊔ zpowers t : Subgroup G) :=
      Subgroup.card_lt_of_lt hlt
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : A ≤ (A ⊔ zpowers t : Subgroup G))
    have hm2 : 2 ≤ m := by
      by_contra h
      have hle : Nat.card (A ⊔ zpowers t : Subgroup G) ≤ Nat.card A :=
        calc Nat.card (A ⊔ zpowers t : Subgroup G) = Nat.card A * m := hm
          _ ≤ Nat.card A * 1 := Nat.mul_le_mul_left _ (by omega)
          _ = Nat.card A := mul_one _
      omega
    calc 2 * Nat.card A ≤ m * Nat.card A := Nat.mul_le_mul_right _ hm2
      _ = Nat.card A * m := mul_comm _ _
      _ = Nat.card (A ⊔ zpowers t : Subgroup G) := hm.symm

theorem sec8t84g6_exists_E8 [Finite G] {H : Subgroup G} {a b c : G} (ha : a ∈ H) (hb : b ∈ H)
    (hc : c ∈ H) (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a)
    (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b) (hcab : c ≠ a * b) :
    ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E := by
  have hbot : CFSG.Open.IsElemAbelian 2 (⊥ : Subgroup G) :=
    ⟨⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])⟩⟩,
      fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩
  obtain ⟨h1e, h1c, h1m⟩ := sec8t84g6_step (A := ⊥) hbot ha2 (by simpa using ha1)
    (fun x hx => by rw [mem_bot.mp hx]; simp)
  have hA1 : ∀ x, x ∈ (⊥ : Subgroup G) ⊔ zpowers a ↔ x = 1 ∨ x = a := by
    intro x
    rw [h1m x]
    constructor
    · rintro (h | ⟨z, hz, rfl⟩)
      · exact Or.inl (mem_bot.mp h)
      · rw [mem_bot.mp hz]; exact Or.inr (by simp)
    · rintro (rfl | rfl)
      · exact Or.inl (one_mem _)
      · exact Or.inr ⟨1, one_mem _, by simp⟩
  obtain ⟨h2e, h2c, h2m⟩ := sec8t84g6_step (A := (⊥ : Subgroup G) ⊔ zpowers a) h1e hb2
    (by rw [hA1]; rintro (h | h); exact hb1 h; exact hba h)
    (fun x hx => by
      rcases (hA1 x).mp hx with rfl | rfl
      · simp
      · exact hab)
  have hA2 : ∀ x, x ∈ ((⊥ : Subgroup G) ⊔ zpowers a) ⊔ zpowers b ↔
      x = 1 ∨ x = a ∨ x = b * 1 ∨ x = b * a := by
    intro x
    rw [h2m x]
    constructor
    · rintro (h | ⟨z, hz, rfl⟩)
      · rcases (hA1 x).mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases (hA1 z).mp hz with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl (one_mem _)
      · exact Or.inl ((hA1 _).mpr (Or.inr rfl))
      · exact Or.inr ⟨1, one_mem _, rfl⟩
      · exact Or.inr ⟨a, (hA1 _).mpr (Or.inr rfl), rfl⟩
  obtain ⟨h3e, h3c, -⟩ := sec8t84g6_step (A := ((⊥ : Subgroup G) ⊔ zpowers a) ⊔ zpowers b) h2e hc2
    (by
      rw [hA2]
      rintro (h | h | h | h)
      · exact hc1 h
      · exact hca h
      · exact hcb (by simpa using h)
      · exact hcab (by rw [h, hab]))
    (fun x hx => by
      rcases (hA2 x).mp hx with rfl | rfl | rfl | rfl
      · simp
      · exact hac
      · simpa using hbc
      · calc b * a * c = b * (a * c) := by group
          _ = b * (c * a) := by rw [hac]
          _ = (b * c) * a := by group
          _ = (c * b) * a := by rw [hbc]
          _ = c * (b * a) := by group)
  refine ⟨_, ?_, h3e, ?_⟩
  · exact sup_le (sup_le (sup_le bot_le (zpowers_le.mpr ha)) (zpowers_le.mpr hb))
      (zpowers_le.mpr hc)
  · have hb1 : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    omega

theorem sec8t84g6_core [Finite G] {K U : Subgroup G} {γ y : G}
    (hKC : K ≤ centralizer ({γ} : Set G))
    (hCN : centralizer ({γ} : Set G) ≤ normalizer (K : Set G))
    (hZ : ∀ z ∈ K ⊓ centralizer (K : Set G), Odd (orderOf z))
    (hUe : CFSG.Open.IsElemAbelian 2 U) (hUC : U ≤ centralizer ({γ} : Set G))
    (hγ2 : γ * γ = 1) (hγ1 : γ ≠ 1) (hy : Odd (orderOf y))
    (hyC : y ∈ centralizer ({γ} : Set G)) (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U)
    (hyfix : ∀ u ∈ U, y * u = u * y → u = 1)
    (hyK : ∃ k ∈ K, ∃ c ∈ centralizer (K : Set G), y = k * c)
    (hrank : ∀ E : Subgroup G, E ≤ centralizer (K : Set G) → CFSG.Open.IsElemAbelian 2 E →
      Nat.card E ≤ 4) : U ≤ K := by
  by_contra hUK
  obtain ⟨u, huU, huK⟩ := Set.not_subset.mp hUK
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = centralizer ({γ} : Set G) ⊓ centralizer (K : Set G) :=
    ⟨_, rfl⟩
  have hDmem : ∀ x, x ∈ D ↔ x ∈ centralizer ({γ} : Set G) ∧ x ∈ centralizer (K : Set G) := by
    intro x; rw [hD]; exact Subgroup.mem_inf
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := fun k hk d hd =>
    mem_centralizer_iff.mp ((hDmem d).mp hd).2 k hk
  have hZ' : ∀ z ∈ K ⊓ D, Odd (orderOf z) := fun z hz => hZ z ⟨hz.1, ((hDmem z).mp hz.2).2⟩
  have hu2 : ∀ w ∈ U, w * w = 1 := fun w hw => by rw [← pow_two]; exact hUe.2 w hw
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm (⟨a, ha⟩ : U) ⟨b, hb⟩)
  obtain ⟨k₀, hk₀, c, hc, hyc⟩ := hyK
  have hUKD := sec8t84g6_U_le_KD hKC hCN hUC hyC hyU hyfix hk₀ hc hyc
  obtain ⟨k, hk, d, hd, hu⟩ := hUKD u huU
  rw [← hD] at hd
  obtain ⟨k₁, hk₁, d₁, hd₁, hdd₁, hu₁⟩ := sec8t84g6_dec_sq hKD hZ' hk hd hu (hu2 u huU)
  have hyN : ∀ x : G, x ∈ K ↔ y * x * y⁻¹ ∈ K := fun x =>
    mem_normalizer_iff.mp (hCN hyC) x
  have hyN' : ∀ x : G, x ∈ K ↔ y⁻¹ * x * y ∈ K := fun x => by
    have := mem_normalizer_iff.mp (hCN (Subgroup.inv_mem _ hyC)) x
    simpa using this
  have hγy : y * γ = γ * y := mem_centralizer_singleton_iff.mp hyC
  obtain ⟨d', hd'⟩ : ∃ d' : G, d' = y * d₁ * y⁻¹ := ⟨_, rfl⟩
  have hd'D : d' ∈ D := by
    obtain ⟨h1, h2⟩ := (hDmem d₁).mp hd₁
    refine (hDmem d').mpr ⟨?_, ?_⟩
    · rw [hd']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyC h1) (Subgroup.inv_mem _ hyC)
    · rw [mem_centralizer_iff]
      intro x hx
      have hx' : y⁻¹ * x * y ∈ K := (hyN' x).mp hx
      have := mem_centralizer_iff.mp h2 _ hx'
      rw [hd']
      calc x * (y * d₁ * y⁻¹) = y * ((y⁻¹ * x * y) * d₁) * y⁻¹ := by group
        _ = y * (d₁ * (y⁻¹ * x * y)) * y⁻¹ := by rw [this]
        _ = y * d₁ * y⁻¹ * x := by group
  have huU' : u ∈ U := huU
  have hu'U : y * u * y⁻¹ ∈ U := hyU u huU'
  obtain ⟨k₂, hk₂⟩ : ∃ k₂ : G, k₂ = y * k₁ * y⁻¹ := ⟨_, rfl⟩
  have hk₂K : k₂ ∈ K := by rw [hk₂]; exact (hyN k₁).mp hk₁
  have hu'eq : y * u * y⁻¹ = k₂ * d' := by rw [hu₁, hk₂, hd']; group
  have hd'd' : d' * d' = 1 := by
    calc d' * d' = y * (d₁ * d₁) * y⁻¹ := by rw [hd']; group
      _ = 1 := by rw [hdd₁]; group
  have hsq₁ : (k₁ * d₁) * (k₁ * d₁) = 1 := by rw [← hu₁]; exact hu2 u huU'
  have hsq₂ : (k₂ * d') * (k₂ * d') = 1 := by rw [← hu'eq]; exact hu2 _ hu'U
  have hcomm₁₂ : (k₁ * d₁) * (k₂ * d') = (k₂ * d') * (k₁ * d₁) := by
    rw [← hu₁, ← hu'eq]; exact hUcomm u huU' _ hu'U
  have hd₁d' : d₁ * d' = d' * d₁ :=
    sec8t84g6_pair hKD hZ' hk₁ hk₂K hd₁ hd'D hdd₁ hd'd' hsq₁ hsq₂ hcomm₁₂
  have hyγ' : y * γ * y⁻¹ = γ := by
    calc y * γ * y⁻¹ = γ * y * y⁻¹ := by rw [hγy]
      _ = γ := by group
  have hd₁1 : d₁ ≠ 1 := by
    intro h
    apply huK
    rw [hu₁, h, mul_one]
    exact hk₁
  have hd'1 : d' ≠ 1 := by
    intro h
    apply hd₁1
    have h1 : y * d₁ * y⁻¹ = 1 := by rw [← hd']; exact h
    calc d₁ = y⁻¹ * (y * d₁ * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hd'd₁ : d' ≠ d₁ := by
    intro h
    apply huK
    have hu'eq' : y * u * y⁻¹ = k₂ * d₁ := by rw [hu'eq, h]
    have hkk : (k₁⁻¹ * k₂) * d₁ = d₁ * (k₁⁻¹ * k₂) :=
      hKD _ (K.mul_mem (K.inv_mem hk₁) hk₂K) d₁ hd₁
    have e : u⁻¹ * (y * u * y⁻¹) = k₁⁻¹ * k₂ := by
      calc u⁻¹ * (y * u * y⁻¹) = (k₁ * d₁)⁻¹ * (k₂ * d₁) := by rw [hu'eq', hu₁]
        _ = d₁⁻¹ * ((k₁⁻¹ * k₂) * d₁) := by group
        _ = d₁⁻¹ * (d₁ * (k₁⁻¹ * k₂)) := by rw [hkk]
        _ = k₁⁻¹ * k₂ := by group
    have hmemV : u⁻¹ * (y * u * y⁻¹) ∈ (U ⊓ K : Subgroup G) := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ huU') hu'U, ?_⟩
      rw [e]
      exact K.mul_mem (K.inv_mem hk₁) hk₂K
    have hyV : ∀ w ∈ (U ⊓ K : Subgroup G), y * w * y⁻¹ ∈ (U ⊓ K : Subgroup G) := fun w hw =>
      ⟨hyU w hw.1, (hyN w).mp hw.2⟩
    exact (sec8t84g6_mem_of_psi_mem inf_le_left hyV hyfix huU' hmemV).2
  have hγd₁ : γ ≠ d₁ := by
    intro h
    apply hd'd₁
    rw [hd', ← h]
    exact hyγ'
  have hγd' : γ ≠ d' := by
    intro h
    apply hd'd₁
    have h1 : y * d₁ * y⁻¹ = γ := by rw [← hd']; exact h.symm
    have hyγ'' : y⁻¹ * γ * y = γ := by
      calc y⁻¹ * γ * y = y⁻¹ * (γ * y) := by group
        _ = y⁻¹ * (y * γ) := by rw [hγy]
        _ = γ := by group
    have h2 : d₁ = γ := by
      calc d₁ = y⁻¹ * (y * d₁ * y⁻¹) * y := by group
        _ = y⁻¹ * γ * y := by rw [h1]
        _ = γ := hyγ''
    exact h.symm.trans h2.symm
  have hγab : γ ≠ d₁ * d' := by
    intro h
    apply hd'd₁
    obtain ⟨d'', hd''⟩ : ∃ d'' : G, d'' = y * d' * y⁻¹ := ⟨_, rfl⟩
    have h1 : γ = d' * d'' := by
      calc γ = y * γ * y⁻¹ := hyγ'.symm
        _ = y * (d₁ * d') * y⁻¹ := by rw [← h]
        _ = (y * d₁ * y⁻¹) * (y * d' * y⁻¹) := by group
        _ = d' * d'' := by rw [← hd', ← hd'']
    have h2 : d₁ = d'' := by
      have h3 : d' * d₁ = d' * d'' := by rw [← hd₁d']; exact h.symm.trans h1
      exact mul_left_cancel h3
    have h3 : d₁ = y * (y * d₁ * y⁻¹) * y⁻¹ := by rw [← hd', ← hd'']; exact h2
    have hyy : y * y * d₁ = d₁ * (y * y) := by
      calc y * y * d₁ = (y * (y * d₁ * y⁻¹) * y⁻¹) * (y * y) := by group
        _ = d₁ * (y * y) := by rw [← h3]
    obtain ⟨j, hj⟩ := hy
    have hyp : (y * y) ^ (j + 1) = y := by
      rw [← pow_two, ← pow_mul]
      have : 2 * (j + 1) = orderOf y + 1 := by omega
      rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
    have hyd : y * d₁ = d₁ * y := by
      have := (Commute.pow_left (hyy : Commute (y * y) d₁) (j + 1)).eq
      rwa [hyp] at this
    rw [hd']
    calc y * d₁ * y⁻¹ = d₁ * y * y⁻¹ := by rw [hyd]
      _ = d₁ := by group
  have hγH : γ ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.mp (hKC hx) γ (Set.mem_singleton γ)).symm
  have hdγ : ∀ x ∈ D, γ * x = x * γ := fun x hx =>
    mem_centralizer_iff.mp ((hDmem x).mp hx).1 γ (Set.mem_singleton γ)
  obtain ⟨E, hEH, hEe, hE8⟩ := sec8t84g6_exists_E8 (H := centralizer (K : Set G))
    ((hDmem d₁).mp hd₁).2 ((hDmem d').mp hd'D).2 hγH hdd₁ hd'd' hγ2 hd₁d'
    (hdγ d₁ hd₁).symm (hdγ d' hd'D).symm hd₁1 hd'1 hd'd₁ hγ1 hγd₁ hγd' hγab
  have h4 := hrank E hEH hEe
  omega

end CFSG.OddStandard.SmallF3.Omega
