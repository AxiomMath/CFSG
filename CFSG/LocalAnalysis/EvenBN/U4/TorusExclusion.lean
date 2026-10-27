module

public import CFSG.LocalAnalysis.EvenBN.U4.TorusPrelim
public import CFSG.LocalAnalysis.EvenBN.U4.LayersTwoCenter
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFour

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup
  card_sup_mul_card_inf_eq)
open scoped MatrixGroups

theorem not_dvd_sec3_15 {q : ℕ} (hq : 4 ≤ q) :
    ¬ (q + 1) * (q ^ 2 - 1) ∣ (q ^ 2) ^ 2 - 1 ∧ ¬ (q + 1) * (q - 1) ^ 2 ∣ (q ^ 2) ^ 2 - 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  have e1 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    rw [show (a + 1) ^ 2 = a * (a + 2) + 1 by ring, Nat.add_sub_cancel]
  have e2 : ((a + 1) ^ 2) ^ 2 - 1 = a * (a + 2) * (a * (a + 2) + 2) := by
    rw [show ((a + 1) ^ 2) ^ 2 = a * (a + 2) * (a * (a + 2) + 2) + 1 by ring, Nat.add_sub_cancel]
  have e3 : a + 1 - 1 = a := by omega
  rw [e1, e2, e3]
  have hpos : 0 < a * (a + 2) := Nat.mul_pos (by omega) (by omega)
  constructor
  · intro hd
    rw [show (a + 1 + 1) * (a * (a + 2)) = a * (a + 2) * (a + 2) by ring] at hd
    have h1 := Nat.dvd_of_mul_dvd_mul_left hpos hd
    have h2 : a + 2 ∣ 2 := (Nat.dvd_add_right (dvd_mul_left (a + 2) a)).1 h1
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · intro hd
    rw [show (a + 1 + 1) * a ^ 2 = a * (a + 2) * a by ring] at hd
    have h1 := Nat.dvd_of_mul_dvd_mul_left hpos hd
    have h2 : a ∣ 2 := (Nat.dvd_add_right (dvd_mul_right a (a + 2))).1 h1
    have := Nat.le_of_dvd (by norm_num) h2
    omega

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)


theorem exists_torus_M2 (hS : Setting h L η t Q T) :
    ∃ J : Subgroup G, J ≤ miyamotoM2G h L η t Q ∧
      J ≤ centralizer (miyamotoIN2G h L η : Set G) ∧ J ≤ normalizer (𝓥 : Set G) ∧
      J ⊓ centralizer (𝓥 : Set G) = ⊥ ∧
      (Nat.card J = (2 ^ f) ^ 2 - 1 ∨ Nat.card J = (2 ^ f - 1) ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := miyamotoM2G h L η t Q with hMdef
  obtain ⟨-, -, hNM, -, hVM, -, -, -⟩ := hS.sec3_12_two
  obtain ⟨d, hd⟩ := (isCyclic_miyamotoIN2G h L η).exists_generator
  have hdM : (d : G) ∈ M := hNM (mem_inf.1 d.2).2
  set d' : M := ⟨d, hdM⟩ with hd'
  have hcardIN := card_miyamotoIN2G h L η
  have hq4 := hS.four_le
  have hd1 : d' ≠ 1 := by
    intro e
    have h0 : ((d' : M) : G) = 1 := by rw [e]; rfl
    have hd1' : d = 1 := Subtype.ext h0
    have hall : ∀ x : miyamotoIN2G h L η, x = 1 := fun x => by
      obtain ⟨n, hn⟩ := hd x
      rw [← hn]
      simp only [hd1', one_zpow]
    have : Nat.card (miyamotoIN2G h L η) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨1⟩⟩
    omega
  have hdpow : (d : G) ^ (2 ^ f - 1) = 1 := by
    have e : d ^ Nat.card (miyamotoIN2G h L η) = 1 := pow_card_eq_one'
    rw [hcardIN] at e
    have := congrArg Subtype.val e
    simpa using this
  have hd'pow : d' ^ (2 ^ f - 1) = 1 := Subtype.ext (by simpa [hd'] using hdpow)
  set V' : Subgroup M := (𝓥 : Subgroup G).subgroupOf M with hV'
  have hV'card : Nat.card V' = (2 ^ f) ^ 2 := by
    rw [hV', Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv, hS.card_V2]
  have hdV : d' ∈ normalizer (V' : Set M) := by
    rw [mem_normalizer_iff]
    intro v
    exact mem_normalizer_iff.1 (hS.IN2G_le_normalizer_V2 d.2) v
  have htrans : ∀ J' : Subgroup M, J' ≤ centralizer (zpowers d' : Set M) →
      J' ≤ normalizer (V' : Set M) → J' ⊓ centralizer (V' : Set M) = ⊥ →
      J'.map M.subtype ≤ centralizer (miyamotoIN2G h L η : Set G) ∧
        J'.map M.subtype ≤ normalizer (𝓥 : Set G) ∧
        J'.map M.subtype ⊓ centralizer (𝓥 : Set G) = ⊥ := by
    intro J' hJC hJN hJI
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨j, hj, rfl⟩
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨n, hn⟩ := hd ⟨y, hy⟩
      have hyn : y = (d : G) ^ n := by
        have := congrArg Subtype.val hn
        simp only [SubgroupClass.coe_zpow] at this
        exact this.symm
      have hc := congrArg Subtype.val
        (mem_centralizer_iff.1 (hJC hj) (d' ^ n) (zpow_mem_zpowers d' n))
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow, hd'] at hc
      rw [hyn]
      exact hc
    · rintro _ ⟨j, hj, rfl⟩
      refine mem_normalizer_fintype fun v hv => ?_
      have hvM : v ∈ M := hVM hv
      have hv' : (⟨v, hvM⟩ : M) ∈ V' := hv
      have := (mem_normalizer_iff.1 (hJN hj) ⟨v, hvM⟩).1 hv'
      exact this
    · refine eq_bot_iff.2 ?_
      rintro _ ⟨⟨j, hj, rfl⟩, hjC⟩
      have hj' : j ∈ J' ⊓ centralizer (V' : Set M) := by
        refine mem_inf.2 ⟨hj, mem_centralizer_iff.2 fun v hv => Subtype.ext ?_⟩
        exact mem_centralizer_iff.1 hjC v hv
      rw [hJI, mem_bot] at hj'
      rw [hj', map_one]
      exact one_mem _
  rcases hS.sec3_12_two_iso_all.or with ⟨k, _, _, hk, ψ, α, hψα, -⟩ |
      ⟨k₂, _, _, hk₂, ψ, -, -⟩
  · have : CharP k 2 := charP_of_card_eq_prime_pow (f := f) hk
    set g := α ⟨d, (mem_inf.1 d.2).2⟩ with hg
    have hψd : ψ d' = (g, g) := hψα ⟨d, (mem_inf.1 d.2).2⟩ d' rfl
    have hg1 : g ≠ 1 := by
      intro e
      apply hd1
      have : (⟨d, (mem_inf.1 d.2).2⟩ : miyamotoN2G h L η) = 1 := by
        rw [← map_one α] at e
        exact α.injective e
      have h0 : (d : G) = 1 := by simpa using congrArg Subtype.val this
      exact Subtype.ext h0
    have hgpow : g ^ (Nat.card k - 1) = 1 := by
      rw [Nat.card_eq_fintype_card, hk, hg, ← map_pow]
      have : (⟨d, (mem_inf.1 d.2).2⟩ : miyamotoN2G h L η) ^ (2 ^ f - 1) = 1 :=
        Subtype.ext (by simpa using hdpow)
      rw [this, map_one]
    have hS' : Nat.card V' = Nat.card k ^ 2 := by rw [hV'card, Nat.card_eq_fintype_card, hk]
    obtain ⟨hN, hI⟩ := Common.centralizer_zpowers_le_normalizer_and_inf_prod ψ hψd hg1 hgpow hS'
      hdV
    obtain ⟨h1, h2, h3⟩ := htrans _ le_rfl hN hI
    refine ⟨_, map_subtype_le _, h1, h2, h3, Or.inr ?_⟩
    rw [card_map_of_injective M.subtype_injective,
      Common.card_centralizer_zpowers_prod ψ hψd hg1 hgpow, Nat.card_eq_fintype_card, hk]
  · have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := 2 * f)
      (by rw [hk₂, ← pow_mul, mul_comm])
    have hdq : d' ^ (Nat.card k₂ - 1) = 1 := by
      rw [Nat.card_eq_fintype_card, hk₂]
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = m + 1 :=
        ⟨2 ^ f - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
      have e : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
        rw [hm, Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 1 + 1) + 1 by ring,
          Nat.add_sub_cancel]
      rw [e, pow_mul, hd'pow, one_pow]
    have hS' : Nat.card V' = Nat.card k₂ := by rw [hV'card, Nat.card_eq_fintype_card, hk₂]
    have hN := Common.centralizer_zpowers_le_normalizer ψ hd1 hdq hS' hdV
    have hI := Common.centralizer_zpowers_inf_centralizer_eq_bot ψ hd1 hdq hS' hdV
    obtain ⟨h1, h2, h3⟩ := htrans _ le_rfl hN hI
    refine ⟨_, map_subtype_le _, h1, h2, h3, Or.inl ?_⟩
    rw [card_map_of_injective M.subtype_injective, Common.card_centralizer_zpowers ψ hd1 hdq,
      Nat.card_eq_fintype_card, hk₂]

theorem sec3_15 (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2) (ψ : miyamotoM1G h L η t ≃* SL(2, k₂)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := h.finite
  have hk2' : Nat.card k₂ = 2 ^ (4 * f) := by
    rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, ← pow_mul]
    ring_nf
  have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := 4 * f) (by
    rw [hk₂, ← pow_mul, ← pow_mul]
    ring_nf)
  set M := miyamotoM1G h L η t with hMdef
  obtain ⟨hMH, hHM, hNM, -, hWM, -, hZ, -, -⟩ := hS.sec3_12_one
  have hq4 := hS.four_le
  obtain ⟨J, hJM2, hJIN2, hJV, hJCV, hJcard⟩ := hS.exists_torus_M2
  have hJI : J ≤ centralizer (miyamotoIG h L η : Set G) := by
    intro j hj
    rw [mem_centralizer_iff]
    intro i hi
    obtain ⟨i₂, hi₂, d, hd, rfl⟩ := hS.exists_I2_mul_IN2 hi
    have h1 : i₂ * j = j * i₂ := mem_centralizer_iff.1
      ((hS.sec3_12_two.1.trans inf_le_right) (hJM2 hj)) i₂ hi₂
    have h2 : d * j = j * d := mem_centralizer_iff.1 (hJIN2 hj) d hd
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hJE : J ≤ centralizer (miyamotoEG h L η Q : Set G) := hJM2.trans hS.M2G_le_centralizer_E
  have hJF2 : J ≤ normalizer (miyamotoF2G h L η t Q : Set G) :=
    hJM2.trans (hS.sec3_12_two.1.trans inf_le_left)
  have hJR : J ≤ normalizer (miyamotoRG h L η t Q : Set G) := fun j hj => by
    rw [← hS.F2_sup_V2]
    exact mem_normalizer_sup (hJF2 hj) (hJV hj)
  have hJF1 : J ≤ normalizer (miyamotoF1G h L η t : Set G) :=
    hJR.trans hS.normalizer_RG_le_normalizer_F1
  have hJI1 : J ≤ centralizer (miyamotoI1G h L η : Set G) :=
    hJI.trans (centralizer_le (SetLike.coe_subset_coe.2 hS.I1G_le_IG))
  have hJN : J ≤ normalizer (M : Set G) := fun j hj => hHM (mem_inf.2 ⟨hJF1 hj, hJI1 hj⟩)
  have hJW : J ≤ normalizer (𝓦 : Set G) := fun j hj =>
    mem_normalizer_inf (hJR hj)
      (mem_normalizer_centralizer (mem_normalizer_of_mem_centralizer' (hJI1 hj)))
  have hJodd : ∀ j ∈ J, Odd (orderOf j) := by
    have hev : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by have := hS.two_le; omega⟩
    have hodd : Odd (Nat.card J) := by
      rcases hJcard with e | e <;> rw [e]
      · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) (hev.pow_of_ne_zero
          two_ne_zero) odd_one
      · exact (Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one).pow
    intro j hj
    have := orderOf_dvd_natCard (⟨j, hj⟩ : J)
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hodd this
  have hJtriv : ∀ j ∈ J, (∀ x ∈ miyamotoF1G h L η t,
      j * x * j⁻¹ * x⁻¹ ∈ miyamotoFG h L η t Q) → j = 1 := by
    intro j hj hc
    have h1 := hS.mem_centralizer_V2_of_commutator_mem_F (hJF2 hj) (hJV hj) hc
    have h2 : j ∈ J ⊓ centralizer (𝓥 : Set G) := mem_inf.2 ⟨hj, h1⟩
    rw [hJCV] at h2
    exact h2
  obtain ⟨α₀, hα₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  set d₁ := miyamotoDHom h L η α₀ with hd₁
  have hd₁ord : orderOf d₁ = 2 ^ (2 * f) - 1 := by
    rw [hd₁, orderOf_injective _ (miyamotoDHom_injective h L η),
      orderOf_eq_card_of_forall_mem_zpowers hα₀, Nat.card_units, h.card_eq_sq, ← pow_mul,
      mul_comm]
  have hd₁D : d₁ ∈ miyamotoDG h L η := miyamotoDHom_mem h L η α₀
  have hd₁I : d₁ ∈ miyamotoIG h L η := (mem_inf.1 hd₁D).1
  have hd₁M : d₁ ∈ M := hNM (hS.DG_le_N1G hd₁D)
  have h16 : 16 ≤ 2 ^ (2 * f) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by have := hS.two_le; omega)
  have hd₁1 : d₁ ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hd₁ord
    omega
  have hd₁W : d₁ ∈ normalizer (𝓦 : Set G) := hS.DG_le_normalizer_W hd₁D
  have hk' : Nat.card k₂ = (2 ^ (2 * f)) ^ 2 := by
    rw [hk2', ← pow_mul]
    ring_nf
  have h8 : 8 ≤ Nat.card k₂ := by
    rw [hk']
    nlinarith
  have hW : Nat.card (𝓦 : Subgroup G) = Nat.card k₂ := by
    rw [hS.card_W, Nat.card_eq_fintype_card, hk₂]
    ring
  have hJinner : ∀ j ∈ J, ∃ τ ∈ M, τ * d₁ = d₁ * τ ∧ ∀ x ∈ M, j * x * j⁻¹ = τ * x * τ⁻¹ :=
    fun j hj => Common.exists_conj_eq_of_odd_of_mem_normalizer hk' h8 ψ hd₁M hd₁1 hd₁ord hWM hW
      hd₁W (hJodd j hj) (hJN hj) (hJW hj) (mem_centralizer_iff.1 (hJI hj) d₁ hd₁I).symm
  have hD₀D : miyamotoD0G h L η ≤ miyamotoDG h L η := hS.normOne_le_DG
  have hD₀M : miyamotoD0G h L η ≤ M := hD₀D.trans (hS.DG_le_N1G.trans hNM)
  have hJD₀ : J ≤ normalizer (miyamotoD0G h L η : Set G) := fun j hj =>
    mem_normalizer_of_mem_centralizer' (centralizer_le
      (SetLike.coe_subset_coe.2 (hD₀D.trans inf_le_left)) (hJI hj))
  have hD₀J : miyamotoD0G h L η ⊓ J = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxD, hxJ⟩ := mem_inf.1 hx
    exact hJtriv x hxJ fun y hy => hS.commutator_mem_F_of_mem_DG (hD₀D hxD) (hJE hxJ) hy
  have hYcard : Nat.card (miyamotoD0G h L η ⊔ J : Subgroup G) = (2 ^ f + 1) * Nat.card J := by
    have := card_sup_mul_card_inf_eq hJD₀
    rwa [hD₀J, card_bot, mul_one, hS.card_normOne] at this
  set d₁' : M := ⟨d₁, hd₁M⟩ with hd₁'
  have hd₁'1 : d₁' ≠ 1 := fun e => hd₁1 (congrArg Subtype.val e)
  have hd₁'q : d₁' ^ (Nat.card k₂ - 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_mk, hd₁ord, hk']
    simpa using Nat.sub_dvd_pow_sub_pow (x := 2 ^ (2 * f)) (y := 1) (n := 2)
  set T₁ := (centralizer (zpowers d₁' : Set M)).map M.subtype with hT₁
  have hT₁card : Nat.card T₁ = (2 ^ (2 * f)) ^ 2 - 1 := by
    rw [hT₁, card_map_of_injective M.subtype_injective,
      Common.card_centralizer_zpowers ψ hd₁'1 hd₁'q, hk']
  have hT₁N : T₁ ≤ normalizer (M : Set G) := (map_subtype_le _).trans le_normalizer
  have hYN : miyamotoD0G h L η ⊔ J ≤ normalizer (M : Set G) :=
    sup_le (hD₀M.trans le_normalizer) hJN
  have hinner : ∀ y ∈ miyamotoD0G h L η ⊔ J, ∃ τ ∈ T₁, ∀ x ∈ M,
      y * x * y⁻¹ = τ * x * τ⁻¹ := by
    intro y hy
    obtain ⟨d, hd, j, hj, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hJD₀ hy
    obtain ⟨τ, hτM, hτd, hτ⟩ := hJinner j hj
    have hdM : d ∈ M := hD₀M hd
    have hdd₁ : d * d₁ = d₁ * d := by
      obtain ⟨β, -, rfl⟩ := hd
      rw [hd₁, ← map_mul, ← map_mul, mul_comm]
    refine ⟨d * τ, ⟨⟨d * τ, mul_mem hdM hτM⟩, ?_, rfl⟩, fun x hx => ?_⟩
    · rw [SetLike.mem_coe, Common.centralizer_zpowers, mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hd₁']
      rw [mul_assoc, hτd, ← mul_assoc, hdd₁, mul_assoc]
    · rw [show d * j * x * (d * j)⁻¹ = d * (j * x * j⁻¹) * d⁻¹ by group, hτ x hx]
      group
  have hdvd : ¬ Nat.card (miyamotoD0G h L η ⊔ J : Subgroup G) ∣ Nat.card T₁ := by
    rw [hYcard, hT₁card, show 2 ^ (2 * f) = (2 ^ f) ^ 2 by rw [← pow_mul, mul_comm]]
    obtain ⟨hA, hB⟩ := not_dvd_sec3_15 hq4
    rcases hJcard with e | e <;> rw [e]
    · exact hA
    · exact hB
  obtain ⟨c, hcY, hc1, hcM⟩ :=
    Common.exists_ne_one_mem_centralizer_of_not_dvd hT₁N hYN hinner hdvd
  obtain ⟨d, hd, j, hj, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer' hJD₀ hcY
  set V := miyamotoF1G h L η t ⊓ centralizer ({d * j} : Set G) with hV
  have hZV : miyamotoZG h L η ≤ V := by
    intro z hz
    refine mem_inf.2 ⟨hS.E_le_F1 (hS.ZP_le_E hz), mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : z * d = d * z := mem_centralizer_iff.1 (hS.normOne_le_centralizer_ZG hd) z hz
    have h2 : z * j = j * z := mem_centralizer_iff.1 (hJE hj) z (hS.ZP_le_E hz)
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  have hMV : M ≤ normalizer (V : Set G) := by
    intro m hm
    refine mem_normalizer_inf ((hMH.trans inf_le_left) hm) (le_normalizer ?_)
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 hcM m hm
  have hV2 : IsPGroup 2 V :=
    hS.isPGroup_RG.to_le (inf_le_left.trans (le_sup_left.trans hS.P1_le_miyamotoRG))
  obtain ⟨e, he⟩ := hV2.exists_card_eq
  by_cases hlt : e < 2 * (4 * f)
  · have hMC := Common.le_centralizer_of_card_lt ψ hk2' (by have := hS.two_le; omega)
      (by omega) hMV he hlt
    exact hS.R1G_not_mem_centralizer_ZG
      (centralizer_le (SetLike.coe_subset_coe.2 hZV) (hMC (hNM hS.R1G_mem_N1)))
  push Not at hlt
  have hVF1 : V = miyamotoF1G h L η t := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [he, hS.card_F1]
    calc (2 ^ f) ^ 8 = 2 ^ (2 * (4 * f)) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hlt
  have hcF1 : ∀ x ∈ miyamotoF1G h L η t, x * (d * j) = (d * j) * x := fun x hx => by
    rw [← hVF1] at hx
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
  have hdE : d ∈ centralizer (miyamotoEG h L η Q : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hcF1 x (hS.E_le_F1 hx)
    have h2 : x * j = j * x := mem_centralizer_iff.1 (hJE hj) x hx
    have h3 : x * d * j = d * x * j := by
      calc x * d * j = x * (d * j) := by group
        _ = (d * j) * x := h1
        _ = d * (j * x) := by group
        _ = d * (x * j) := by rw [h2]
        _ = d * x * j := by group
    exact mul_right_cancel h3
  have hdD : d ∈ miyamotoDG h L η := hD₀D hd
  have hj1 : j = 1 := by
    refine hJtriv j hj fun x hx => ?_
    have hdx := hS.commutator_mem_F_of_mem_DG (inv_mem hdD) (inv_mem hdE) hx
    have hc := hcF1 x hx
    have e : j * x * j⁻¹ * x⁻¹ = d⁻¹ * x * d⁻¹⁻¹ * x⁻¹ := by
      rw [inv_inv]
      calc j * x * j⁻¹ * x⁻¹ = d⁻¹ * ((d * j) * x) * j⁻¹ * x⁻¹ := by group
        _ = d⁻¹ * (x * (d * j)) * j⁻¹ * x⁻¹ := by rw [hc]
        _ = d⁻¹ * x * d * x⁻¹ := by group
    rw [e]
    exact hdx
  apply hc1
  rw [hj1, mul_one] at hcM ⊢
  have hdC : (⟨d, hD₀M hd⟩ : M) ∈ center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (mem_centralizer_iff.1 hcM m m.2)
  rw [hZ, mem_bot] at hdC
  exact congrArg Subtype.val hdC

theorem sec3_15_iso (hS : Setting h L η t Q T) :
    ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
      ∃ (ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)) (α : miyamotoN1G h L η ≃* SL(2, k)),
        (∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
          ψ x = (α a, α a)) ∧
        ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
          ψ x = (y₁, y₂) → ψ y = (y₂, y₁) := by
  rcases hS.sec3_12_one_iso.or with h1 | ⟨k₂, _, _, hk₂, ψ, -, -⟩
  · exact h1
  · exact (hS.sec3_15 hk₂ ψ).elim

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
