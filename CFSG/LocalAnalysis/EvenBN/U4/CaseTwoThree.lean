module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoTwo
public import CFSG.LocalAnalysis.EvenBN.U4.TorusExclusion
public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoCenter

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup)
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem orderOf_coe_symm_inl {M : Subgroup G} {S : Type*} [Group S] (ψ : M ≃* S × S) (x : S) :
    orderOf ((ψ.symm (x, 1) : M) : G) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Prod.orderOf_mk, orderOf_one, Nat.lcm_one_right]

end Generic

noncomputable abbrev miyamotoJ2G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  miyamotoM2G h L η t Q ⊓ centralizer (miyamotoIN2G h L η : Set G)

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓥" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)

local notation "𝓜₂" => miyamotoM2G h L η t Q

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

theorem odd_orderOf_J2 (hS : Setting h L η t Q T)
    (hcard : Nat.card (miyamotoJ2G h L η t Q) = (2 ^ f - 1) ^ 2) {j : G}
    (hj : j ∈ miyamotoJ2G h L η t Q) : Odd (orderOf j) := by
  have hev : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by have := hS.two_le; omega⟩
  have hodd : Odd (Nat.card (miyamotoJ2G h L η t Q)) := by
    rw [hcard]
    exact (Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one).pow
  have := orderOf_dvd_natCard (⟨j, hj⟩ : miyamotoJ2G h L η t Q)
  rw [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat hodd this


variable {k : Type} [Field k]

theorem J2_two (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = 2 ^ f)
    {ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂) × SL(2, k₂)} {α₂ : miyamotoN2G h L η ≃* SL(2, k₂)}
    (hψα₂ : ∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
      ψ₂ x = (α₂ a, α₂ a)) :
    Nat.card (miyamotoJ2G h L η t Q) = (2 ^ f - 1) ^ 2 ∧
      miyamotoJ2G h L η t Q ≤ normalizer (𝓥 : Set G) ∧
      miyamotoJ2G h L η t Q ⊓ centralizer (𝓥 : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k₂ 2 := charP_of_card_eq_prime_pow (f := f) hk₂
  obtain ⟨-, -, hNM, -, hVM, -, -, -⟩ := hS.sec3_12_two
  obtain ⟨d, hd⟩ := (isCyclic_miyamotoIN2G h L η).exists_generator
  have hdM : (d : G) ∈ 𝓜₂ := hNM (mem_inf.1 d.2).2
  set d' : 𝓜₂ := ⟨d, hdM⟩ with hd'
  have hcardIN := card_miyamotoIN2G h L η
  have hq4 := hS.four_le
  have hJ : miyamotoJ2G h L η t Q =
      (centralizer (zpowers d' : Set 𝓜₂)).map (miyamotoM2G h L η t Q).subtype := by
    ext x
    constructor
    · rintro ⟨hxM, hxC⟩
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      show (⟨x, hxM⟩ : 𝓜₂) ∈ centralizer (zpowers d' : Set 𝓜₂)
      rw [Common.centralizer_zpowers, mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_iff.1 hxC d d.2).symm
    · rintro ⟨m, hm, rfl⟩
      have hm : m ∈ centralizer (zpowers d' : Set 𝓜₂) := hm
      rw [Common.centralizer_zpowers, mem_centralizer_singleton_iff] at hm
      refine ⟨m.2, mem_centralizer_iff.2 fun y hy => ?_⟩
      obtain ⟨n, hn⟩ := hd ⟨y, hy⟩
      have hyn : y = (d : G) ^ n := by
        have := congrArg Subtype.val hn
        simp only [SubgroupClass.coe_zpow] at this
        exact this.symm
      have hc : (d : G) * m = m * d := congrArg Subtype.val hm.symm
      rw [hyn]
      exact (Commute.zpow_left hc n).eq
  set g := α₂ ⟨d, (mem_inf.1 d.2).2⟩ with hg
  have hψd : ψ₂ d' = (g, g) := hψα₂ ⟨d, (mem_inf.1 d.2).2⟩ d' rfl
  have hd1 : d ≠ 1 := by
    intro e
    have hall : ∀ x : miyamotoIN2G h L η, x = 1 := fun x => by
      obtain ⟨n, hn⟩ := hd x
      rw [← hn]
      simp [e]
    have : Nat.card (miyamotoIN2G h L η) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨1⟩⟩
    omega
  have hg1 : g ≠ 1 := by
    intro e
    apply hd1
    have : (⟨d, (mem_inf.1 d.2).2⟩ : miyamotoN2G h L η) = 1 := by
      rw [← map_one α₂] at e
      exact α₂.injective e
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have hdpow : (d : G) ^ (2 ^ f - 1) = 1 := by
    have e : d ^ Nat.card (miyamotoIN2G h L η) = 1 := pow_card_eq_one'
    rw [hcardIN] at e
    simpa using congrArg Subtype.val e
  have hgpow : g ^ (Nat.card k₂ - 1) = 1 := by
    rw [Nat.card_eq_fintype_card, hk₂, hg, ← map_pow]
    have : (⟨d, (mem_inf.1 d.2).2⟩ : miyamotoN2G h L η) ^ (2 ^ f - 1) = 1 :=
      Subtype.ext (by simpa using hdpow)
    rw [this, map_one]
  set V' : Subgroup 𝓜₂ := (𝓥 : Subgroup G).subgroupOf 𝓜₂ with hV'
  have hV'card : Nat.card V' = Nat.card k₂ ^ 2 := by
    rw [hV', Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv, hS.card_V2,
      Nat.card_eq_fintype_card, hk₂]
  have hdV : d' ∈ normalizer (V' : Set 𝓜₂) := by
    rw [mem_normalizer_iff]
    intro v
    exact mem_normalizer_iff.1 (hS.IN2G_le_normalizer_V2 d.2) v
  obtain ⟨hN, hI⟩ := Common.centralizer_zpowers_le_normalizer_and_inf_prod ψ₂ hψd hg1 hgpow
    hV'card hdV
  refine ⟨?_, ?_, ?_⟩
  · rw [hJ, card_map_of_injective (miyamotoM2G h L η t Q).subtype_injective,
      Common.card_centralizer_zpowers_prod ψ₂ hψd hg1 hgpow, Nat.card_eq_fintype_card, hk₂]
  · rw [hJ]
    rintro _ ⟨j, hj, rfl⟩
    refine mem_normalizer_fintype fun v hv => ?_
    have hvM : v ∈ 𝓜₂ := hVM hv
    have hv' : (⟨v, hvM⟩ : 𝓜₂) ∈ V' := hv
    exact (mem_normalizer_iff.1 (hN hj) ⟨v, hvM⟩).1 hv'
  · rw [hJ]
    refine eq_bot_iff.2 ?_
    rintro _ ⟨⟨j, hj, rfl⟩, hjC⟩
    have hj' : j ∈ centralizer (zpowers d' : Set 𝓜₂) ⊓ centralizer (V' : Set 𝓜₂) := by
      refine mem_inf.2 ⟨hj, mem_centralizer_iff.2 fun v hv => Subtype.ext ?_⟩
      exact mem_centralizer_iff.1 hjC v hv
    rw [hI, mem_bot] at hj'
    rw [hj', map_one]
    exact one_mem _

theorem J2_le_centralizer_I (hS : Setting h L η t Q T) :
    miyamotoJ2G h L η t Q ≤ centralizer (miyamotoIG h L η : Set G) := by
  intro j hj
  rw [mem_centralizer_iff]
  intro i hi
  obtain ⟨i₂, hi₂, d, hd, rfl⟩ := hS.exists_I2_mul_IN2 hi
  have h1 : i₂ * j = j * i₂ := mem_centralizer_iff.1
    ((hS.sec3_12_two.1.trans inf_le_right) (mem_inf.1 hj).1) i₂ hi₂
  have h2 : d * j = j * d := mem_centralizer_iff.1 (mem_inf.1 hj).2 d hd
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem J2_le (hS : Setting h L η t Q T) (hJV : miyamotoJ2G h L η t Q ≤ normalizer (𝓥 : Set G)) :
    miyamotoJ2G h L η t Q ≤ centralizer (miyamotoEG h L η Q : Set G) ∧
      miyamotoJ2G h L η t Q ≤ normalizer (miyamotoF2G h L η t Q : Set G) ∧
      miyamotoJ2G h L η t Q ≤ normalizer (miyamotoRG h L η t Q : Set G) ∧
      miyamotoJ2G h L η t Q ≤ normalizer (miyamotoF1G h L η t : Set G) ∧
      miyamotoJ2G h L η t Q ≤ centralizer (miyamotoI1G h L η : Set G) ∧
      miyamotoJ2G h L η t Q ≤ normalizer (miyamotoM1G h L η t : Set G) ∧
      miyamotoJ2G h L η t Q ≤ normalizer (𝓦 : Set G) := by
  have hJM2 : miyamotoJ2G h L η t Q ≤ 𝓜₂ := inf_le_left
  have hJE := hJM2.trans hS.M2G_le_centralizer_E
  have hJF2 : miyamotoJ2G h L η t Q ≤ normalizer (miyamotoF2G h L η t Q : Set G) :=
    hJM2.trans (hS.sec3_12_two.1.trans inf_le_left)
  have hJR : miyamotoJ2G h L η t Q ≤ normalizer (miyamotoRG h L η t Q : Set G) := fun j hj => by
    rw [← hS.F2_sup_V2]
    exact mem_normalizer_sup (hJF2 hj) (hJV hj)
  have hJF1 := hJR.trans hS.normalizer_RG_le_normalizer_F1
  have hJI1 : miyamotoJ2G h L η t Q ≤ centralizer (miyamotoI1G h L η : Set G) :=
    hS.J2_le_centralizer_I.trans (centralizer_le (SetLike.coe_subset_coe.2 hS.I1G_le_IG))
  refine ⟨hJE, hJF2, hJR, hJF1, hJI1, fun j hj => hS.sec3_12_one.2.1 (mem_inf.2 ⟨hJF1 hj,
    hJI1 hj⟩), fun j hj => mem_normalizer_inf (hJR hj)
      (mem_normalizer_centralizer (mem_normalizer_of_mem_centralizer' (hJI1 hj)))⟩

theorem J2_le_normalizer_X [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}
    (hJV : miyamotoJ2G h L η t Q ≤ normalizer (𝓥 : Set G))
    (hcard : Nat.card (miyamotoJ2G h L η t Q) = (2 ^ f - 1) ^ 2) :
    miyamotoJ2G h L η t Q ≤ normalizer (prodFactorOne ψ : Set G) ∧
      miyamotoJ2G h L η t Q ≤ normalizer (prodFactorTwo ψ : Set G) := by
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have h4 : 4 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card, hk]
    have := hS.four_le
    nlinarith
  have hJN := (hS.J2_le hJV).2.2.2.2.2.1
  exact ⟨fun j hj => (mem_normalizer_prodFactor_of_odd h4 ψ (hJN hj)
    (hS.odd_orderOf_J2 hcard hj)).1, fun j hj => (mem_normalizer_prodFactor_of_odd h4 ψ (hJN hj)
    (hS.odd_orderOf_J2 hcard hj)).2⟩

theorem exists_torus_X1 [Fintype k] (hS : Setting h L η t Q T)
    {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)} {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a)) :
    ∃ m : miyamotoM1G h L η t, (m : G) ∈ miyamotoDG h L η ∧
      orderOf (compOne ψ m) = 2 ^ f - 1 ∧
      compOne ψ m ∈ normalizer ((𝓦 ⊓ prodFactorOne ψ : Subgroup G) : Set G) := by
  have : Finite K := h.finite
  have hN1M : miyamotoN1G h L η ≤ miyamotoM1G h L η t := hS.sec3_12_one.2.2.1
  obtain ⟨α₀, hα₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hα₀ord : orderOf α₀ = (2 ^ f - 1) * (2 ^ f + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hα₀, Nat.card_units, h.card_eq_sq]
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = m + 1 := ⟨2 ^ f - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    rw [hm, Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 1 + 1) + 1 by ring, Nat.add_sub_cancel]
  set α₁ := α₀ ^ (2 ^ f + 1) with hα₁
  have hα₁ord : orderOf α₁ = 2 ^ f - 1 := by
    rw [hα₁, orderOf_pow' _ (by positivity), hα₀ord, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (by positivity)]
  have hD : miyamotoDHom h L η α₁ ∈ miyamotoDG h L η := miyamotoDHom_mem h L η α₁
  set m : miyamotoM1G h L η t := ⟨miyamotoDHom h L η α₁, hN1M (hS.DG_le_N1G hD)⟩ with hm
  refine ⟨m, hD, ?_, ?_⟩
  · rw [compOne_apply, orderOf_coe_symm_inl, hψA ⟨_, hS.DG_le_N1G hD⟩ m rfl, MulEquiv.orderOf_eq,
      Subgroup.orderOf_mk, orderOf_injective _ (miyamotoDHom_injective h L η), hα₁ord]
  · have hnorm : ∀ m' : miyamotoM1G h L η t, (m' : G) ∈ normalizer (𝓦 : Set G) →
        ∀ w ∈ 𝓦 ⊓ prodFactorOne ψ, compOne ψ m' * w * (compOne ψ m')⁻¹ ∈ 𝓦 ⊓ prodFactorOne ψ := by
      intro m' hm' w hw
      rw [← conj_eq_conj_compOne m' (mem_inf.1 hw).2]
      exact mem_inf.2 ⟨(mem_normalizer_iff.1 hm' w).1 (mem_inf.1 hw).1,
        (mem_normalizer_iff.1 (Common.le_normalizer_prodFactorOne ψ m'.2) w).1 (mem_inf.1 hw).2⟩
    refine Common.mem_normalizer_of_conj_mem (hnorm m (hS.DG_le_normalizer_W hD)) fun w hw => ?_
    have := hnorm m⁻¹ (inv_mem (hS.DG_le_normalizer_W hD)) w hw
    rw [map_inv, inv_inv] at this
    rw [inv_inv]
    exact this

theorem exists_J2_centralizer_X1 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)} {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hJV : miyamotoJ2G h L η t Q ≤ normalizer (𝓥 : Set G))
    (hcard : Nat.card (miyamotoJ2G h L η t Q) = (2 ^ f - 1) ^ 2) :
    ∃ j ∈ miyamotoJ2G h L η t Q, j ≠ 1 ∧ j ∈ centralizer (prodFactorOne ψ : Set G) := by
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have hq4 := hS.four_le
  obtain ⟨m, hmD, hord, hcW⟩ := hS.exists_torus_X1 hψA
  set c := compOne ψ m with hcdef
  have hcX : c ∈ prodFactorOne ψ := compOne_mem m
  have hc1 : c ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hord
    omega
  obtain ⟨hJX1, hJX2⟩ := hS.J2_le_normalizer_X hk hJV hcard
  have hJW := (hS.J2_le hJV).2.2.2.2.2.2
  set c₂ : G := ((ψ.symm (1, (ψ m).2) : miyamotoM1G h L η t) : G) with hc₂
  have hc₂X : c₂ ∈ prodFactorTwo ψ := Common.symm_inr_mem_prodFactorTwo ψ _
  have hm : (m : G) = c * c₂ := by
    rw [hcdef, compOne_apply, hc₂, ← coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      Prod.mk.eta, MulEquiv.symm_apply_apply]
  have hJc : ∀ j ∈ miyamotoJ2G h L η t Q, j * c = c * j := by
    intro j hj
    have hjm : j * m = m * j :=
      (mem_centralizer_iff.1 (hS.J2_le_centralizer_I hj) m (mem_inf.1 hmD).1).symm
    have h1 : j * c * j⁻¹ ∈ prodFactorOne ψ := (mem_normalizer_iff.1 (hJX1 hj) c).1 hcX
    have h2 : j * c₂ * j⁻¹ ∈ prodFactorTwo ψ := (mem_normalizer_iff.1 (hJX2 hj) c₂).1 hc₂X
    have h3 : (j * c * j⁻¹) * (j * c₂ * j⁻¹) = c * c₂ := by
      rw [← hm, show j * c * j⁻¹ * (j * c₂ * j⁻¹) = j * (c * c₂) * j⁻¹ by group, ← hm, hjm,
        mul_inv_cancel_right]
    have h4 : c⁻¹ * (j * c * j⁻¹) = c₂ * (j * c₂ * j⁻¹)⁻¹ := by
      calc c⁻¹ * (j * c * j⁻¹) = c⁻¹ * ((j * c * j⁻¹) * (j * c₂ * j⁻¹)) * (j * c₂ * j⁻¹)⁻¹ := by
            group
        _ = c₂ * (j * c₂ * j⁻¹)⁻¹ := by rw [h3]; group
    have h5 : c⁻¹ * (j * c * j⁻¹) ∈ prodFactorOne ψ ⊓ prodFactorTwo ψ :=
      mem_inf.2 ⟨mul_mem (inv_mem hcX) h1, h4 ▸ mul_mem hc₂X (inv_mem h2)⟩
    rw [Common.prodFactorOne_inf_prodFactorTwo, mem_bot] at h5
    have h6 : j * c * j⁻¹ = c := by
      calc j * c * j⁻¹ = c * (c⁻¹ * (j * c * j⁻¹)) := by group
        _ = c := by rw [h5, mul_one]
    calc j * c = (j * c * j⁻¹) * j := by group
      _ = c * j := by rw [h6]
  have hk' : Nat.card k = (2 ^ f) ^ 2 := by rw [Nat.card_eq_fintype_card, hk]
  have h8 : 8 ≤ Nat.card k := by rw [hk']; nlinarith
  have hW1card : Nat.card (𝓦 ⊓ prodFactorOne ψ : Subgroup G) = Nat.card k := by
    rw [(hS.W_eq_sup (ψ := ψ) hk).2.1, hk']
  have hinner : ∀ j ∈ miyamotoJ2G h L η t Q, ∃ τ ∈ prodFactorOne ψ, τ * c = c * τ ∧
      ∀ x ∈ prodFactorOne ψ, j * x * j⁻¹ = τ * x * τ⁻¹ := fun j hj =>
    Common.exists_conj_eq_of_odd_of_mem_normalizer hk' h8 (Common.prodFactorOneEquiv ψ) hcX hc1
      hord inf_le_right hW1card hcW (hS.odd_orderOf_J2 hcard hj) (hJX1 hj)
      (mem_normalizer_inf (hJW hj) (hJX1 hj)) (hJc j hj)
  set c' : prodFactorOne ψ := ⟨c, hcX⟩ with hc'
  set Tt : Subgroup G :=
    (centralizer (zpowers c' : Set (prodFactorOne ψ))).map (prodFactorOne ψ).subtype with hTt
  have hc'1 : c' ≠ 1 := fun e => hc1 (congrArg Subtype.val e)
  have hc'pow : c' ^ (Nat.card k - 1) = 1 := by
    have hdvd : 2 ^ f - 1 ∣ Nat.card k - 1 := by
      rw [hk']
      obtain ⟨n, hn⟩ : ∃ n, 2 ^ f = n + 1 :=
        ⟨2 ^ f - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
      refine ⟨2 ^ f + 1, ?_⟩
      rw [hn, Nat.add_sub_cancel, show (n + 1) ^ 2 = n * (n + 1 + 1) + 1 by ring,
        Nat.add_sub_cancel]
    obtain ⟨e, he⟩ := hdvd
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, he, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    rfl
  have hTcard : Nat.card Tt = Nat.card k - 1 := by
    rw [hTt, card_map_of_injective (prodFactorOne ψ).subtype_injective,
      Common.card_centralizer_zpowers (Common.prodFactorOneEquiv ψ) hc'1 hc'pow]
  have hinner' : ∀ j ∈ miyamotoJ2G h L η t Q, ∃ τ ∈ Tt,
      ∀ x ∈ prodFactorOne ψ, j * x * j⁻¹ = τ * x * τ⁻¹ := by
    intro j hj
    obtain ⟨τ, hτX, hτc, hτ⟩ := hinner j hj
    refine ⟨τ, ⟨⟨τ, hτX⟩, ?_, rfl⟩, hτ⟩
    show (⟨τ, hτX⟩ : prodFactorOne ψ) ∈ centralizer (zpowers c' : Set (prodFactorOne ψ))
    rw [Common.centralizer_zpowers, mem_centralizer_singleton_iff]
    exact Subtype.ext hτc
  have hdvd : ¬ Nat.card (miyamotoJ2G h L η t Q) ∣ Nat.card Tt := by
    rw [hcard, hTcard, hk']
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ f = n + 1 := ⟨2 ^ f - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    rw [hn, Nat.add_sub_cancel, show (n + 1) ^ 2 - 1 = n * (n + 2) by
      rw [show (n + 1) ^ 2 = n * (n + 2) + 1 by ring, Nat.add_sub_cancel]]
    intro hd
    have hn0 : 0 < n := by omega
    rw [sq] at hd
    have h1 : n ∣ n + 2 := Nat.dvd_of_mul_dvd_mul_left hn0 hd
    have h2 : n ∣ 2 := (Nat.dvd_add_right (dvd_refl n)).1 h1
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨j, hj, hj1, hjC⟩ := Common.exists_ne_one_mem_centralizer_of_not_dvd
    (fun x hx => le_normalizer (map_subtype_le _ hx)) hJX1 hinner' hdvd
  exact ⟨j, hj, hj1, hjC⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
