module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Table
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611F

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem card_modEq_fixed_three {α : Type*} [Finite α] (σ : Equiv.Perm α) (h3 : σ ^ 3 = 1) :
    Nat.card α ≡ Nat.card (Function.fixedPoints σ) [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have := Fintype.ofFinite α
  let f : Function.End α := ⇑σ
  have hpow : ∀ k : ℕ, f ^ k = (⇑(σ ^ k) : Function.End α) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by
    rw [pow_one, hpow, h3]; rfl)
  have e : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  have e2 : Nat.card (Function.fixedPoints σ) = Fintype.card ↑(Function.fixedPoints f) := by
    rw [Nat.card_eq_fintype_card]
  rw [e, e2]
  exact h

theorem ncard_modEq_fixed_conj_three {G : Type*} [Group G] {O : Set G} (hO : O.Finite) {y : G}
    (hy3 : y ^ 3 = 1) (h1 : ∀ u ∈ O, y * u * y⁻¹ ∈ O) (h2 : ∀ u ∈ O, y⁻¹ * u * y ∈ O) :
    O.ncard ≡ {u | u ∈ O ∧ y * u * y⁻¹ = u}.ncard [MOD 3] := by
  classical
  haveI : Finite ↥O := hO.to_subtype
  let σ : Equiv.Perm ↥O :=
    { toFun := fun u => ⟨y * u * y⁻¹, h1 u u.2⟩
      invFun := fun u => ⟨y⁻¹ * u * y, h2 u u.2⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group) }
  have hσk : ∀ (k : ℕ) (u : ↥O), (((σ ^ k) u : ↥O) : G) = y ^ k * u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show y ^ k * (y * (u : G) * y⁻¹) * (y ^ k)⁻¹ = y ^ (k + 1) * u * (y ^ (k + 1))⁻¹
      rw [pow_succ]; group
  have hσ3 : σ ^ 3 = 1 := by
    ext u
    rw [hσk, hy3]
    simp
  have hmod := card_modEq_fixed_three σ hσ3
  have hfix : {u | u ∈ O ∧ y * u * y⁻¹ = u} = Subtype.val '' (Function.fixedPoints σ) := by
    ext u
    constructor
    · rintro ⟨hu, hfu⟩
      exact ⟨⟨u, hu⟩, Subtype.ext hfu, rfl⟩
    · rintro ⟨⟨u, hu⟩, hfu, rfl⟩
      exact ⟨hu, congrArg Subtype.val hfu⟩
  rw [hfix, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hmod
  exact hmod

theorem comm_of_card_center_eight {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 8)
    (hZ : 4 ≤ Nat.card (Subgroup.center K)) (a b : K) : a * b = b * a := by
  have hmul : Nat.card (Subgroup.center K) * (Subgroup.center K).index = Nat.card K :=
    Subgroup.card_mul_index (H := Subgroup.center K)
  rw [hK] at hmul
  have hidx : (Subgroup.center K).index ≤ 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hne0 : (Subgroup.center K).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    omega
  rcases (show (Subgroup.center K).index = 1 ∨ (Subgroup.center K).index = 2 by omega) with
    h1 | h2
  · have htop : Subgroup.center K = ⊤ := (Subgroup.index_eq_one (H := Subgroup.center K)).1 h1
    have ha : a ∈ Subgroup.center K := by
      rw [htop]
      exact Subgroup.mem_top a
    exact ((Subgroup.mem_center_iff.1 ha) b).symm
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq : Nat.card (K ⧸ Subgroup.center K) = 2 := h2
    haveI : IsCyclic (K ⧸ Subgroup.center K) := isCyclic_of_prime_card hq
    exact (isMulCommutative_of_isCyclic_quotient_center_self (G := K)).is_comm.comm a b

theorem four_le_card_center_of_invol {K : Type*} [Group K] [Finite K] {u v : K}
    (hu : u * u = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hcu : u ∈ Subgroup.center K) (hcv : v ∈ Subgroup.center K) :
    4 ≤ Nat.card (Subgroup.center K) := by
  have hcuv : u * v ∈ Subgroup.center K := mul_mem hcu hcv
  have hsub : ({1, u, v, u * v} : Set K) ⊆ (Subgroup.center K : Set K) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact one_mem _
    · exact hcu
    · exact hcv
    · exact hcuv
  have hne1u : (1 : K) ≠ u := fun e => hu1 e.symm
  have hne1v : (1 : K) ≠ v := fun e => hv1 e.symm
  have hne1uv : (1 : K) ≠ u * v := by
    intro e
    apply huv
    calc u = u * (u * v) := by rw [← e, mul_one]
      _ = u * u * v := (mul_assoc u u v).symm
      _ = v := by rw [hu, one_mul]
  have hne_u_uv : u ≠ u * v := by
    intro e
    apply hv1
    have : u * v = u * 1 := by
      rw [mul_one]
      exact e.symm
    exact mul_left_cancel this
  have hne_v_uv : v ≠ u * v := by
    intro e
    apply hu1
    have : u * v = 1 * v := by
      rw [one_mul]
      exact e.symm
    exact mul_right_cancel this
  have hcard4 : ({1, u, v, u * v} : Set K).ncard = 4 := by
    have n1 : u ∉ ({v, u * v} : Set K) := by simp [huv, hne_u_uv]
    have n2 : (1 : K) ∉ ({u, v, u * v} : Set K) := by simp [hne1u, hne1v, hne1uv]
    have e1 : ({v, u * v} : Set K).ncard = 2 := Set.ncard_pair hne_v_uv
    have e2 : ({u, v, u * v} : Set K).ncard = 3 := by
      have := Set.ncard_insert_of_notMem n1 (Set.toFinite _)
      omega
    have e3 : ({1, u, v, u * v} : Set K).ncard = ({u, v, u * v} : Set K).ncard + 1 :=
      Set.ncard_insert_of_notMem n2 (Set.toFinite _)
    omega
  have hle : ({1, u, v, u * v} : Set K).ncard ≤ (Subgroup.center K : Set K).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hNC : Nat.card (Subgroup.center K) = (Subgroup.center K : Set K).ncard :=
    Nat.card_coe_set_eq _
  omega

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem conj_mem_E2 {b u : G} (hb : b ∈ L ⊓ centralizer ({t} : Set G)) (hu : u ∈ E2 E t) :
    b * u * b⁻¹ ∈ E2 E t := by
  have hu' : u ∈ E ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ t := hu
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu'
  have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 hb.2
  show b * u * b⁻¹ ∈ E ∧ (b * u * b⁻¹) * (b * u * b⁻¹) = 1 ∧ b * u * b⁻¹ ≠ 1 ∧ b * u * b⁻¹ ≠ t
  refine ⟨h.W_norm_E hb hu1, ?_, ?_, ?_⟩
  · calc b * u * b⁻¹ * (b * u * b⁻¹) = b * (u * u) * b⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  · intro e
    apply hu3
    calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
      _ = 1 := by rw [e]; group
  · intro e
    apply hu4
    have htb : t * b = b * t := hbt.symm
    calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
      _ = b⁻¹ * t * b := by rw [e]
      _ = b⁻¹ * (t * b) := by group
      _ = b⁻¹ * (b * t) := by rw [htb]
      _ = t := by group

theorem exists_fixed_E2 : ∃ d ∈ E2 E t, β * d * β⁻¹ = d := by
  have hβL : β ∈ L ⊓ centralizer ({t} : Set G) := h.B_le_W h.ob.beta_mem
  have hβ3 : β ^ 3 = 1 := by
    rw [← h.ob.beta_order]
    exact pow_orderOf_eq_one β
  have h1 : ∀ u ∈ E2 E t, β * u * β⁻¹ ∈ E2 E t := fun u hu => h.conj_mem_E2 hβL hu
  have h2 : ∀ u ∈ E2 E t, β⁻¹ * u * β ∈ E2 E t := fun u hu => by
    have := h.conj_mem_E2 (inv_mem hβL) hu
    rwa [inv_inv] at this
  have hmod := ncard_modEq_fixed_conj_three (Set.toFinite (E2 E t)) hβ3 h1 h2
  have hE2c : (E2 E t).ncard = 10 := h.ef.card_two
  rw [hE2c] at hmod
  have hne : {u | u ∈ E2 E t ∧ β * u * β⁻¹ = u}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    rw [h0] at hmod
    norm_num [Nat.ModEq] at hmod
  obtain ⟨d, hdE2, hdfix⟩ := hne
  exact ⟨d, hdE2, hdfix⟩

theorem exists_noncomm_partner (hcard : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8)
    {d : G} (hdD : d ∈ E ⊓ centralizer ({β} : Set G)) (hdd : d * d = 1) (hd1 : d ≠ 1)
    (hdt : d ≠ t) (hβt : β * t = t * β)
    (hab : ∃ a ∈ E ⊓ centralizer ({β} : Set G), ∃ b ∈ E ⊓ centralizer ({β} : Set G),
      a * b ≠ b * a) :
    ∃ d' ∈ E ⊓ centralizer ({β} : Set G), d' * d ≠ d * d' := by
  by_contra hno
  push Not at hno
  obtain ⟨a, ha, b, hb, hab⟩ := hab
  have htD : t ∈ E ⊓ centralizer ({β} : Set G) :=
    ⟨h.t_mem_E, mem_centralizer_singleton_iff.2 hβt.symm⟩
  have hucen : (⟨t, htD⟩ : ↥(E ⊓ centralizer ({β} : Set G))) ∈
      Subgroup.center ↥(E ⊓ centralizer ({β} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact h.t_comm_E _ g.2.1
  have hvcen : (⟨d, hdD⟩ : ↥(E ⊓ centralizer ({β} : Set G))) ∈
      Subgroup.center ↥(E ⊓ centralizer ({β} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hno _ g.2
  have hu_sq : (⟨t, htD⟩ : ↥(E ⊓ centralizer ({β} : Set G))) * ⟨t, htD⟩ = 1 :=
    Subtype.ext (by simpa using h.t_sq)
  have hu1 : (⟨t, htD⟩ : ↥(E ⊓ centralizer ({β} : Set G))) ≠ 1 :=
    fun e => h.t_ne (by simpa using congrArg Subtype.val e)
  have hv1 : (⟨d, hdD⟩ : ↥(E ⊓ centralizer ({β} : Set G))) ≠ 1 :=
    fun e => hd1 (by simpa using congrArg Subtype.val e)
  have huv : (⟨t, htD⟩ : ↥(E ⊓ centralizer ({β} : Set G))) ≠ ⟨d, hdD⟩ := by
    intro e
    have ht_d : t = d := by simpa using congrArg Subtype.val e
    exact hdt ht_d.symm
  have hZ := four_le_card_center_of_invol hu_sq hu1 hv1 huv hucen hvcen
  have hcomm := comm_of_card_center_eight hcard hZ ⟨a, ha⟩ ⟨b, hb⟩
  have hc' := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul] at hc'
  exact hab hc'

theorem exists_invol_pair_inf_centralizer
    (hcard : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8) :
    ∃ d₁ ∈ E ⊓ centralizer ({β} : Set G), ∃ d₂ ∈ E ⊓ centralizer ({β} : Set G),
      d₁ * d₁ = 1 ∧ d₂ * d₂ = 1 ∧ d₁ * d₂ ≠ d₂ * d₁ := by
  have hβB : β ∈ B := h.ob.beta_mem
  have hβt : β * t = t * β := mem_centralizer_singleton_iff.1 (h.ob.B_cent hβB)
  have hab := exists_noncomm_inf_centralizer h.wf (h.ob.B_le hβB) hβt h.ob.beta_order
  obtain ⟨d, hdE2, hdfix⟩ := h.exists_fixed_E2
  have hdD : d ∈ E ⊓ centralizer ({β} : Set G) := by
    refine ⟨hdE2.1, mem_centralizer_singleton_iff.2 ?_⟩
    calc d * β = (β * d * β⁻¹) * β := by rw [hdfix]
      _ = β * d := by group
  have hdd : d * d = 1 := hdE2.2.1
  have hd1 : d ≠ 1 := hdE2.2.2.1
  have hdt : d ≠ t := hdE2.2.2.2
  obtain ⟨d', hd'D, hd'd⟩ := h.exists_noncomm_partner hcard hdD hdd hd1 hdt hβt hab
  rcases h.ef.sq d' hd'D.1 with hd'2 | hd'2
  · exact ⟨d, hdD, d', hd'D, hdd, hd'2, fun e => hd'd e.symm⟩
  ·
    have hdd' : d * d' = t * (d' * d) := by
      rcases h.E_comm d hdD.1 d' hd'D.1 with h1 | h1
      · exact absurd h1 (fun e => hd'd e.symm)
      · exact h1
    have hd'd2 : d' * d = t * (d * d') := by
      rw [hdd']
      rw [← mul_assoc, h.t_sq, one_mul]
    have hsq2 : (d * d') * (d * d') = 1 := by
      calc (d * d') * (d * d') = d * (d' * d) * d' := by group
        _ = d * (t * (d * d')) * d' := by rw [hd'd2]
        _ = (d * t) * (d * d') * d' := by group
        _ = (t * d) * (d * d') * d' := by rw [h.t_comm_E d hdD.1]
        _ = t * ((d * d) * (d' * d')) := by group
        _ = t * t := by rw [hdd, hd'2, one_mul]
        _ = 1 := h.t_sq
    have hne : d * (d * d') ≠ d * d' * d := by
      intro e
      apply hd'd
      calc d' * d = (d * d) * d' * d := by rw [hdd, one_mul]
        _ = d * (d * d') * d := by group
        _ = d * d' * d * d := by rw [e]
        _ = d * d' * (d * d) := by group
        _ = d * d' := by rw [hdd, mul_one]
    exact ⟨d, hdD, d * d', mul_mem hdD hd'D, hdd, hsq2, hne⟩

theorem outerPairing_of_noTable {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hcard : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8)
    (hl96 : ∃ hz : z ∈ centralizer ({β} : Set G),
      Lemma96Conclusion ↥(centralizer ({β} : Set G))
        (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G)))))
    (hNT : OuterNoTable) : OuterPairing h hα := by
  obtain ⟨ε, hε, hp⟩ := h.pairing_structure hα hF hM
  rcases hε with hε1 | hεt
  ·
    rw [hε1] at hp
    unfold OuterPairing
    intro x hx y hy w w' hw hw'
    obtain ⟨h1, h2⟩ := hp x hx y hy w w' hw hw'
    exact ⟨by rwa [mul_one] at h1, by rwa [iota_one_left] at h2⟩
  ·
    exfalso
    rw [hεt] at hp
    obtain ⟨hz, hl⟩ := hl96
    obtain ⟨d₁, hd₁, d₂, hd₂, hd₁d₁, hd₂d₂, hne⟩ := h.exists_invol_pair_inf_centralizer hcard
    have hB : β ∈ B := h.ob.beta_mem
    have hβ3 : orderOf β = 3 := h.ob.beta_order
    have hfix : ∀ d ∈ E ⊓ centralizer ({β} : Set G), β * d * β⁻¹ = d := by
      intro d hd
      have hc : d * β = β * d := mem_centralizer_singleton_iff.1 hd.2
      calc β * d * β⁻¹ = d * β * β⁻¹ := by rw [← hc]
        _ = d := by group
    obtain ⟨g₁, hg₁, hg₁β⟩ := h.exists_fixed_lift hα hF hM hB hβ3 hd₁.1 (hfix d₁ hd₁)
    obtain ⟨g₂, hg₂, hg₂β⟩ := h.exists_fixed_lift hα hF hM hB hβ3 hd₂.1 (hfix d₂ hd₂)
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
    have hd12 : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ = t := by
      have h1 : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ ≠ 1 := fun h1 => hne (cmt_eq_one_iff.1 h1)
      exact (h.oe.econfig.comm d₁ hd₁.1 d₂ hd₂.1).resolve_left h1
    have hd21 : d₂ * d₁ * d₂⁻¹ * d₁⁻¹ = t := by
      have : d₂ * d₁ * d₂⁻¹ * d₁⁻¹ = (d₁ * d₂ * d₁⁻¹ * d₂⁻¹)⁻¹ := by group
      rw [this, hd12, hti]
    have P12 := hp d₁ hd₁.1 d₂ hd₂.1 g₁ g₂ hg₁ hg₂
    have P21 := hp d₂ hd₂.1 d₁ hd₁.1 g₂ g₁ hg₂ hg₁
    have P11 := hp d₁ hd₁.1 d₁ hd₁.1 g₁ g₁ hg₁ hg₁
    have P22 := hp d₂ hd₂.1 d₂ hd₂.1 g₂ g₂ hg₂ hg₂
    have e11 : d₁ * d₁ * d₁⁻¹ * d₁⁻¹ = 1 := by group
    have e22 : d₂ * d₂ * d₂⁻¹ * d₂⁻¹ = 1 := by group
    have hzαt : z * (α * t) * z⁻¹ = α := by
      calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
        _ = α * t * t := by rw [h.z_conj_alpha hα, h.z_conj_t]
        _ = α := by rw [mul_assoc, h.t_sq, mul_one]
    have T12 : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = α * t := by
      have := P12.1
      rwa [hd12, iota_of_ne h.t_ne] at this
    have T34 : (z * g₁ * z⁻¹) * (z * g₂ * z⁻¹) * (z * g₁ * z⁻¹)⁻¹ * (z * g₂ * z⁻¹)⁻¹ = α := by
      have : (z * g₁ * z⁻¹) * (z * g₂ * z⁻¹) * (z * g₁ * z⁻¹)⁻¹ * (z * g₂ * z⁻¹)⁻¹ =
          z * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * z⁻¹ := by group
      rw [this, T12, hzαt]
    have T14 : g₁ * (z * g₂ * z⁻¹) * g₁⁻¹ * (z * g₂ * z⁻¹)⁻¹ = t := by
      have := P12.2
      rwa [hd12, iota_of_ne h.t_ne] at this
    have T23 : g₂ * (z * g₁ * z⁻¹) * g₂⁻¹ * (z * g₁ * z⁻¹)⁻¹ = t := by
      have := P21.2
      rwa [hd21, iota_of_ne h.t_ne] at this
    have T13 : g₁ * (z * g₁ * z⁻¹) = (z * g₁ * z⁻¹) * g₁ := by
      have := P11.2
      rw [e11, iota_one] at this
      exact cmt_eq_one_iff.1 this
    have T24 : g₂ * (z * g₂ * z⁻¹) = (z * g₂ * z⁻¹) * g₂ := by
      have := P22.2
      rw [e22, iota_one] at this
      exact cmt_eq_one_iff.1 this
    have hzβ : Commute z β := mem_centralizer_singleton_iff.1 hz
    have hzβ' : Commute z⁻¹ β := hzβ.inv_left
    have hg₁c : Commute g₁ β := hg₁β
    have hg₂c : Commute g₂ β := hg₂β
    have hh₁c : Commute (z * g₁ * z⁻¹) β := (hzβ.mul_left hg₁c).mul_left hzβ'
    have hh₂c : Commute (z * g₂ * z⁻¹) β := (hzβ.mul_left hg₂c).mul_left hzβ'
    have hαβ : Commute α β := (h.BS β hB α hα.mem).symm
    have htβ : Commute t β := (mem_centralizer_singleton_iff.1 (h.ob.B_cent hB)).symm
    have hQg₁ := hg₁.1
    have hQg₂ := hg₂.1
    have hQh₁ := h.z_norm_Qs hα hQg₁
    have hQh₂ := h.z_norm_Qs hα hQg₂
    obtain ⟨z', hz'⟩ : ∃ z' : ↥(centralizer ({β} : Set G)), (z' : G) = z := ⟨⟨z, hz⟩, rfl⟩
    obtain ⟨α', hα'⟩ : ∃ α' : ↥(centralizer ({β} : Set G)), (α' : G) = α :=
      ⟨⟨α, mem_centralizer_singleton_iff.2 hαβ.eq⟩, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t' : ↥(centralizer ({β} : Set G)), (t' : G) = t :=
      ⟨⟨t, mem_centralizer_singleton_iff.2 htβ.eq⟩, rfl⟩
    obtain ⟨g₁', hg₁'⟩ : ∃ g₁' : ↥(centralizer ({β} : Set G)), (g₁' : G) = g₁ :=
      ⟨⟨g₁, mem_centralizer_singleton_iff.2 hg₁c.eq⟩, rfl⟩
    obtain ⟨g₂', hg₂'⟩ : ∃ g₂' : ↥(centralizer ({β} : Set G)), (g₂' : G) = g₂ :=
      ⟨⟨g₂, mem_centralizer_singleton_iff.2 hg₂c.eq⟩, rfl⟩
    obtain ⟨h₁', hh₁'⟩ : ∃ h₁' : ↥(centralizer ({β} : Set G)), (h₁' : G) = z * g₁ * z⁻¹ :=
      ⟨⟨z * g₁ * z⁻¹, mem_centralizer_singleton_iff.2 hh₁c.eq⟩, rfl⟩
    obtain ⟨h₂', hh₂'⟩ : ∃ h₂' : ↥(centralizer ({β} : Set G)), (h₂' : G) = z * g₂ * z⁻¹ :=
      ⟨⟨z * g₂ * z⁻¹, mem_centralizer_singleton_iff.2 hh₂c.eq⟩, rfl⟩
    have hcomm_Q : ∀ c : ↥(centralizer ({β} : Set G)),
        (c : G) ∈ Fsub h hα ⊓ centralizer ({α} : Set G) →
          c * α' = α' * c ∧ c * t' = t' * c := by
      intro c hc
      have hA : (c : G) * α = α * c :=
        ((h.Zg_cent_Q hα (h.alpha_mem_Zg hα)).2 (c : G) hc).symm
      have hT : (c : G) * t = t * c :=
        ((h.Zg_cent_Q hα (h.t_mem_Zg hα)).2 (c : G) hc).symm
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · simp only [Subgroup.coe_mul, hα']
        exact hA
      · simp only [Subgroup.coe_mul, ht']
        exact hT
    have hgsq : ∀ {d g : G}, d ∈ E → d * d = 1 → IsLift h hα α d g →
        g * g = 1 ∨ g * g = t := by
      intro d g hd hdd hg
      have e := h.sq_lift_rel hα hd hg
      rw [hdd] at e
      rcases h.QF_sq hα hg.1 with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exfalso
        have h2 := (h.sq_conj_val hα).2 (Or.inl h1)
        exact h.t_ne (h2.symm.trans e.symm)
      · exfalso
        have h2 := (h.sq_conj_val hα).2 (Or.inr h1)
        exact h.t_ne (h2.symm.trans e.symm)
    have hg₁sq' : g₁' * g₁' = 1 ∨ g₁' * g₁' = t' := by
      rcases hgsq hd₁.1 hd₁d₁ hg₁ with e | e
      · exact Or.inl (Subtype.ext (by simpa [hg₁'] using e))
      · exact Or.inr (Subtype.ext (by simpa [hg₁', ht'] using e))
    have hg₂sq' : g₂' * g₂' = 1 ∨ g₂' * g₂' = t' := by
      rcases hgsq hd₂.1 hd₂d₂ hg₂ with e | e
      · exact Or.inl (Subtype.ext (by simpa [hg₂'] using e))
      · exact Or.inr (Subtype.ext (by simpa [hg₂', ht'] using e))
    have htable : OuterTable z' α' t' g₁' g₂' h₁' h₂' := by
      have hQ2 : IsPGroup 2 (Fsub h hα) := h.F_pgroup hM hα
      have hQβ : IsPGroup 2 ((Fsub h hα ⊓ centralizer ({α} : Set G)).subgroupOf
          (centralizer ({β} : Set G))) := (hQ2.to_le inf_le_left).comap_subtype
      unfold OuterTable
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply Subtype.ext
        simpa [hz'] using h.z_sq
      · apply Subtype.ext
        simpa [hα'] using hα.sq
      · apply Subtype.ext
        simpa [ht'] using h.t_sq
      · intro e
        exact hα.ne_one (by simpa [hα'] using congrArg Subtype.val e)
      · intro e
        exact h.t_ne (by simpa [ht'] using congrArg Subtype.val e)
      · intro e
        exact hα.ne_t (by rw [← hα', ← ht']; exact congrArg Subtype.val e)
      · apply Subtype.ext
        simpa [hα', ht'] using h.t_comm_S α hα.mem
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz', hα', ht']
        exact h.z_conj_alpha hα
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz', ht']
        exact h.z_conj_t
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz', hh₁', hg₁']
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz', hh₂', hg₂']
      · refine hQβ.to_le ?_
        rw [Subgroup.closure_le]
        intro c hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rw [SetLike.mem_coe, mem_subgroupOf]
        rcases hc with hc | hc | hc | hc | hc | hc <;> rw [hc]
        · rw [hα']
          exact (h.Zg_cent_Q hα (h.alpha_mem_Zg hα)).1
        · rw [ht']
          exact (h.Zg_cent_Q hα (h.t_mem_Zg hα)).1
        · rw [hg₁']
          exact hQg₁
        · rw [hg₂']
          exact hQg₂
        · rw [hh₁']
          exact hQh₁
        · rw [hh₂']
          exact hQh₂
      · intro c hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        apply hcomm_Q
        rcases hc with hc | hc | hc | hc <;> rw [hc]
        · rw [hg₁']
          exact hQg₁
        · rw [hg₂']
          exact hQg₂
        · rw [hh₁']
          exact hQh₁
        · rw [hh₂']
          exact hQh₂
      · exact hg₁sq'
      · exact hg₂sq'
      · apply Subtype.ext
        simpa [hg₁', hg₂', hα', ht'] using T12
      · apply Subtype.ext
        simpa [hh₁', hh₂', hα'] using T34
      · apply Subtype.ext
        simpa [hg₁', hh₂', ht'] using T14
      · apply Subtype.ext
        simpa [hg₂', hh₁', ht'] using T23
      · apply Subtype.ext
        simpa [hg₁', hh₁'] using T13
      · apply Subtype.ext
        simpa [hg₂', hh₂'] using T24
    have hl96' : Lemma96Conclusion ↥(centralizer ({β} : Set G)) (QuotientGroup.mk z') := by
      have hz'eq : z' = ⟨z, hz⟩ := Subtype.ext hz'
      rw [hz'eq]
      exact hl
    have hnconj : ∀ k : ↥(centralizer ({β} : Set G)), k * z' * k⁻¹ ≠ α' := by
      intro g hg
      have e1 := congrArg Subtype.val hg
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz', hα'] at e1
      rcases h.h67 (g : G) (by rw [e1]; exact hα.mem) with h1 | h1
      · exact hα.ne_z (by rw [← e1, h1])
      · exact hα.ne_zt (by rw [← e1, h1])
    unfold OuterNoTable at hNT
    exact hNT ↥(centralizer ({β} : Set G)) z' α' t' g₁' g₂' h₁' h₂' hl96' htable hnconj

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
