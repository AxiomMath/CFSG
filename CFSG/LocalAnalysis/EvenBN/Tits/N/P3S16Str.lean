module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16Gen
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Cnt

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.S16

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N CFSG.LocalAnalysis.EvenBN.Tits.N.P4

section Str

variable {Γ : Type*} [Group Γ]

theorem exists_comm_of_fpf [Finite Γ] {U : Subgroup Γ} {x : Γ} (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hfpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1) :
    ∀ w ∈ U, ∃ a ∈ U, x * a * x⁻¹ * a⁻¹ = w := by
  classical
  let φ : ↥U →* ↥U :=
    { toFun := fun a => ⟨x * a * x⁻¹ * a⁻¹, mul_mem (hxU a a.2) (inv_mem a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hc : (a : Γ)⁻¹ * (x * b * x⁻¹ * (b : Γ)⁻¹) = (x * b * x⁻¹ * (b : Γ)⁻¹) * (a : Γ)⁻¹ :=
          hcomm _ (inv_mem a.2) _ (mul_mem (hxU b b.2) (inv_mem b.2))
        show x * ((a : Γ) * b) * x⁻¹ * ((a : Γ) * b)⁻¹ =
          (x * a * x⁻¹ * (a : Γ)⁻¹) * (x * b * x⁻¹ * (b : Γ)⁻¹)
        calc x * ((a : Γ) * b) * x⁻¹ * ((a : Γ) * b)⁻¹
            = x * a * x⁻¹ * ((x * b * x⁻¹ * (b : Γ)⁻¹) * (a : Γ)⁻¹) := by group
          _ = x * a * x⁻¹ * ((a : Γ)⁻¹ * (x * b * x⁻¹ * (b : Γ)⁻¹)) := by rw [hc]
          _ = (x * a * x⁻¹ * (a : Γ)⁻¹) * (x * b * x⁻¹ * (b : Γ)⁻¹) := by group) }
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun a ha => ?_
    have h1 : x * (a : Γ) * x⁻¹ * (a : Γ)⁻¹ = 1 := congrArg Subtype.val ha
    have h2 : x * (a : Γ) * x⁻¹ = a := mul_inv_eq_one.1 h1
    exact Subtype.ext (hfpf a a.2 h2)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro w hw
  obtain ⟨a, ha⟩ := hsurj ⟨w, hw⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

theorem exists_fusionIsSylowIn' [Finite Γ] {B Γ' : Subgroup Γ} (hB : IsPGroup 2 B) (hBΓ : B ≤ Γ') :
    ∃ T : Subgroup Γ, B ≤ T ∧ fusionIsSylowIn 2 T Γ' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (hB.comap_subtype (K := Γ')).exists_le_sylow
  refine ⟨(P : Subgroup Γ').map Γ'.subtype,
    fun u hu => ⟨⟨u, hBΓ hu⟩, hP (show (⟨u, hBΓ hu⟩ : Γ') ∈ B.comap Γ'.subtype from hu), rfl⟩,
    Subgroup.map_subtype_le _, P.isPGroup'.map _, fun Q hQX hQ hPQ => ?_⟩
  have h1 := P.is_maximal' (Q := Q.subgroupOf Γ') hQ.comap_subtype
    (fun x hx => hPQ ⟨x, hx, rfl⟩)
  refine le_antisymm (fun q hq => ⟨⟨q, hQX hq⟩, ?_, rfl⟩) hPQ
  rw [← h1]
  exact hq

structure Ctx (U : Subgroup Γ) (x y t : Γ) (Ξ Θ : Subgroup Γ) : Prop where
  F : IsF20 U x y
  Ξ_eq : Ξ = zpowers t ⊔ IsF20.Pgrp U x y
  t2 : t * t = 1
  t1 : t ≠ 1
  tP : ∀ p ∈ IsF20.Pgrp U x y, t * p = p * t
  tinf : zpowers t ⊓ IsF20.Pgrp U x y = ⊥
  ΞΘ : Ξ ≤ Θ
  Θt : ∀ θ ∈ Θ, θ * t = t * θ
  norm : ∀ θ ∈ Θ, ∀ ξ ∈ Ξ, θ * ξ * θ⁻¹ ∈ Ξ
  cos : ∀ θ ∈ Θ, θ ∉ Ξ → ∀ θ' ∈ Θ, θ' ∉ Ξ → θ⁻¹ * θ' ∈ Ξ

namespace Ctx

variable {U : Subgroup Γ} {x y t : Γ} {Ξ Θ : Subgroup Γ}

theorem x_mem_P (hC : Ctx U x y t Ξ Θ) : x ∈ IsF20.Pgrp U x y :=
  mem_sup_right (mem_sup_left (mem_zpowers x))

theorem y_mem_P (hC : Ctx U x y t Ξ Θ) : y ∈ IsF20.Pgrp U x y :=
  mem_sup_right (mem_sup_right (mem_zpowers y))

theorem U_le_P (hC : Ctx U x y t Ξ Θ) : U ≤ IsF20.Pgrp U x y := le_sup_left

theorem P_le_Ξ (hC : Ctx U x y t Ξ Θ) : IsF20.Pgrp U x y ≤ Ξ := by
  rw [hC.Ξ_eq]
  exact le_sup_right

theorem t_mem_Ξ (hC : Ctx U x y t Ξ Θ) : t ∈ Ξ := by
  rw [hC.Ξ_eq]
  exact mem_sup_left (mem_zpowers t)

theorem t_comm_x (hC : Ctx U x y t Ξ Θ) : t * x = x * t := hC.tP x hC.x_mem_P

theorem mem_Ξ_iff (hC : Ctx U x y t Ξ Θ) {g : Γ} :
    g ∈ Ξ ↔ g ∈ IsF20.Pgrp U x y ∨ ∃ p ∈ IsF20.Pgrp U x y, g = p * t := by
  rw [hC.Ξ_eq, sup_comm]
  exact mem_sup_zpowers_of_normalizes hC.t2 (fun k hk => by
    have : t * k * t⁻¹ = k := by
      calc t * k * t⁻¹ = k * t * t⁻¹ := by rw [hC.tP k hk]
        _ = k := by group
    rw [this]
    exact hk)

theorem t_comm_Ξ (hC : Ctx U x y t Ξ Θ) {g : Γ} (hg : g ∈ Ξ) : t * g = g * t := by
  rcases hC.mem_Ξ_iff.1 hg with hgP | ⟨p, hp, rfl⟩
  · exact hC.tP g hgP
  · calc t * (p * t) = (t * p) * t := by group
      _ = (p * t) * t := by rw [hC.tP p hp]

theorem sq_mem (hC : Ctx U x y t Ξ Θ) {θ : Γ} (hθ : θ ∈ Θ) (hθΞ : θ ∉ Ξ) : θ * θ ∈ Ξ := by
  have h := hC.cos θ⁻¹ (inv_mem hθ) (fun h => hθΞ (by simpa using inv_mem h)) θ hθ hθΞ
  simpa using h

theorem card_Ξ (hC : Ctx U x y t Ξ Θ) : Nat.card Ξ = 640 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := hC.F.card_Pgrp
  have htz : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hC.t2) hC.t1]
  have hN : zpowers t ≤ normalizer ((IsF20.Pgrp U x y : Subgroup Γ) : Set Γ) := by
    rw [zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun p hp => (hC.tP p hp).symm)
  rw [hC.Ξ_eq, sup_comm, card_sup_of_inf_eq_bot' hN (by rw [inf_comm]; exact hC.tinf), hP, htz]

theorem sylow5 [Finite Γ] (hC : Ctx U x y t Ξ Θ) : fusionIsSylowIn 5 (zpowers x) Ξ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hxΞ : zpowers x ≤ Ξ := zpowers_le.2 (hC.P_le_Ξ hC.x_mem_P)
  refine ⟨hxΞ, IsPGroup.of_card (n := 1) (by rw [hC.F.card_zpowers_x]; norm_num), ?_⟩
  intro Q hQΞ hQ hxQ
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ 640 := hC.card_Ξ ▸ Subgroup.card_dvd_of_le hQΞ
  have h5 : 5 ∣ Nat.card Q := hC.F.card_zpowers_x ▸ Subgroup.card_dvd_of_le hxQ
  have hk1 : k = 1 := by
    rw [hk] at hdvd h5
    by_contra hne
    rcases Nat.lt_or_ge k 1 with h0 | h2
    · have : k = 0 := by omega
      rw [this, pow_zero] at h5
      omega
    · have h2' : 2 ≤ k := by omega
      have h25 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 h2'
      have := h25.trans hdvd
      norm_num at this
  exact (Subgroup.eq_of_le_of_card_ge hxQ (by rw [hk, hk1, hC.F.card_zpowers_x]; norm_num)).symm

theorem exists_comm_x [Finite Γ] (hC : Ctx U x y t Ξ Θ) {θ : Γ} (hθ : θ ∈ Θ) :
    ∃ ξ ∈ Ξ, (ξ * θ) * x = x * (ξ * θ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ξ₁, hξ₁, hn⟩ := exists_conj_normalizes_sylow (p := 5) hC.ΞΘ hC.norm hC.sylow5 hθ
  have hx' : (ξ₁ * θ) * x * (ξ₁ * θ)⁻¹ ∈ zpowers x := (mem_normalizer_iff.1 hn x).1 (mem_zpowers x)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hx'
  obtain ⟨w, hw, hwy⟩ := hC.F.exists_frob
  have hwP : w ∈ IsF20.Pgrp U x y := by
    have : w ∈ zpowers y := hwy ▸ mem_zpowers w
    exact (zpowers_le.2 hC.y_mem_P) this
  have hj5 : j % 5 ≠ 0 := by
    intro h0
    have h1 : x ^ j = 1 := by rw [hC.F.zpow_emod_five j, h0, zpow_zero]
    rw [h1] at hj
    apply hC.F.x_ne_one
    have := hj.symm
    rw [mul_inv_eq_one] at this
    exact mul_eq_left.1 this
  have hm : ∃ m : ℕ, ((3 : ℤ) ^ m * j) % 5 = 1 := by
    have hc : j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
    rcases hc with h | h | h | h
    · exact ⟨0, by norm_num; omega⟩
    · exact ⟨1, by norm_num; omega⟩
    · exact ⟨3, by norm_num; omega⟩
    · exact ⟨2, by norm_num; omega⟩
  obtain ⟨m, hm⟩ := hm
  refine ⟨w ^ m * ξ₁, mul_mem (pow_mem (hC.P_le_Ξ hwP) m) hξ₁, ?_⟩
  have hconj : (w ^ m * ξ₁ * θ) * x * (w ^ m * ξ₁ * θ)⁻¹ = x := by
    have e1 : (w ^ m * ξ₁ * θ) * x * (w ^ m * ξ₁ * θ)⁻¹
        = w ^ m * ((ξ₁ * θ) * x * (ξ₁ * θ)⁻¹) * (w ^ m)⁻¹ := by group
    rw [e1, ← hj, ← conj_zpow]
    have e2 : w ^ m * x * (w ^ m)⁻¹ = x ^ (3 ^ m) := hw.y_pow_conj m
    rw [e2, ← zpow_natCast, ← zpow_mul, hC.F.zpow_emod_five]
    have : (((3 ^ m : ℕ) : ℤ) * j) % 5 = 1 := by simpa using hm
    rw [this, zpow_one]
  exact (mul_inv_eq_iff_eq_mul.1 hconj)

theorem exists_two_part [Finite Γ] (hC : Ctx U x y t Ξ Θ) {θ : Γ} (hθ : θ ∈ Θ) (hθΞ : θ ∉ Ξ) :
    ∃ β ∈ Θ, β ∉ Ξ ∧ β * x = x * β ∧ ∃ k : ℕ, β ^ (2 ^ k) = 1 := by
  obtain ⟨ξ, hξ, hx⟩ := hC.exists_comm_x hθ
  have hθ₂ : ξ * θ ∈ Θ := mul_mem (hC.ΞΘ hξ) hθ
  have hθ₂Ξ : ξ * θ ∉ Ξ := fun h => hθΞ (by
    have := mul_mem (inv_mem hξ) h
    simpa using this)
  obtain ⟨m, hmodd, k, hk⟩ := exists_odd_pow_two_power (ξ * θ)
  refine ⟨(ξ * θ) ^ m, pow_mem hθ₂ m, ?_, ?_, k, hk⟩
  · intro hmem
    obtain ⟨r, rfl⟩ := hmodd
    have hsq := hC.sq_mem hθ₂ hθ₂Ξ
    have e : (ξ * θ) ^ (2 * r + 1) = ((ξ * θ) * (ξ * θ)) ^ r * (ξ * θ) := by
      rw [pow_succ, pow_mul, pow_two]
    rw [e] at hmem
    apply hθ₂Ξ
    have := mul_mem (inv_mem (pow_mem hsq r)) hmem
    simpa using this
  · exact (Commute.pow_left (show Commute (ξ * θ) x from hx) m).eq

theorem mem_U_iff [Finite Γ] (hC : Ctx U x y t Ξ Θ) {w : Γ} :
    w ∈ U ↔ w * w = 1 ∧ ∃ g ∈ Ξ, w = x * g * x⁻¹ * g⁻¹ := by
  have hF := hC.F
  have hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu => (mem_normalizer_iff.1 hF.x_norm u).1 hu
  constructor
  · intro hw
    refine ⟨hF.sq w hw, ?_⟩
    obtain ⟨a, ha, hae⟩ := exists_comm_of_fpf hF.comm hxU hF.fpf w hw
    exact ⟨a, hC.P_le_Ξ (hC.U_le_P ha), hae.symm⟩
  · rintro ⟨hw2, g, hg, rfl⟩
    have hred : ∀ p ∈ IsF20.Pgrp U x y, (x * p * x⁻¹ * p⁻¹) * (x * p * x⁻¹ * p⁻¹) = 1 →
        x * p * x⁻¹ * p⁻¹ ∈ U := by
      intro p hp hp2
      obtain ⟨u, hu, f, hf, rfl⟩ := hF.exists_mul hp
      obtain ⟨w₀, hw₀, hw₀y⟩ := hF.exists_frob
      have hFN : (zpowers x ⊔ zpowers y : Subgroup Γ) ≤ normalizer (zpowers x : Set Γ) := by
        rw [← hw₀y]
        exact hw₀.sup_le_normalizer
      have hxF : x ∈ (zpowers x ⊔ zpowers y : Subgroup Γ) := mem_sup_left (mem_zpowers x)
      have hcF : x * f * x⁻¹ * f⁻¹ ∈ (zpowers x ⊔ zpowers y : Subgroup Γ) :=
        mul_mem (mul_mem (mul_mem hxF hf) (inv_mem hxF)) (inv_mem hf)
      have hcN : (x * f * x⁻¹ * f⁻¹) ∈ normalizer (U : Set Γ) := hF.F_le_normalizer hcF
      have hu'' : (x * u * x⁻¹) * ((x * f * x⁻¹ * f⁻¹) * u⁻¹ * (x * f * x⁻¹ * f⁻¹)⁻¹) ∈ U :=
        mul_mem (hxU u hu) ((mem_normalizer_iff.1 hcN u⁻¹).1 (inv_mem hu))
      have hdec : x * (u * f) * x⁻¹ * (u * f)⁻¹ =
          ((x * u * x⁻¹) * ((x * f * x⁻¹ * f⁻¹) * u⁻¹ * (x * f * x⁻¹ * f⁻¹)⁻¹)) *
            (x * f * x⁻¹ * f⁻¹) := by group
      rw [hdec] at hp2 ⊢
      have hc2 := hF.sq_of_mul_sq hu'' hcF hp2
      have hfx : f * x⁻¹ * f⁻¹ ∈ zpowers x :=
        (mem_normalizer_iff.1 (hFN hf) x⁻¹).1 (inv_mem (mem_zpowers x))
      obtain ⟨r, hr⟩ := mem_zpowers_iff.1 (mul_mem (mem_zpowers x) hfx)
      have hc1 : x * f * x⁻¹ * f⁻¹ = 1 := by
        have e : x * f * x⁻¹ * f⁻¹ = x * (f * x⁻¹ * f⁻¹) := by group
        rw [e, ← hr]
        apply hF.zpow_x_eq_one_of_sq
        rw [pow_two, hr, ← e]
        exact hc2
      have hfin : ∀ (u'' c : Γ), u'' ∈ U → c = 1 → u'' * c ∈ U := by
        rintro u'' c hu'' rfl
        simpa using hu''
      exact hfin _ _ hu'' hc1
    rcases hC.mem_Ξ_iff.1 hg with hgP | ⟨p, hp, rfl⟩
    · exact hred g hgP hw2
    · have hxt : t * x = x * t := hC.t_comm_x
      have e : x * (p * t) * x⁻¹ * (p * t)⁻¹ = x * p * x⁻¹ * p⁻¹ := by
        have h1 : t * x⁻¹ * t⁻¹ = x⁻¹ := by
          have : t * x⁻¹ = x⁻¹ * t := by
            calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
              _ = x⁻¹ * (t * x) * x⁻¹ := by rw [hxt]
              _ = x⁻¹ * t := by group
          calc t * x⁻¹ * t⁻¹ = x⁻¹ * t * t⁻¹ := by rw [this]
            _ = x⁻¹ := by group
        calc x * (p * t) * x⁻¹ * (p * t)⁻¹ = x * p * (t * x⁻¹ * t⁻¹) * p⁻¹ := by group
          _ = x * p * x⁻¹ * p⁻¹ := by rw [h1]
      rw [e] at hw2 ⊢
      exact hred p hp hw2

theorem normalizes_U [Finite Γ] (hC : Ctx U x y t Ξ Θ) {β : Γ} (hβ : β ∈ Θ) (hβx : β * x = x * β) :
    ∀ u ∈ U, β * u * β⁻¹ ∈ U := by
  intro u hu
  obtain ⟨hu2, g, hg, hug⟩ := hC.mem_U_iff.1 hu
  refine hC.mem_U_iff.2 ⟨?_, β * g * β⁻¹, hC.norm β hβ g hg, ?_⟩
  · calc β * u * β⁻¹ * (β * u * β⁻¹) = β * (u * u) * β⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  · have hxβ : β * x * β⁻¹ = x := by rw [hβx]; group
    calc β * u * β⁻¹ = β * (x * g * x⁻¹ * g⁻¹) * β⁻¹ := by rw [← hug]
      _ = (β * x * β⁻¹) * (β * g * β⁻¹) * (β * x⁻¹ * β⁻¹) * (β * g⁻¹ * β⁻¹) := by group
      _ = x * (β * g * β⁻¹) * x⁻¹ * (β * g * β⁻¹)⁻¹ := by
          have hxβ' : β * x⁻¹ * β⁻¹ = x⁻¹ := by
            calc β * x⁻¹ * β⁻¹ = (β * x * β⁻¹)⁻¹ := by group
              _ = x⁻¹ := by rw [hxβ]
          rw [hxβ, hxβ']
          group

theorem centralizes_U [Finite Γ] (hC : Ctx U x y t Ξ Θ) {β : Γ} (hβ : β ∈ Θ) (hβx : β * x = x * β)
    {k : ℕ} (hβ2 : β ^ (2 ^ k) = 1) : ∀ u ∈ U, β * u = u * β := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPg : IsPGroup 2 (zpowers β) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hβ2)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hβ' : β⁻¹ ∈ Θ := inv_mem hβ
  have hβx' : β⁻¹ * x = x * β⁻¹ := by
    calc β⁻¹ * x = β⁻¹ * (x * β) * β⁻¹ := by group
      _ = β⁻¹ * (β * x) * β⁻¹ := by rw [hβx]
      _ = x * β⁻¹ := by group
  have hPU : zpowers β ≤ normalizer (U : Set Γ) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro u
    refine ⟨hC.normalizes_U hβ hβx u, fun h => ?_⟩
    have := hC.normalizes_U hβ' hβx' _ h
    simpa [mul_assoc] using this
  have hxP : ∀ p ∈ zpowers β, x * p * x⁻¹ ∈ zpowers β := by
    intro p hp
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hp
    have hc : Commute x β := hβx.symm
    have : x * β ^ n * x⁻¹ = β ^ n := mul_inv_eq_iff_eq_mul.2 (hc.zpow_right n).eq
    rw [this]
    exact hp
  exact hC.F.centralizes_of_isPGroup_two hPg hPU hxP β (mem_zpowers β)

theorem eq_one_or_eq_t [Finite Γ] (hC : Ctx U x y t Ξ Θ) {g : Γ} (hg : g ∈ Ξ) (hgx : g * x = x * g)
    (hgU : ∀ u ∈ U, g * u = u * g) : g = 1 ∨ g = t := by
  have hF := hC.F
  have key : ∀ p ∈ IsF20.Pgrp U x y, p * x = x * p → (∀ u ∈ U, p * u = u * p) → p = 1 := by
    intro p hp hpx hpU
    have hpU' : p ∈ U := hF.centralizer_Pgrp hp hpU
    exact hF.fpf p hpU' (by rw [mul_inv_eq_iff_eq_mul]; exact hpx.symm)
  rcases hC.mem_Ξ_iff.1 hg with hgP | ⟨p, hp, rfl⟩
  · exact Or.inl (key g hgP hgx hgU)
  · right
    have htx : t * x = x * t := hC.t_comm_x
    have hp1 : p = 1 := by
      refine key p hp ?_ ?_
      · have h1 : p * t * x = x * (p * t) := hgx
        have h2 : (p * x) * t = (x * p) * t := by
          calc (p * x) * t = p * (x * t) := by group
            _ = p * (t * x) := by rw [htx]
            _ = (p * t) * x := by group
            _ = x * (p * t) := h1
            _ = (x * p) * t := by group
        exact mul_right_cancel h2
      · intro u hu
        have htu : t * u = u * t := hC.tP u (hC.U_le_P hu)
        have h1 : p * t * u = u * (p * t) := hgU u hu
        have h2 : (p * u) * t = (u * p) * t := by
          calc (p * u) * t = p * (u * t) := by group
            _ = p * (t * u) := by rw [htu]
            _ = (p * t) * u := by group
            _ = u * (p * t) := h1
            _ = (u * p) * t := by group
        exact mul_right_cancel h2
    rw [hp1, one_mul]

theorem comm_y_or [Finite Γ] (hC : Ctx U x y t Ξ Θ) {β : Γ} (hβ : β ∈ Θ) (hβx : β * x = x * β)
    (hβU : ∀ u ∈ U, β * u = u * β) : β * y * β⁻¹ = y ∨ β * y * β⁻¹ = y * t := by
  have hF := hC.F
  have hyΞ : y ∈ Ξ := hC.P_le_Ξ hC.y_mem_P
  have hβyΞ : β * y * β⁻¹ ∈ Ξ := hC.norm β hβ y hyΞ
  have hd : y⁻¹ * (β * y * β⁻¹) ∈ Ξ := mul_mem (inv_mem hyΞ) hβyΞ
  obtain ⟨w₀, hw₀, hw₀y⟩ := hF.exists_frob
  have hyN : y ∈ normalizer (zpowers x : Set Γ) := by
    have : y ∈ zpowers w₀ := hw₀y ▸ mem_zpowers y
    exact hw₀.zpowers_y_le_normalizer this
  have hyx : y * x * y⁻¹ ∈ zpowers x := (mem_normalizer_iff.1 hyN x).1 (mem_zpowers x)
  have hβyx : β * (y * x * y⁻¹) = (y * x * y⁻¹) * β := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hyx
    rw [← hn]
    exact ((Commute.zpow_right (show Commute β x from hβx) n).eq)
  have hβx' : β⁻¹ * x = x * β⁻¹ := by
    calc β⁻¹ * x = β⁻¹ * (x * β) * β⁻¹ := by group
      _ = β⁻¹ * (β * x) * β⁻¹ := by rw [hβx]
      _ = x * β⁻¹ := by group
  have hxfix : β * x * β⁻¹ = x := by rw [hβx]; group
  have hyxfix : β * (y * x * y⁻¹) * β⁻¹ = y * x * y⁻¹ := by rw [hβyx]; group
  have hdx : (y⁻¹ * (β * y * β⁻¹)) * x = x * (y⁻¹ * (β * y * β⁻¹)) := by
    have h1 : (β * y * β⁻¹) * x * (β * y * β⁻¹)⁻¹ = y * x * y⁻¹ := by
      calc (β * y * β⁻¹) * x * (β * y * β⁻¹)⁻¹
          = β * y * (β⁻¹ * x * β) * y⁻¹ * β⁻¹ := by group
        _ = β * y * x * y⁻¹ * β⁻¹ := by
            have : β⁻¹ * x * β = x := by
              calc β⁻¹ * x * β = (x * β⁻¹) * β := by rw [hβx']
                _ = x := by group
            rw [this]
        _ = β * (y * x * y⁻¹) * β⁻¹ := by group
        _ = y * x * y⁻¹ := hyxfix
    calc (y⁻¹ * (β * y * β⁻¹)) * x = y⁻¹ * ((β * y * β⁻¹) * x * (β * y * β⁻¹)⁻¹) * (β * y * β⁻¹) := by
          group
      _ = y⁻¹ * (y * x * y⁻¹) * (β * y * β⁻¹) := by rw [h1]
      _ = x * (y⁻¹ * (β * y * β⁻¹)) := by group
  have hdU : ∀ u ∈ U, (y⁻¹ * (β * y * β⁻¹)) * u = u * (y⁻¹ * (β * y * β⁻¹)) := by
    intro u hu
    have hyuy : y * u * y⁻¹ ∈ U := (mem_normalizer_iff.1 hF.v_norm u).1 hu
    have hβu : β⁻¹ * u * β = u := by
      have h1 := hβU u hu
      calc β⁻¹ * u * β = β⁻¹ * (u * β) := by group
        _ = β⁻¹ * (β * u) := by rw [h1]
        _ = u := by group
    have h1 : (β * y * β⁻¹) * u * (β * y * β⁻¹)⁻¹ = y * u * y⁻¹ := by
      calc (β * y * β⁻¹) * u * (β * y * β⁻¹)⁻¹ = β * y * (β⁻¹ * u * β) * y⁻¹ * β⁻¹ := by group
        _ = β * (y * u * y⁻¹) * β⁻¹ := by rw [hβu]; group
        _ = (y * u * y⁻¹) := by
            have := hβU _ hyuy
            rw [this]; group
    calc (y⁻¹ * (β * y * β⁻¹)) * u = y⁻¹ * ((β * y * β⁻¹) * u * (β * y * β⁻¹)⁻¹) * (β * y * β⁻¹) := by
          group
      _ = y⁻¹ * (y * u * y⁻¹) * (β * y * β⁻¹) := by rw [h1]
      _ = u * (y⁻¹ * (β * y * β⁻¹)) := by group
  rcases hC.eq_one_or_eq_t hd hdx hdU with h | h
  · left
    calc β * y * β⁻¹ = y * (y⁻¹ * (β * y * β⁻¹)) := by group
      _ = y := by rw [h, mul_one]
  · right
    calc β * y * β⁻¹ = y * (y⁻¹ * (β * y * β⁻¹)) := by group
      _ = y * t := by rw [h]

theorem comm_Ξ_of_gens (hC : Ctx U x y t Ξ Θ) {β : Γ} (hβt : β * t = t * β) (hβx : β * x = x * β)
    (hβy : β * y = y * β) (hβU : ∀ u ∈ U, β * u = u * β) : ∀ ξ ∈ Ξ, ξ * β = β * ξ := by
  intro ξ hξ
  have hle : Ξ ≤ centralizer ({β} : Set Γ) := by
    rw [hC.Ξ_eq]
    refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hβt.symm)) ?_
    show U ⊔ (zpowers x ⊔ zpowers y) ≤ _
    refine sup_le (fun u hu => mem_centralizer_singleton_iff.2 (hβU u hu).symm) (sup_le ?_ ?_)
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hβx.symm)
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hβy.symm)
  exact mem_centralizer_singleton_iff.1 (hle hξ)

end Ctx

end Str

end CFSG.LocalAnalysis.EvenBN.Tits.N.S16
