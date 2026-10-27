module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR7

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

@[expose] def B_ivk_oddcent : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    (Nonempty (K ≃* alternatingGroup (Fin 7)) ∨ HasL2Model K Odd) →
    ∀ y : MulAut K, y ^ 2 = 1 →
      ∀ s ∈ fixedSubgroup K y, Odd (orderOf s) →
        ∀ w ∈ pPrimeCoreOf 2 (fixedSubgroup K y), s * w = w * s

theorem conj_injective_of_centerless {K : Type} [Group K]
    (h : ∀ a : K, (∀ b : K, a * b = b * a) → a = 1) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro a b hab
  have h1 : MulAut.conj (a * b⁻¹) = (1 : MulAut K) := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : ∀ c : K, (a * b⁻¹) * c = c * (a * b⁻¹) := by
    intro c
    have := congrArg (fun φ : MulAut K => φ c) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc (a * b⁻¹) * c = (a * b⁻¹) * c * (a * b⁻¹)⁻¹ * (a * b⁻¹) := by group
      _ = c * (a * b⁻¹) := by rw [this]
  exact mul_inv_eq_one.1 (h _ h2)

theorem mul_conj_mul_inv' {K : Type} [Group K] (φ : MulAut K) (k : K) :
    φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext a
  simp [MulAut.conj_apply]

theorem odd_natCard_of_forall_odd_orderOf {H : Type*} [Group H] [Finite H]
    (h : ∀ x : H, Odd (orderOf x)) : Odd (Nat.card H) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card H := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have := h x
  rw [hx] at this
  exact absurd this (by decide)

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem endgame_comm_le_cSec_of_normalizing_actors (hKG : B_ivk_oddcent) {u t : G}
    (ht2 : orderOf t = 2) {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({u} : Set G)) L)
    (htL : t ∈ normalizer (L : Set G))
    (hu : Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model (kBar L) Odd)
    {X : Subgroup G} (hXu : X ≤ centralizer ({u} : Set G)) (hXt : X ≤ centralizer ({t} : Set G))
    (hXN : X ≤ normalizer (L : Set G))
    (hXodd : Odd (Nat.card X)) {b : G} (hbN : b ∈ normalizer (L : Set G))
    (hinv : ∀ x ∈ X, b * x * b⁻¹ = x⁻¹)
    (hAN : pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) ≤
      normalizer (L : Set G)) :
    ⁅⁅pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G), X⁆, X⁆ ≤
      centralizerSection L (pPrimeCoreOf 2 L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G)
    with hA
  have hcen := (centerless_two_le_of_u2 hL hu).1
  have hinj : Function.Injective (MulAut.conj : kBar L →* MulAut (kBar L)) :=
    conj_injective_of_centerless hcen
  have hXN' : ∀ x ∈ X, x ∈ normalizer (L : Set G) := fun x hx => hXN hx
  have hAN' : ∀ a ∈ A, a ∈ normalizer (L : Set G) := fun a ha => hAN ha
  set y : MulAut (kBar L) := barAct L ⟨t, htL⟩ with hy
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
  have hy2 : y ^ 2 = 1 := by
    rw [hy, ← map_pow]
    have : (⟨t, htL⟩ : ↥(normalizer (L : Set G))) ^ 2 = 1 := Subtype.ext (by simp [pow_two, htt])
    rw [this, map_one]
  have hX : ∀ x (hx : x ∈ X), ∃ k : kBar L, k ∈ fixedSubgroup (kBar L) y ∧ Odd (orderOf k) ∧
      barAct L ⟨x, hXN' x hx⟩ = MulAut.conj k := by
    intro x hx
    have hxN : x ∈ normalizer (L : Set G) := hXN' x hx
    have hodd : Odd (orderOf x) := Odd.of_dvd_nat hXodd (Subgroup.orderOf_dvd_natCard X hx)
    obtain ⟨j, hjL, hjc⟩ := exists_mem_J_mul_cSec_of_u2 hu hxN hbN hodd (hinv x hx)
    have hjN : j ∈ normalizer (L : Set G) := Subgroup.le_normalizer hjL
    have hxjN : x * j⁻¹ ∈ normalizer (L : Set G) :=
      (normalizer (L : Set G)).mul_mem hxN ((normalizer (L : Set G)).inv_mem hjN)
    have h1 : barAct L ⟨x, hxN⟩ = MulAut.conj (QuotientGroup.mk (⟨j, hjL⟩ : ↥L) : kBar L) := by
      have hxj : (⟨x, hxN⟩ : ↥(normalizer (L : Set G))) = ⟨x * j⁻¹, hxjN⟩ * ⟨j, hjN⟩ :=
        Subtype.ext (by simp)
      rw [hxj, map_mul, (barAct_eq_one_iff _).2 hjc, one_mul, barAct_of_mem hjL]
    refine ⟨QuotientGroup.mk ⟨j, hjL⟩, ?_, ?_, h1⟩
    · have hcomm : barAct L ⟨x, hxN⟩ * y = y * barAct L ⟨x, hxN⟩ := by
        rw [hy, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.1 (hXt hx))
      rw [h1] at hcomm
      have h2 : y * MulAut.conj (QuotientGroup.mk (⟨j, hjL⟩ : ↥L) : kBar L) * y⁻¹ =
          MulAut.conj (QuotientGroup.mk (⟨j, hjL⟩ : ↥L) : kBar L) := by
        rw [← hcomm]; group
      rw [mul_conj_mul_inv'] at h2
      exact hinj h2
    · have h3 : orderOf (barAct L ⟨x, hxN⟩) ∣ orderOf (⟨x, hxN⟩ : ↥(normalizer (L : Set G))) :=
        orderOf_map_dvd _ _
      have h4 : orderOf (⟨x, hxN⟩ : ↥(normalizer (L : Set G))) = orderOf x :=
        (Subgroup.orderOf_coe _).symm
      rw [h1] at h3
      have h5 := orderOf_injective (MulAut.conj : kBar L →* MulAut (kBar L)) hinj
        (QuotientGroup.mk (⟨j, hjL⟩ : ↥L) : kBar L)
      rw [h5, h4] at h3
      exact Odd.of_dvd_nat hodd h3
  have hAnorm : ∀ g ∈ centralizer ({t} : Set G), g ∈ centralizer ({u} : Set G) →
      ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hgt hgu a ha
    refine ⟨TwoThin.pPrimeCoreOf_normalized (centralizer ({t} : Set G)) hgt ha.1, ?_⟩
    exact (centralizer ({u} : Set G)).mul_mem
      ((centralizer ({u} : Set G)).mul_mem hgu ha.2) ((centralizer ({u} : Set G)).inv_mem hgu)
  have hAu : ∀ a ∈ A, a ∈ centralizer ({u} : Set G) := fun a ha => ha.2
  have hAt : ∀ a ∈ A, a ∈ centralizer ({t} : Set G) := fun a ha => TwoThin.pPrimeCoreOf_le _ ha.1
  have hAodd : ∀ a ∈ A, Odd (orderOf a) := fun a ha =>
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({t} : Set G)))
      (Subgroup.orderOf_dvd_natCard _ ha.1)
  let AL : Subgroup (kBar L) :=
    { carrier := {k | ∃ a ∈ A, ∃ ha : a ∈ normalizer (L : Set G),
        barAct L ⟨a, ha⟩ = MulAut.conj k}
      mul_mem' := by
        rintro k₁ k₂ ⟨a₁, ha₁, hN₁, h₁⟩ ⟨a₂, ha₂, hN₂, h₂⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, (normalizer (L : Set G)).mul_mem hN₁ hN₂, ?_⟩
        have : (⟨a₁ * a₂, (normalizer (L : Set G)).mul_mem hN₁ hN₂⟩ :
            ↥(normalizer (L : Set G))) = ⟨a₁, hN₁⟩ * ⟨a₂, hN₂⟩ := rfl
        rw [this, map_mul, h₁, h₂, map_mul]
      one_mem' := ⟨1, A.one_mem, (normalizer (L : Set G)).one_mem, by
        rw [show (⟨1, (normalizer (L : Set G)).one_mem⟩ : ↥(normalizer (L : Set G))) = 1 from rfl,
          map_one, map_one]⟩
      inv_mem' := by
        rintro k ⟨a, ha, hN, h⟩
        refine ⟨a⁻¹, A.inv_mem ha, (normalizer (L : Set G)).inv_mem hN, ?_⟩
        have : (⟨a⁻¹, (normalizer (L : Set G)).inv_mem hN⟩ : ↥(normalizer (L : Set G))) =
            (⟨a, hN⟩ : ↥(normalizer (L : Set G)))⁻¹ := rfl
        rw [this, map_inv, h, map_inv] }
  have hALmem : ∀ k, k ∈ AL ↔ ∃ a ∈ A, ∃ ha : a ∈ normalizer (L : Set G),
      barAct L ⟨a, ha⟩ = MulAut.conj k := fun k => Iff.rfl
  have hALfix : AL ≤ fixedSubgroup (kBar L) y := by
    intro k hk
    obtain ⟨a, ha, haN, h⟩ := (hALmem k).1 hk
    have hcomm : barAct L ⟨a, haN⟩ * y = y * barAct L ⟨a, haN⟩ := by
      rw [hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hAt a ha))
    rw [h] at hcomm
    have h2 : y * MulAut.conj k * y⁻¹ = MulAut.conj k := by rw [← hcomm]; group
    rw [mul_conj_mul_inv'] at h2
    exact hinj h2
  have hlift : ∀ k ∈ fixedSubgroup (kBar L) y, ∃ (l : G) (hl : l ∈ L), l * t = t * l ∧
      (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : kBar L) = k :=
    fun k hk => exists_mem_cent_lift ht2 htL hk
  have hALnorm : ∀ c ∈ fixedSubgroup (kBar L) y, ∀ k ∈ AL, c * k * c⁻¹ ∈ AL := by
    intro c hc k hk
    obtain ⟨l, hl, hlt, rfl⟩ := hlift c hc
    obtain ⟨a, ha, haN, h⟩ := (hALmem k).1 hk
    have hlu : l ∈ centralizer ({u} : Set G) := hL.1 hl
    have hltc : l ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hlt
    have hlaA : l * a * l⁻¹ ∈ A := hAnorm l hltc hlu a ha
    refine (hALmem _).2 ⟨l * a * l⁻¹, hlaA, hAN' _ hlaA, ?_⟩
    have hlN : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
    have e1 : (⟨l * a * l⁻¹, hAN' _ hlaA⟩ : ↥(normalizer (L : Set G))) =
        ⟨l, hlN⟩ * ⟨a, haN⟩ * ⟨l, hlN⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, h, barAct_of_mem hl]
    simp [map_mul, map_inv]
  have hALodd : Odd (Nat.card AL) := by
    refine odd_natCard_of_forall_odd_orderOf (fun k => ?_)
    obtain ⟨a, ha, haN, h⟩ := (hALmem k).1 k.2
    have h1 : orderOf (barAct L ⟨a, haN⟩) ∣ orderOf (⟨a, haN⟩ : ↥(normalizer (L : Set G))) :=
      orderOf_map_dvd _ _
    have h2 : orderOf (⟨a, haN⟩ : ↥(normalizer (L : Set G))) = orderOf a :=
      (Subgroup.orderOf_coe _).symm
    rw [h] at h1
    have h5 := orderOf_injective (MulAut.conj : kBar L →* MulAut (kBar L)) hinj (k : kBar L)
    rw [h5, h2] at h1
    rw [← Subgroup.orderOf_coe k]
    exact Odd.of_dvd_nat (hAodd a ha) h1
  have hALY : AL ≤ pPrimeCoreOf 2 (fixedSubgroup (kBar L) y) := by
    refine le_pPrimeCoreOf_of_normal_odd hALfix ⟨fun n hn g => ?_⟩ (Nat.coprime_two_left.2 hALodd)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hALnorm g g.2 n hn
  have hcomm4 : ∀ m ∈ ⁅A, X⁆, ∃ hm : m ∈ normalizer (L : Set G), ∃ k ∈ AL,
      barAct L ⟨m, hm⟩ = MulAut.conj k := by
    intro m hm
    rw [Subgroup.commutator_def] at hm
    induction hm using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hg
      obtain ⟨kx, -, -, hkx⟩ := hX x hx
      have haN : a ∈ normalizer (L : Set G) := hAN' a ha
      have hxN : x ∈ normalizer (L : Set G) := hXN' x hx
      have hxA : x * a⁻¹ * x⁻¹ ∈ A :=
        hAnorm x (hXt hx) (hXu hx) a⁻¹ (A.inv_mem ha)
      have hgA : ⁅a, x⁆ ∈ A := by
        have : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]
        exact A.mul_mem ha hxA
      have hgN : ⁅a, x⁆ ∈ normalizer (L : Set G) := hAN' _ hgA
      have heq : barAct L ⟨⁅a, x⁆, hgN⟩ = MulAut.conj ((barAct L ⟨a, haN⟩) kx * kx⁻¹) := by
        have e : (⟨⁅a, x⁆, hgN⟩ : ↥(normalizer (L : Set G))) =
            ⟨a, haN⟩ * ⟨x, hxN⟩ * ⟨a, haN⟩⁻¹ * ⟨x, hxN⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hkx, mul_conj_mul_inv', map_mul,
          map_inv]
      exact ⟨hgN, _, (hALmem _).2 ⟨⁅a, x⁆, hgA, hgN, heq⟩, heq⟩
    | one =>
      exact ⟨(normalizer (L : Set G)).one_mem, 1, AL.one_mem, by
        rw [show (⟨1, (normalizer (L : Set G)).one_mem⟩ : ↥(normalizer (L : Set G))) = 1 from rfl,
          map_one, map_one]⟩
    | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      obtain ⟨hm₁, k₁, hk₁, h₁⟩ := ih₁
      obtain ⟨hm₂, k₂, hk₂, h₂⟩ := ih₂
      refine ⟨(normalizer (L : Set G)).mul_mem hm₁ hm₂, k₁ * k₂, AL.mul_mem hk₁ hk₂, ?_⟩
      have : (⟨g₁ * g₂, (normalizer (L : Set G)).mul_mem hm₁ hm₂⟩ : ↥(normalizer (L : Set G))) =
          ⟨g₁, hm₁⟩ * ⟨g₂, hm₂⟩ := rfl
      rw [this, map_mul, h₁, h₂, map_mul]
    | inv g hg ih =>
      obtain ⟨hm, k, hk, h⟩ := ih
      refine ⟨(normalizer (L : Set G)).inv_mem hm, k⁻¹, AL.inv_mem hk, ?_⟩
      have : (⟨g⁻¹, (normalizer (L : Set G)).inv_mem hm⟩ : ↥(normalizer (L : Set G))) =
          (⟨g, hm⟩ : ↥(normalizer (L : Set G)))⁻¹ := rfl
      rw [this, map_inv, h, map_inv]
  rw [Subgroup.commutator_le]
  intro m hm x' hx'
  obtain ⟨hmN, k, hk, hbm⟩ := hcomm4 m hm
  obtain ⟨kx, hkxfix, hkxodd, hbx⟩ := hX x' hx'
  have hx'N : x' ∈ normalizer (L : Set G) := hXN' x' hx'
  have hkY : k ∈ pPrimeCoreOf 2 (fixedSubgroup (kBar L) y) := hALY hk
  have hcomm := hKG (kBar L) hu y hy2 kx hkxfix hkxodd k hkY
  have hcN : ⁅m, x'⁆ ∈ normalizer (L : Set G) := by
    have : ⁅m, x'⁆ = m * x' * m⁻¹ * x'⁻¹ := rfl
    rw [this]
    exact (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem hmN hx'N)
        ((normalizer (L : Set G)).inv_mem hmN)) ((normalizer (L : Set G)).inv_mem hx'N)
  refine (barAct_eq_one_iff ⟨⁅m, x'⁆, hcN⟩).1 ?_
  have e : (⟨⁅m, x'⁆, hcN⟩ : ↥(normalizer (L : Set G))) =
      ⟨m, hmN⟩ * ⟨x', hx'N⟩ * ⟨m, hmN⟩⁻¹ * ⟨x', hx'N⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hbm, hbx]
  have hcc : MulAut.conj k * MulAut.conj kx = MulAut.conj kx * MulAut.conj k := by
    rw [← map_mul, ← map_mul, hcomm.symm]
  calc MulAut.conj k * MulAut.conj kx * (MulAut.conj k)⁻¹ * (MulAut.conj kx)⁻¹
      = MulAut.conj kx * MulAut.conj k * (MulAut.conj k)⁻¹ * (MulAut.conj kx)⁻¹ := by rw [hcc]
    _ = 1 := by group

theorem endgame_comm_le_cSec (hKG : B_ivk_oddcent) {u t : G} (ht2 : orderOf t = 2)
    (hut : u * t = t * u) {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({u} : Set G)) L)
    (hLN : ∀ g ∈ centralizer ({u} : Set G), g ∈ normalizer (L : Set G))
    (hu : Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model (kBar L) Odd)
    {X : Subgroup G} (hXu : X ≤ centralizer ({u} : Set G)) (hXt : X ≤ centralizer ({t} : Set G))
    (hXodd : Odd (Nat.card X)) {b : G} (hbu : b ∈ centralizer ({u} : Set G))
    (hinv : ∀ x ∈ X, b * x * b⁻¹ = x⁻¹) :
    ⁅⁅pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G), X⁆, X⁆ ≤
      centralizerSection L (pPrimeCoreOf 2 L) := by
  have htu : t ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hut.symm
  exact endgame_comm_le_cSec_of_normalizing_actors hKG ht2 hL (hLN t htu) hu hXu hXt
    (fun x hx => hLN x (hXu hx)) hXodd (hLN b hbu) hinv
    (fun a ha => hLN a ha.2)

end CFSG.GH74.GLS.Th2.Obs
