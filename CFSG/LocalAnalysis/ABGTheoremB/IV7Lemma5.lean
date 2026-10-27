module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SignalizerFunctor.HallContainment
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ABGTheoremB

open Subgroup
open scoped commutatorElement

universe u

section General

variable {G : Type*} [Group G]

private theorem mem_normalizer_of_conj_mem [Finite G] {L : Subgroup G} {g : G}
    (h : ∀ x ∈ L, g * x * g⁻¹ ∈ L) : g ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem conj_eq_of_mem_of_coprime [Finite G] {p : ℕ} [Fact p.Prime] {H₀ : Subgroup G}
    (hH₀ : IsPGroup p H₀) {k h : G} (hk : (orderOf k).Coprime p)
    (hcent : ∀ a ∈ H₀, k * a = a * k) (hh : h⁻¹ * (k * h * k⁻¹) ∈ H₀) : k * h * k⁻¹ = h := by
  set d := h⁻¹ * (k * h * k⁻¹) with hd
  have hkd : k * d * k⁻¹ = d := by rw [hcent d hh, mul_inv_cancel_right]
  have hhd : k * h * k⁻¹ = h * d := by rw [hd, mul_inv_cancel_left]
  have key : ∀ j : ℕ, k ^ j * h * (k ^ j)⁻¹ = h * d ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc k ^ (j + 1) * h * (k ^ (j + 1))⁻¹ = k * (k ^ j * h * (k ^ j)⁻¹) * k⁻¹ := by
            rw [pow_succ']; group
        _ = (k * h * k⁻¹) * (k * d ^ j * k⁻¹) := by rw [ih]; group
        _ = h * d ^ (j + 1) := by rw [hhd, ← conj_pow, hkd, pow_succ', mul_assoc]
  have h1 := key (orderOf k)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, left_eq_mul] at h1
  obtain ⟨n, hn⟩ := hH₀ ⟨d, hh⟩
  have hd1 : orderOf d ∣ p ^ n := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hn
    simpa using this)
  have hd2 : orderOf d ∣ orderOf k := orderOf_dvd_of_pow_eq_one h1
  have hcop : (orderOf d).Coprime (orderOf k) :=
    Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.pow_left n hk.symm)
  have hord : orderOf d = 1 := Nat.Coprime.eq_one_of_dvd hcop hd2
  rw [orderOf_eq_one_iff] at hord
  rw [hhd, hord, mul_one]

private theorem exists_mem_commute_mul [Finite G] {A : Subgroup G} (hA : Odd (Nat.card A))
    {t h : G} (ht : t * t = 1) (hc : h⁻¹ * (t * h * t⁻¹) ∈ A) :
    ∃ a ∈ A, t * (h * a) = h * a * t := by
  set c := h⁻¹ * (t * h * t⁻¹) with hcdef
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htc : t * c * t⁻¹ = c⁻¹ := by
    rw [hcdef, ht']
    calc t * (h⁻¹ * (t * h * t)) * t = t * h⁻¹ * t * h * (t * t) := by group
      _ = t * h⁻¹ * t * h := by rw [ht, mul_one]
      _ = (h⁻¹ * (t * h * t))⁻¹ := by
        simp only [mul_inv_rev, inv_inv, ht', mul_assoc]
  have hodd : Odd (orderOf c) := hA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A hc)
  obtain ⟨m, hm⟩ := hodd
  refine ⟨c ^ (m + 1), pow_mem hc _, ?_⟩
  have hthc : t * h * t⁻¹ = h * c := by rw [hcdef, mul_inv_cancel_left]
  have hcc : c ^ (m + 1) * c ^ (m + 1) = c := by
    rw [← pow_add, show m + 1 + (m + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have key : t * (h * c ^ (m + 1)) * t⁻¹ = h * c ^ (m + 1) := by
    calc t * (h * c ^ (m + 1)) * t⁻¹ = (t * h * t⁻¹) * (t * c * t⁻¹) ^ (m + 1) := by
          rw [conj_pow]; group
      _ = h * c * (c ^ (m + 1))⁻¹ := by rw [hthc, htc, inv_pow]
      _ = h * c ^ (m + 1) := by
          rw [mul_assoc, mul_right_inj, mul_inv_eq_iff_eq_mul, hcc]
  calc t * (h * c ^ (m + 1)) = t * (h * c ^ (m + 1)) * t⁻¹ * t := by group
    _ = h * c ^ (m + 1) * t := by rw [key]

private theorem exists_mem_forall_commutator_mem [Finite G] {p : ℕ} [Fact p.Prime]
    {P A C : Subgroup G} (hP : IsPGroup p P) (hAC : A < C) (hCP : C ≤ P)
    (hAn : P ≤ normalizer (A : Set G)) (hCn : P ≤ normalizer (C : Set G)) :
    ∃ b ∈ C, b ∉ A ∧ ∀ x ∈ P, b * x * b⁻¹ * x⁻¹ ∈ A := by
  have hAP : A ≤ P := hAC.le.trans hCP
  have : (A.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hAP).mpr hAn
  have : (C.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hCP).mpr hCn
  have hlt : A.subgroupOf P < C.subgroupOf P := by
    refine lt_of_le_of_ne (fun x hx => hAC.le hx) fun h => hAC.ne ?_
    have h' := subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hAP, inf_eq_left.mpr hCP] at h'
  obtain ⟨b, hbC, hbA, -, B, -, -, -, hbB, -, hcomm⟩ :=
    CFSG.SectionRank.Ccomm.exists_central_extension hP hlt
  refine ⟨b, hbC, hbA, fun x hx => ?_⟩
  have h := hcomm b hbB ⟨x, hx⟩
  rw [mem_subgroupOf] at h
  simpa [commutatorElement_def] using h

end General

section Sections

variable {G : Type*} [Group G]

private def centSub (A : Subgroup G) (B : Set G) (H₀ : Subgroup G)
    (hA : A ≤ normalizer (H₀ : Set G)) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ H₀}
  mul_mem' := by
    rintro x y ⟨hxA, hx⟩ ⟨hyA, hy⟩
    refine ⟨A.mul_mem hxA hyA, fun b hb => ?_⟩
    have h1 : x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ ∈ H₀ :=
      (mem_normalizer_iff.mp (hA hxA) _).mp (hy b hb)
    have h2 := H₀.mul_mem h1 (hx b hb)
    convert h2 using 1
    group
  one_mem' := ⟨A.one_mem, fun b _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxA, hx⟩
    refine ⟨A.inv_mem hxA, fun b hb => ?_⟩
    have h1 : x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * x⁻¹⁻¹ ∈ H₀ :=
      (mem_normalizer_iff.mp (hA (A.inv_mem hxA)) _).mp (H₀.inv_mem (hx b hb))
    convert h1 using 1
    group

private theorem mem_centSub {A : Subgroup G} {B : Set G} {H₀ : Subgroup G}
    {hA : A ≤ normalizer (H₀ : Set G)} {x : G} :
    x ∈ centSub A B H₀ hA ↔ x ∈ A ∧ ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ H₀ := Iff.rfl

private theorem le_normalizer_centSub [Finite G] {X A B H₀ : Subgroup G}
    (hA : A ≤ normalizer (H₀ : Set G)) (hXA : X ≤ normalizer (A : Set G))
    (hXB : X ≤ normalizer (B : Set G)) (hXH₀ : X ≤ normalizer (H₀ : Set G)) :
    X ≤ normalizer (centSub A B H₀ hA : Set G) := by
  intro y hy
  apply mem_normalizer_of_conj_mem
  rintro a ⟨haA, ha⟩
  refine ⟨(mem_normalizer_iff.mp (hXA hy) a).mp haA, fun b hb => ?_⟩
  have hb' : y⁻¹ * b * y ∈ B := by
    have := (mem_normalizer_iff.mp (hXB (X.inv_mem hy)) b).mp hb
    simpa using this
  have h1 := (mem_normalizer_iff.mp (hXH₀ hy) _).mp (ha _ hb')
  convert h1 using 1
  group

private def quotConj (H H₀ : Subgroup G) [(H₀.subgroupOf H).Normal] (g : G)
    (hgH : g ∈ normalizer (H : Set G)) (hgH₀ : g ∈ normalizer (H₀ : Set G)) :
    ↥H ⧸ H₀.subgroupOf H →* ↥H ⧸ H₀.subgroupOf H :=
  QuotientGroup.map _ _ (H.normalizerMonoidHom ⟨g, hgH⟩).toMonoidHom (by
    intro x hx
    rw [mem_comap, mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      normalizerMonoidHom_apply_apply_coe]
    exact (mem_normalizer_iff.mp hgH₀ x).mp hx)

private theorem quotConj_mk (H H₀ : Subgroup G) [(H₀.subgroupOf H).Normal] (g : G)
    (hgH : g ∈ normalizer (H : Set G)) (hgH₀ : g ∈ normalizer (H₀ : Set G)) (x : ↥H) :
    quotConj H H₀ g hgH hgH₀ (x : ↥H ⧸ H₀.subgroupOf H) =
      ((⟨g * x * g⁻¹, (mem_normalizer_iff.mp hgH x).mp x.2⟩ : ↥H) : ↥H ⧸ H₀.subgroupOf H) := by
  rw [quotConj, QuotientGroup.map_mk]
  congr 1

private theorem quotConj_iterate_mk (H H₀ : Subgroup G) [(H₀.subgroupOf H).Normal] (g : G)
    (hgH : g ∈ normalizer (H : Set G)) (hgH₀ : g ∈ normalizer (H₀ : Set G)) (n : ℕ)
    (x : ↥H) :
    (quotConj H H₀ g hgH hgH₀)^[n] (x : ↥H ⧸ H₀.subgroupOf H) =
      ((⟨g ^ n * x * (g ^ n)⁻¹, (mem_normalizer_iff.mp (pow_mem hgH n) x).mp x.2⟩ : ↥H) :
        ↥H ⧸ H₀.subgroupOf H) := by
  induction n with
  | zero =>
    have hx : (⟨g ^ 0 * x * (g ^ 0)⁻¹, (mem_normalizer_iff.mp (pow_mem hgH 0) x).mp x.2⟩ : ↥H)
        = x := Subtype.ext (by simp)
    rw [hx]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, quotConj_mk]
    congr 1
    apply Subtype.ext
    simp only
    group

end Sections

section Abstract

private theorem eq_one_of_mul_self_eq_one {V : Type*} [Group V] [Finite V]
    (hodd : Odd (Nat.card V)) {v : V} (hv : v * v = 1) : v = 1 := by
  have h2 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hv])
  have hcop : (orderOf v).Coprime 2 :=
    Nat.coprime_two_right.mpr (hodd.of_dvd_nat (orderOf_dvd_natCard v))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2)

private theorem exists_fixed_ne_one_of_iterate {V : Type*} [Group V] [Finite V] {p : ℕ}
    [hp : Fact p.Prime] (hV : IsPGroup p V) (U : V →* V) {k : ℕ} (hU : ∀ v, U^[p ^ k] v = v)
    (W : Subgroup V) (hW : ∀ w ∈ W, U w ∈ W) (hWne : W ≠ ⊥) : ∃ w ∈ W, w ≠ 1 ∧ U w = w := by
  classical
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨m, hm⟩ : ∃ m, p ^ k = m + 1 := ⟨p ^ k - 1, by
    have := pow_pos hp.out.pos k
    omega⟩
  have hUinj : Function.Injective U := by
    intro a b hab
    rw [← hU a, ← hU b, hm, Function.iterate_succ_apply, Function.iterate_succ_apply, hab]
  let f : W → W := fun w => ⟨U w, hW w w.2⟩
  have hfinj : Function.Injective f := fun a b hab =>
    Subtype.ext (hUinj (congrArg Subtype.val hab))
  let σ : Equiv.Perm W := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  have hσ : ∀ (n : ℕ) (w : W), ((σ ^ n) w : V) = U^[n] w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply', ← ih]
      rfl
  have hσp : σ ^ p ^ k = 1 := by
    ext w
    rw [hσ, hU]
    rfl
  have hσ1 : σ 1 = 1 := Subtype.ext (map_one U)
  have hdvd : p ∣ Fintype.card W := by
    obtain ⟨n, hn⟩ := (hV.to_subgroup W).exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hn
      exact hWne hn
    rw [← Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p hn0
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' hdvd hσp hσ1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h), ?_⟩
  have := congrArg Subtype.val hb
  exact this

private theorem exists_fixed_not_fixed {V : Type*} [CommGroup V] [Finite V] {p : ℕ}
    [Fact p.Prime] (hV : IsPGroup p V) (hodd : Odd (Nat.card V)) [Nontrivial V]
    (T U N A B : V →* V) {k : ℕ} (hT : ∀ v, T (T v) = v) (hU : ∀ v, U^[p ^ k] v = v)
    (hTU : ∀ v, T (U v) = U (T v)) (hN : Function.Injective N)
    (hA : ∀ v, A (N v) = T (N (T v))) (hB : ∀ v, B (N (U v)) = U (N v))
    (hAfix : ∀ v, A v = v → v = 1) (hBfix : ∀ v, B v = v → v = 1) :
    ∃ v, T v = v ∧ U v ≠ v := by
  by_contra hcon
  push Not at hcon
  have hnorm : ∀ S : Subgroup V, normalizer (S : Set V) = ⊤ := fun S => by
    have := Subgroup.normal_of_isMulCommutative S
    exact normalizer_eq_top S
  have hcard : ∀ S S' : Subgroup V,
      Nat.card (S ⊔ S' : Subgroup V) * Nat.card (S ⊓ S' : Subgroup V) =
        Nat.card S * Nat.card S' := fun S S' =>
    card_sup_mul_card_inf_of_le_normalizer (by rw [hnorm]; exact le_top)
  let Ct : Subgroup V := MonoidHom.eqLocus T (MonoidHom.id V)
  let It : Subgroup V := MonoidHom.eqLocus T invMonoidHom
  let Cu : Subgroup V := MonoidHom.eqLocus U (MonoidHom.id V)
  have hCt : ∀ v, v ∈ Ct ↔ T v = v := fun v => Iff.rfl
  have hIt : ∀ v, v ∈ It ↔ T v = v⁻¹ := fun v => Iff.rfl
  have hCu : ∀ v, v ∈ Cu ↔ U v = v := fun v => Iff.rfl
  let ψ : V →* V := MonoidHom.id V / T
  have hψ : ∀ v, ψ v = v / T v := fun v => rfl
  have hker : ψ.ker = Ct := by
    ext v
    rw [MonoidHom.mem_ker, hψ, div_eq_one, hCt, eq_comm]
  have hrange : ψ.range = It := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      rw [hIt, hψ, map_div, hT, inv_div]
    · intro hw
      rw [hIt] at hw
      obtain ⟨m, hm⟩ := hodd
      refine ⟨w ^ (m + 1), ?_⟩
      rw [hψ, map_pow, hw, inv_pow, div_inv_eq_mul, ← pow_add,
        show m + 1 + (m + 1) = Nat.card V + 1 by omega, pow_succ, pow_card_eq_one', one_mul]
  have hcardV : Nat.card V = Nat.card Ct * Nat.card It := by
    rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker, hker, hrange]
  have hCtIt : Ct ⊓ It = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := mem_inf.mp hv
    rw [hCt] at hv1
    rw [hIt, hv1] at hv2
    rw [mem_bot]
    apply eq_one_of_mul_self_eq_one hodd
    nth_rewrite 1 [hv2]
    exact inv_mul_cancel v
  have hItN : It ⊓ It.map N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx'
    obtain ⟨hx, hx2⟩ := mem_inf.mp hx'
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx2
    rw [mem_bot]
    apply hAfix
    rw [hIt] at hy
    rw [hIt] at hx
    rw [hA, hy, map_inv, map_inv, hx, inv_inv]
  have hCuN : Cu ⊓ Cu.map N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx'
    obtain ⟨hx, hx2⟩ := mem_inf.mp hx'
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx2
    rw [mem_bot]
    apply hBfix
    rw [hCu] at hy
    rw [hCu] at hx
    conv_lhs => rw [← hy]
    rw [hB, hx]
  have hsq : ∀ S : Subgroup V, S ⊓ S.map N = ⊥ → Nat.card S * Nat.card S ≤ Nat.card V := by
    intro S hS
    have h := hcard S (S.map N)
    rw [hS, Subgroup.card_bot, mul_one, Subgroup.card_map_of_injective hN] at h
    rw [← h]
    exact Subgroup.card_le_card_group _
  have hIt2 := hsq It hItN
  have hCu2 := hsq Cu hCuN
  have hItne : It ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, mul_one] at hcardV
    have hCttop : Ct = ⊤ := Subgroup.eq_top_of_card_eq Ct hcardV.symm
    have hTid : ∀ v, T v = v := fun v => (hCt v).mp (hCttop ▸ mem_top v)
    have hNsurj : Function.Surjective N := Finite.injective_iff_surjective.mp hN
    obtain ⟨w, hw⟩ := exists_ne (1 : V)
    obtain ⟨v, rfl⟩ := hNsurj w
    exact hw (hAfix _ (by rw [hA, hTid, hTid]))
  have hUIt : ∀ w ∈ It, U w ∈ It := by
    intro w hw
    rw [hIt] at hw ⊢
    rw [hTU, hw, map_inv]
  obtain ⟨w, hwIt, hw1, hUw⟩ := exists_fixed_ne_one_of_iterate hV U hU It hUIt hItne
  have hCtCu : Ct ≤ Cu := fun v hv => (hCu v).mpr (hcon v ((hCt v).mp hv))
  have hwCu : w ∈ Cu ⊓ It := mem_inf.mpr ⟨(hCu w).mpr hUw, hwIt⟩
  have h2 : 2 ≤ Nat.card (Cu ⊓ It : Subgroup V) := by
    have hne : Cu ⊓ It ≠ ⊥ := fun h => hw1 (by rw [h] at hwCu; exact mem_bot.mp hwCu)
    have h1 : Nat.card (Cu ⊓ It : Subgroup V) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    have h0 : 0 < Nat.card (Cu ⊓ It : Subgroup V) := Nat.card_pos
    omega
  have hjoin := hcard Ct (Cu ⊓ It)
  have hmeet : Ct ⊓ (Cu ⊓ It) = ⊥ := by
    rw [eq_bot_iff, ← hCtIt]
    exact inf_le_inf_left _ inf_le_right
  rw [hmeet, Subgroup.card_bot, mul_one] at hjoin
  have hle : Nat.card (Ct ⊔ (Cu ⊓ It) : Subgroup V) ≤ Nat.card Cu :=
    Subgroup.card_le_of_le (sup_le hCtCu inf_le_left)
  have hItCt : Nat.card It ≤ Nat.card Ct := by
    have hpos : 0 < Nat.card It := Nat.card_pos
    rw [hcardV] at hIt2
    exact Nat.le_of_mul_le_mul_right hIt2 hpos
  rw [hcardV] at hCu2
  have hCtpos : 0 < Nat.card Ct := Nat.card_pos
  have h3 : Nat.card Ct * 2 ≤ Nat.card Cu :=
    le_trans (Nat.mul_le_mul_left _ h2) (hjoin ▸ hle)
  have h4 := Nat.mul_le_mul h3 h3
  have h5 : Nat.card Ct * Nat.card It ≤ Nat.card Ct * Nat.card Ct := Nat.mul_le_mul_left _ hItCt
  have h6 : 1 ≤ Nat.card Ct * Nat.card Ct := Nat.mul_pos hCtpos hCtpos
  nlinarith
end Abstract

section Bridge

variable {G : Type*} [Group G]

private theorem quotConj_mk_eq_iff {H H₀ : Subgroup G} [(H₀.subgroupOf H).Normal]
    (hHn : H ≤ normalizer (H₀ : Set G)) {g : G} (hgH : g ∈ normalizer (H : Set G))
    (hgH₀ : g ∈ normalizer (H₀ : Set G)) (x : ↥H) :
    quotConj H H₀ g hgH hgH₀ (x : ↥H ⧸ H₀.subgroupOf H) = x ↔ g * x * g⁻¹ * x⁻¹ ∈ H₀ := by
  rw [quotConj_mk, QuotientGroup.eq, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hx := mem_normalizer_iff.mp (hHn x.2)
  constructor
  · intro h
    have h' := H₀.inv_mem ((hx _).mp h)
    convert h' using 1
    group
  · intro h
    have h' := (mem_normalizer_iff.mp (hHn (H.inv_mem x.2)) _).mp (H₀.inv_mem h)
    convert h' using 1
    group

private theorem exists_fixed_not_fixed_mod [Finite G] {p : ℕ} [Fact p.Prime]
    {H₀ H : Subgroup G} (hlt : H₀ < H) (hHn : H ≤ normalizer (H₀ : Set G))
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ H₀) (hHp : IsPGroup p H)
    (hHodd : Odd (Nat.card H)) {t u n : G}
    (htH : t ∈ normalizer (H : Set G)) (htH₀ : t ∈ normalizer (H₀ : Set G))
    (huH : u ∈ normalizer (H : Set G)) (huH₀ : u ∈ normalizer (H₀ : Set G))
    (hnH : n ∈ normalizer (H : Set G)) (hnH₀ : n ∈ normalizer (H₀ : Set G))
    (ht : t * t = 1) {k : ℕ} (hu : u ^ p ^ k = 1) (htu : t * u = u * t)
    (hfa : ∀ h ∈ H, (t * n * t⁻¹ * n⁻¹) * h * (t * n * t⁻¹ * n⁻¹)⁻¹ * h⁻¹ ∈ H₀ → h ∈ H₀)
    (hfb : ∀ h ∈ H, (u * n * u⁻¹ * n⁻¹) * h * (u * n * u⁻¹ * n⁻¹)⁻¹ * h⁻¹ ∈ H₀ → h ∈ H₀) :
    ∃ h ∈ H, t * h * t⁻¹ * h⁻¹ ∈ H₀ ∧ u * h * u⁻¹ * h⁻¹ ∉ H₀ := by
  have hH₀H : H₀ ≤ H := hlt.le
  have : (H₀.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hH₀H).mpr hHn
  set V := ↥H ⧸ H₀.subgroupOf H
  have hcomm : ∀ x y : V, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have h := hab _ (H.inv_mem b.2) _ (H.inv_mem a.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    convert h using 1
    group
  let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := hcomm }
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have haH : t * n * t⁻¹ * n⁻¹ ∈ normalizer (H : Set G) :=
    mul_mem (mul_mem (mul_mem htH hnH) (inv_mem htH)) (inv_mem hnH)
  have haH₀ : t * n * t⁻¹ * n⁻¹ ∈ normalizer (H₀ : Set G) :=
    mul_mem (mul_mem (mul_mem htH₀ hnH₀) (inv_mem htH₀)) (inv_mem hnH₀)
  have hbH : u * n * u⁻¹ * n⁻¹ ∈ normalizer (H : Set G) :=
    mul_mem (mul_mem (mul_mem huH hnH) (inv_mem huH)) (inv_mem hnH)
  have hbH₀ : u * n * u⁻¹ * n⁻¹ ∈ normalizer (H₀ : Set G) :=
    mul_mem (mul_mem (mul_mem huH₀ hnH₀) (inv_mem huH₀)) (inv_mem hnH₀)
  let T := quotConj H H₀ t htH htH₀
  let U := quotConj H H₀ u huH huH₀
  let Nn := quotConj H H₀ n hnH hnH₀
  let A := quotConj H H₀ _ haH haH₀
  let B := quotConj H H₀ _ hbH hbH₀
  have hT : ∀ v, T (T v) = v := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [T, quotConj_mk]
    congr 1
    apply Subtype.ext
    calc t * (t * (x : G) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht]; group
  have hU : ∀ v, U^[p ^ k] v = v := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [U, quotConj_iterate_mk]
    congr 1
    apply Subtype.ext
    simp [hu]
  have hTU : ∀ v, T (U v) = U (T v) := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [T, U, quotConj_mk]
    congr 1
    apply Subtype.ext
    calc t * (u * (x : G) * u⁻¹) * t⁻¹ = (t * u) * x * (t * u)⁻¹ := by group
      _ = (u * t) * x * (u * t)⁻¹ := by rw [htu]
      _ = u * (t * x * t⁻¹) * u⁻¹ := by group
  have hN : Function.Injective Nn := by
    rw [injective_iff_map_eq_one]
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [Nn, quotConj_mk, QuotientGroup.eq_one_iff, mem_subgroupOf] at hv
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact (mem_normalizer_iff.mp hnH₀ x).mpr hv
  have hA : ∀ v, A (Nn v) = T (Nn (T v)) := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [A, T, Nn, quotConj_mk]
    congr 1
    apply Subtype.ext
    simp only [mul_inv_rev, inv_inv, ht']
    group
  have hB : ∀ v, B (Nn (U v)) = U (Nn v) := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [B, U, Nn, quotConj_mk]
    congr 1
    apply Subtype.ext
    simp only
    group
  have hAfix : ∀ v, A v = v → v = 1 := by
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    rw [quotConj_mk_eq_iff hHn] at hv
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hfa x x.2 hv
  have hBfix : ∀ v, B v = v → v = 1 := by
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    rw [quotConj_mk_eq_iff hHn] at hv
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hfb x x.2 hv
  have hVp : IsPGroup p V := hHp.to_quotient _
  have hVodd : Odd (Nat.card V) := hHodd.of_dvd_nat (Subgroup.index_dvd_card _)
  obtain ⟨x₀, hx₀H, hx₀⟩ := IsConcreteLE.exists_of_lt hlt
  have : Nontrivial V := by
    refine nontrivial_of_ne ((⟨x₀, hx₀H⟩ : ↥H) : V) 1 fun h => hx₀ ?_
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    exact h
  obtain ⟨v, hTv, hUv⟩ := exists_fixed_not_fixed hVp hVodd T U Nn A B hT hU hTU hN hA hB hAfix
    hBfix
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  exact ⟨x, x.2, (quotConj_mk_eq_iff hHn htH htH₀ x).mp hTv,
    fun h => hUv ((quotConj_mk_eq_iff hHn huH huH₀ x).mpr h)⟩

end Bridge

section Abstract2

private theorem mem_of_pow_mem_of_not_dvd {W : Type*} [Group W] {r : ℕ} (hr : r.Prime)
    {v : W} (hv : v ^ r = 1) {Y : Subgroup W} {m : ℕ} (hm : ¬ r ∣ m) (hvm : v ^ m ∈ Y) :
    v ∈ Y := by
  have hcop : m.Coprime r := Nat.coprime_comm.mp ((hr.coprime_iff_not_dvd).mpr hm)
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  have hv' : v = (v ^ m) ^ m' := by
    rw [← pow_mul, ← Nat.mod_add_div (m * m') r, hm', pow_add, pow_mul, hv, one_pow, mul_one,
      pow_one]
  rw [hv']
  exact pow_mem hvm m'

private theorem exists_eigen {W : Type*} [CommGroup W] {r : ℕ} (hr : r.Prime)
    (hW : ∀ w : W, w ^ r = 1) (T : W →* W) {N : ℕ} (hN : ∀ w, T^[N] w = w) (hrN : ¬ r ∣ N)
    (Y : Subgroup W) (hTY : ∀ y ∈ Y, T y ∈ Y) {w₀ : W} (hw₀ : w₀ ∉ Y) {l : ℕ}
    (hl : T w₀ * (w₀ ^ l)⁻¹ ∈ Y) : ∃ e, e ∉ Y ∧ T e = e ^ l := by
  have hiter : ∀ i, T^[i] w₀ * (w₀ ^ (l ^ i))⁻¹ ∈ Y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h := Y.mul_mem (hTY _ ih) (pow_mem hl (l ^ i))
      convert h using 1
      rw [Function.iterate_succ_apply', map_mul, map_inv, map_pow, mul_pow, inv_pow, ← pow_mul,
        ← pow_succ']
      group
  have hN0 : N ≠ 0 := fun h => hrN (h ▸ dvd_zero r)
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hl0 : ¬ r ∣ l := by
    intro hdvd
    have hl1 : w₀ ^ l = 1 := by
      obtain ⟨c, rfl⟩ := hdvd
      rw [pow_mul, hW, one_pow]
    have h := hiter (M + 1)
    rw [hN, pow_succ', pow_mul, hl1, one_pow, inv_one, mul_one] at h
    exact hw₀ h
  have hwlN : w₀ ^ (l ^ (M + 1)) = w₀ := by
    have hpos : 0 < l ^ (M + 1) :=
      pow_pos (Nat.pos_of_ne_zero (by rintro rfl; exact hl0 (dvd_zero r))) _
    obtain ⟨a, ha⟩ : ∃ a, l ^ (M + 1) = a + 1 := ⟨l ^ (M + 1) - 1, by omega⟩
    have h := hiter (M + 1)
    rw [hN, ha, pow_succ, mul_inv, ← mul_assoc, mul_comm w₀, mul_assoc, mul_inv_cancel,
      mul_one] at h
    have ha' : r ∣ a := by
      by_contra hna
      exact hw₀ (mem_of_pow_mem_of_not_dvd hr (hW w₀) hna (by simpa using Y.inv_mem h))
    obtain ⟨c, rfl⟩ := ha'
    rw [ha, pow_succ, pow_mul, hW, one_pow, one_mul]
  obtain ⟨P, hP0, hPs⟩ : ∃ P : ℕ → W, P 0 = 1 ∧ ∀ n, P (n + 1) = P n ^ l * T^[n] w₀ :=
    ⟨fun n => Nat.rec (motive := fun _ => W) 1 (fun n Pn => Pn ^ l * T^[n] w₀) n, rfl,
      fun n => rfl⟩
  have hTP : ∀ n, T (P n) = P n ^ l * T^[n] w₀ * (w₀ ^ (l ^ n))⁻¹ := by
    intro n
    induction n with
    | zero => simp [hP0]
    | succ n ih =>
      rw [hPs, map_mul, map_pow, ih, ← Function.iterate_succ_apply' T n w₀]
      simp only [mul_pow, inv_pow, ← pow_mul, ← pow_succ]
      ac_rfl
  have hPY : ∀ n, P (n + 1) * (w₀ ^ ((n + 1) * l ^ n))⁻¹ ∈ Y := by
    intro n
    induction n with
    | zero => simp [hPs, hP0]
    | succ n ih =>
      have h := Y.mul_mem (pow_mem ih l) (hiter (n + 1))
      have key : P (n + 1 + 1) * (w₀ ^ ((n + 1 + 1) * l ^ (n + 1)))⁻¹ =
          (P (n + 1) * (w₀ ^ ((n + 1) * l ^ n))⁻¹) ^ l *
            (T^[n + 1] w₀ * (w₀ ^ (l ^ (n + 1)))⁻¹) := by
        rw [hPs (n + 1), mul_pow, inv_pow, ← pow_mul,
          show (n + 1 + 1) * l ^ (n + 1) = (n + 1) * l ^ n * l + l ^ (n + 1) by ring, pow_add,
          mul_inv]
        ac_rfl
      rw [key]
      exact h
  have hc : ¬ r ∣ (M + 1) * l ^ M := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
    · exact hrN h
    · exact hl0 (hr.dvd_of_dvd_pow h)
  have hcop : ((M + 1) * l ^ M).Coprime r := Nat.coprime_comm.mp ((hr.coprime_iff_not_dvd).mpr hc)
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  refine ⟨P (M + 1) ^ m', fun he => hw₀ ?_, ?_⟩
  · have h := Y.mul_mem (Y.inv_mem (pow_mem (hPY M) m')) he
    have hw : w₀ ^ ((M + 1) * l ^ M * m') = w₀ := by
      rw [← Nat.mod_add_div ((M + 1) * l ^ M * m') r, hm', pow_add, pow_mul, hW, one_pow,
        mul_one, pow_one]
    rw [mul_pow, inv_pow, ← pow_mul, hw, mul_inv, inv_inv, mul_comm, ← mul_assoc,
      mul_inv_cancel, one_mul] at h
    exact h
  · rw [map_pow, hTP (M + 1), hN, hwlN, mul_inv_cancel_right, ← pow_mul, ← pow_mul, mul_comm]

end Abstract2

section Abstract3

private theorem sup_eq_of_relIndex_prime {G : Type*} [Group G] {Y L M : Subgroup G}
    (hYL : Y ≤ L) (hML : M ≤ L) (hp : (Y.relIndex L).Prime) (hM : ¬ M ≤ Y) : M ⊔ Y = L := by
  have hle : M ⊔ Y ≤ L := sup_le hML hYL
  have hmul := Subgroup.relIndex_mul_relIndex Y (M ⊔ Y) L le_sup_right hle
  have h1 : Y.relIndex (M ⊔ Y) ≠ 1 := fun h =>
    hM ((relIndex_eq_one.mp h).trans' le_sup_left)
  rcases hp.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hmul) with h | h
  · exact le_antisymm hle (relIndex_eq_one.mp h)
  · exfalso
    rw [h] at hmul
    have hpos : 0 < Y.relIndex L := hp.pos
    have : Y.relIndex (M ⊔ Y) = 1 := by
      have := Nat.eq_of_mul_eq_mul_right hpos (hmul.trans (one_mul _).symm)
      exact this
    exact h1 this

private theorem eq_top_of_not_le_of_invariant {Q : Type*} [Group Q] [Finite Q] {r : ℕ}
    [hr : Fact r.Prime] (hQ : IsPGroup r Q) (T : Q →* Q) {N : ℕ} (hN : ∀ x, T^[N] x = x)
    (hrN : ¬ r ∣ N) (Y₁ : Subgroup Q) [Y₁.Normal] (hTY : ∀ y ∈ Y₁, T y ∈ Y₁)
    (hY₁ : Y₁.index = r) (hinv : ∀ L : Subgroup Q, (∀ x ∈ L, T x ∈ L) → ¬ L ≤ Y₁ → L = ⊤)
    (M : Subgroup Q) (hM : ¬ M ≤ Y₁) : M = ⊤ := by
  have hcardQY : Nat.card (Q ⧸ Y₁) = r := hY₁
  have hcyc : IsCyclic (Q ⧸ Y₁) := isCyclic_of_prime_card hcardQY
  have hcommY : ∀ a b : Q, ⁅a, b⁆ ∈ Y₁ := by
    intro a b
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have hc := (hcyc.commGroup).mul_comm (a : Q ⧸ Y₁) (b : Q ⧸ Y₁)
    rw [hc]
    group
  have hpowY : ∀ a : Q, a ^ r ∈ Y₁ := fun a => hY₁ ▸ Subgroup.pow_index_mem Y₁ a
  have hΦ : frattini Q ≤ Y₁ :=
    CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := r) Y₁ hcommY hpowY
  obtain ⟨-, hcommW, hpowW⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary hQ
  let W := Q ⧸ frattini Q
  let π := QuotientGroup.mk' (frattini Q)
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcommW }
  have hN0 : N ≠ 0 := fun h => hrN (h ▸ dvd_zero r)
  have hTsurj : Function.Surjective T := by
    intro x
    obtain ⟨M', hM'⟩ : ∃ M', N = M' + 1 := ⟨N - 1, by omega⟩
    refine ⟨T^[M'] x, ?_⟩
    have h := hN x
    rwa [hM', Function.iterate_succ_apply'] at h
  let TW : W →* W := QuotientGroup.map (frattini Q) (frattini Q) T
    (frattini_le_comap_frattini_of_surjective hTsurj)
  have hTW : ∀ x : Q, TW (π x) = π (T x) := fun x => QuotientGroup.map_mk _ _ _ _ x
  have hTWN : ∀ w, TW^[N] w = w := by
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) w
    have : ∀ n, TW^[n] (π x) = π (T^[n] x) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hTW, (Function.iterate_succ_apply' T n x).symm]
    rw [this, hN]
  let Ybar : Subgroup W := Y₁.map π
  have hTYbar : ∀ y ∈ Ybar, TW y ∈ Ybar := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hTW]
    exact mem_map_of_mem π (hTY y hy)
  have hmemY : ∀ x : Q, π x ∈ Ybar → x ∈ Y₁ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
    have hyx' : y⁻¹ * x ∈ frattini Q := QuotientGroup.eq.mp hyx
    have := Y₁.mul_mem hy (hΦ hyx')
    simpa using this
  have hY₁top : Y₁ ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hY₁
    exact hr.out.one_lt.ne hY₁
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ ∉ Y₁ := by
    by_contra h
    push Not at h
    exact hY₁top (eq_top_iff.mpr fun x _ => h x)
  have hq₀1 : (q₀ : Q ⧸ Y₁) ≠ 1 := fun h => hq₀ ((QuotientGroup.eq_one_iff q₀).mp h)
  have hgen := zpowers_eq_top_of_prime_card hcardQY hq₀1
  obtain ⟨l, hl⟩ : ∃ l : ℕ, (q₀ : Q ⧸ Y₁) ^ l = (T q₀ : Q ⧸ Y₁) := by
    have hmem : (T q₀ : Q ⧸ Y₁) ∈ Submonoid.powers (q₀ : Q ⧸ Y₁) := by
      rw [mem_powers_iff_mem_zpowers, hgen]
      exact mem_top _
    exact (Submonoid.mem_powers_iff _ _).mp hmem
  have hl' : T q₀ * (q₀ ^ l)⁻¹ ∈ Y₁ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, hl, mul_inv_cancel]
  have hw₀ : π q₀ ∉ Ybar := fun h => hq₀ (hmemY q₀ h)
  have hlW : TW (π q₀) * (π q₀ ^ l)⁻¹ ∈ Ybar := by
    rw [hTW, ← map_pow, ← map_inv, ← map_mul]
    exact mem_map_of_mem π hl'
  obtain ⟨e, he, hTe⟩ := exists_eigen hr.out hpowW TW hTWN hrN Ybar hTYbar hw₀ hlW
  let L : Subgroup Q := (zpowers e).comap π
  have hLT : ∀ x ∈ L, T x ∈ L := by
    intro x hx
    change π (T x) ∈ zpowers e
    rw [← hTW]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hx : π x ∈ zpowers e)
    rw [← hk, map_zpow, hTe, ← zpow_natCast, ← zpow_mul]
    exact zpow_mem (mem_zpowers e) _
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (frattini Q) e
  have hLY : ¬ L ≤ Y₁ := by
    intro h
    have hqL : q ∈ L := by
      change π q ∈ zpowers e
      rw [hq]
      exact mem_zpowers e
    exact he (hq ▸ mem_map_of_mem π (h hqL))
  have hLtop := hinv L hLT hLY
  have hetop : zpowers e = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) w
    have hx : x ∈ L := hLtop ▸ mem_top x
    exact hx
  have he1 : e ≠ 1 := fun h => he (h ▸ Ybar.one_mem)
  have hcardW : Nat.card W = r := by
    rw [← Subgroup.card_top (G := W), ← hetop, Nat.card_zpowers, orderOf_eq_prime (hpowW e) he1]
  have hYbar : Ybar = ⊥ := by
    have hdvd : Nat.card Ybar ∣ r := hcardW ▸ Subgroup.card_subgroup_dvd_card Ybar
    rcases hr.out.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq Ybar h
    · exfalso
      have htop : Ybar = ⊤ := Subgroup.eq_top_of_card_eq Ybar (h.trans hcardW.symm)
      exact he (htop ▸ mem_top e)
  have hY₁Φ : Y₁ ≤ frattini Q := by
    intro y hy
    have h : π y ∈ Ybar := mem_map_of_mem π hy
    rw [hYbar, mem_bot] at h
    exact (QuotientGroup.eq_one_iff y).mp h
  have hprime : (Y₁.relIndex ⊤).Prime := by
    rw [relIndex_top_right, hY₁]
    exact hr.out
  have hsup := sup_eq_of_relIndex_prime le_top le_top hprime hM
  exact frattini_nongenerating (eq_top_iff.mpr (hsup ▸ sup_le_sup_left hY₁Φ M))

end Abstract3

section Config

open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

private structure FrobConfig (p r : ℕ) (t u : G) (X Y K : Subgroup G) : Prop where
  hYK : Y ≤ K
  hKX : K ≤ X
  hYn : X ≤ normalizer (Y : Set G)
  hKn : X ≤ normalizer (K : Set G)
  hYodd : Odd (Nat.card Y)
  hp : p.Prime
  hr : r.Prime
  hp2 : p ≠ 2
  hr2 : r ≠ 2
  hpr : p ≠ r
  hXY : Y.relIndex X = 2 * p * r
  hKY : Y.relIndex K = r
  htX : t ∈ X
  huX : u ∈ X
  ht : orderOf t = 2
  hu : ∃ n : ℕ, u ^ p ^ n = 1
  htu : t * u = u * t
  hcomp : ∀ k : ℕ, (t * u) ^ k ∈ Y ↔ 2 * p ∣ k
  hfrob : ∀ g ∈ zpowers (t * u), g ∉ Y → ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ Y → k ∈ Y
  hcent : ∀ R : Subgroup G, IsSylowOf p R Y → X ⊓ centralizer (R : Set G) ≤ Y

private def FrobConcl (p : ℕ) (t u : G) (Y : Subgroup G) : Prop :=
  ∃ R : Subgroup G, IsSylowOf p R Y ∧ t * u ∈ normalizer (R : Set G) ∧
    ∃ z ∈ R, z * t = t * z ∧ z ^ p = 1 ∧ z * u ≠ u * z

namespace FrobConfig

variable {p r : ℕ} {t u : G} {X Y K : Subgroup G}

private theorem hgX (c : FrobConfig p r t u X Y K) : t * u ∈ X := mul_mem c.htX c.huX

private theorem mul_self_t (c : FrobConfig p r t u X Y K) : t * t = 1 := by
  rw [← pow_two, ← c.ht, pow_orderOf_eq_one]

private theorem odd_p (c : FrobConfig p r t u X Y K) : Odd p :=
  c.hp.eq_two_or_odd'.resolve_left c.hp2

private theorem t_u_pow (c : FrobConfig p r t u X Y K) :
    ∃ n : ℕ, u ^ p ^ n = 1 ∧ (t * u) ^ p ^ n = t ∧ (t * u) ^ (p ^ n + 1) = u := by
  obtain ⟨n, hn⟩ := c.hu
  have hodd : Odd (p ^ n) := c.odd_p.pow
  have hcomm : Commute t u := c.htu
  refine ⟨n, hn, ?_, ?_⟩
  · rw [hcomm.mul_pow, hn, mul_one, ← pow_mod_orderOf, c.ht, Nat.odd_iff.mp hodd, pow_one]
  · rw [hcomm.mul_pow, pow_succ u, hn, one_mul, ← pow_mod_orderOf t, c.ht,
      Nat.even_iff.mp hodd.add_one, pow_zero, one_mul]

private theorem t_mem_zpowers (c : FrobConfig p r t u X Y K) : t ∈ zpowers (t * u) := by
  obtain ⟨n, -, ht, -⟩ := c.t_u_pow
  exact mem_zpowers_iff.mpr ⟨((p ^ n : ℕ) : ℤ), by rw [zpow_natCast]; exact ht⟩

private theorem u_mem_zpowers (c : FrobConfig p r t u X Y K) : u ∈ zpowers (t * u) := by
  obtain ⟨n, -, -, hu⟩ := c.t_u_pow
  exact mem_zpowers_iff.mpr ⟨((p ^ n + 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact hu⟩

private theorem t_not_mem (c : FrobConfig p r t u X Y K) : t ∉ Y := by
  obtain ⟨n, -, ht, -⟩ := c.t_u_pow
  rw [← ht, c.hcomp]
  intro h
  exact c.odd_p.pow.not_two_dvd_nat (dvd_trans (dvd_mul_right 2 p) h)

private theorem u_not_mem (c : FrobConfig p r t u X Y K) : u ∉ Y := by
  obtain ⟨n, -, -, hu⟩ := c.t_u_pow
  rw [← hu, c.hcomp]
  intro h
  have hp' : p ∣ p ^ n + 1 := dvd_trans (dvd_mul_left p 2) h
  rcases n with _ | n
  · rw [pow_zero] at hp'
    exact c.hp2 ((Nat.prime_dvd_prime_iff_eq c.hp Nat.prime_two).mp hp')
  · have : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (Nat.succ_ne_zero n))).mp hp'
    exact c.hp.one_lt.ne' (Nat.dvd_one.mp this)

private theorem normal_Y_K (c : FrobConfig p r t u X Y K) : (Y.subgroupOf K).Normal :=
  (normal_subgroupOf_iff_le_normalizer c.hYK).mpr (c.hKX.trans c.hYn)

private theorem pow_r_mem (c : FrobConfig p r t u X Y K) {k : G} (hk : k ∈ K) : k ^ r ∈ Y := by
  have := c.normal_Y_K
  have h : (⟨k, hk⟩ : ↥K) ^ Y.relIndex K ∈ Y.subgroupOf K := Subgroup.pow_index_mem _ _
  rw [c.hKY, mem_subgroupOf] at h
  simpa using h

private theorem coprime_two_p_r (c : FrobConfig p r t u X Y K) : Nat.Coprime (2 * p) r := by
  rw [Nat.coprime_comm, c.hr.coprime_iff_not_dvd]
  intro h
  rcases (Nat.Prime.dvd_mul c.hr).mp h with h2 | hp'
  · exact c.hr2 ((Nat.prime_dvd_prime_iff_eq c.hr Nat.prime_two).mp h2)
  · exact c.hpr ((Nat.prime_dvd_prime_iff_eq c.hr c.hp).mp hp').symm

private theorem gpow_mem_K_iff (c : FrobConfig p r t u X Y K) (j : ℕ) :
    (t * u) ^ j ∈ K ↔ 2 * p ∣ j := by
  constructor
  · intro h
    have h' := c.pow_r_mem h
    rw [← pow_mul, c.hcomp] at h'
    exact c.coprime_two_p_r.dvd_of_dvd_mul_right h'
  · intro h
    exact c.hYK ((c.hcomp j).mpr h)

private theorem relIndex_K_X (c : FrobConfig p r t u X Y K) : K.relIndex X = 2 * p := by
  have h := Subgroup.relIndex_mul_relIndex Y K X c.hYK c.hKX
  rw [c.hKY, c.hXY] at h
  have hr0 : 0 < r := c.hr.pos
  nlinarith

private theorem exists_zpow_mem [Finite G] (c : FrobConfig p r t u X Y K) {x : G} (hx : x ∈ X) :
    ∃ j : ℤ, ((t * u) ^ j)⁻¹ * x ∈ K := by
  have : (K.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer c.hKX).mpr c.hKn
  set g : ↥X := ⟨t * u, c.hgX⟩
  have hpow : ∀ j : ℕ, ((g : ↥X ⧸ K.subgroupOf X)) ^ j = 1 ↔ 2 * p ∣ j := by
    intro j
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow,
      c.gpow_mem_K_iff]
  have hord : orderOf (g : ↥X ⧸ K.subgroupOf X) = 2 * p := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one ((hpow _).mpr dvd_rfl)
    · exact (hpow _).mp (pow_orderOf_eq_one _)
  have hcard : Nat.card (↥X ⧸ K.subgroupOf X) = 2 * p := c.relIndex_K_X
  have htop : zpowers (g : ↥X ⧸ K.subgroupOf X) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  have hmem : ((⟨x, hx⟩ : ↥X) : ↥X ⧸ K.subgroupOf X) ∈ zpowers (g : ↥X ⧸ K.subgroupOf X) :=
    htop ▸ mem_top _
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  refine ⟨j, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf] at hj
  simpa using hj

private theorem X_le [Finite G] (c : FrobConfig p r t u X Y K) : X ≤ K ⊔ zpowers (t * u) := by
  intro x hx
  obtain ⟨j, hj⟩ := c.exists_zpow_mem hx
  have : x = (t * u) ^ j * (((t * u) ^ j)⁻¹ * x) := by group
  rw [this, sup_comm]
  exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers _) j)) (mem_sup_right hj)

end FrobConfig

end Config

section Config2

open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

private theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [mem_inf, mem_inf, hA, hB]

private theorem isSylowOf_of_isSylowOf_le [Finite G] {p : ℕ} [Fact p.Prime] {S Y₀ Y R : Subgroup G}
    (hS : IsSylowOf p S Y) (hSY₀ : S ≤ Y₀) (hY₀Y : Y₀ ≤ Y) (hR : IsSylowOf p R Y₀) :
    IsSylowOf p R Y := by
  have hS₀ : IsSylowOf p S Y₀ := hS.of_le hSY₀ hY₀Y
  apply isSylowOf_of_card (hR.le.trans hY₀Y)
  rw [hR.card_eq, ← hS₀.card_eq, hS.card_eq]

private theorem exists_hall_ge [Finite G] {X U : Subgroup G} (hUX : U ≤ X)
    (hX : Group.IsSolvable X) (π : Set ℕ) (hU : ∀ q, q.Prime → q ∣ Nat.card U → q ∈ π) :
    ∃ B : Subgroup G, U ≤ B ∧ B ≤ X ∧ (∀ q, q.Prime → q ∣ Nat.card B → q ∈ π) ∧
      ∀ q, q.Prime → q ∣ B.relIndex X → q ∉ π := by
  have hcardU : Nat.card (U.subgroupOf X) = Nat.card U :=
    Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv
  obtain ⟨hall, hle, hhall1, hhall2⟩ :=
    CFSG.SignalizerFunctor.Helpers.solvable_hall_subgroup_containing X π (U.subgroupOf X)
      (fun q hq hdvd => hU q hq (hcardU ▸ hdvd))
  refine ⟨hall.map X.subtype, fun x hx => ?_, map_subtype_le hall, fun q hq hdvd => ?_,
    fun q hq hdvd => ?_⟩
  · exact ⟨⟨x, hUX hx⟩, hle hx, rfl⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective] at hdvd
    exact hhall1 q hq hdvd
  · have h : (hall.map X.subtype).subgroupOf X = hall :=
      comap_map_eq_self_of_injective X.subtype_injective hall
    rw [relIndex, h] at hdvd
    exact hhall2 q hq hdvd

namespace FrobConfig

variable {p r : ℕ} {t u : G} {X Y K : Subgroup G}

private theorem solvable [Finite G] (c : FrobConfig p r t u X Y K) : Group.IsSolvable X := by
  have hYs : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ c.hYodd
  have := c.normal_Y_K
  have : Fact r.Prime := ⟨c.hr⟩
  have hKY : Group.IsSolvable (↥K ⧸ Y.subgroupOf K) := by
    have hcyc : IsCyclic (↥K ⧸ Y.subgroupOf K) := isCyclic_of_prime_card (p := r) c.hKY
    exact Group.isSolvable_of_comm hcyc.commGroup.mul_comm
  have hKs : Group.IsSolvable K := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion c.hYK)
      (QuotientGroup.mk' (Y.subgroupOf K)) ?_
    intro x hx
    rw [QuotientGroup.ker_mk', mem_subgroupOf] at hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have : (K.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer c.hKX).mpr c.hKn
  have hgen : ∀ x : ↥X, ∃ j : ℤ, (x : ↥X ⧸ K.subgroupOf X) =
      (((⟨t * u, c.hgX⟩ : ↥X) ^ j : ↥X) : ↥X ⧸ K.subgroupOf X) := by
    intro x
    obtain ⟨j, hj⟩ := c.exists_zpow_mem x.2
    refine ⟨j, ?_⟩
    rw [eq_comm, QuotientGroup.eq, mem_subgroupOf]
    simpa using hj
  have hXK : Group.IsSolvable (↥X ⧸ K.subgroupOf X) := by
    apply Group.isSolvable_of_comm
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨i, hi⟩ := hgen x
    obtain ⟨j, hj⟩ := hgen y
    rw [hi, hj, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← zpow_add, ← zpow_add,
      add_comm]
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion c.hKX)
    (QuotientGroup.mk' (K.subgroupOf X)) ?_
  intro x hx
  rw [QuotientGroup.ker_mk', mem_subgroupOf] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem restrict [Finite G] (c : FrobConfig p r t u X Y K) {X₀ : Subgroup G}
    (hX₀ : X₀ ≤ X) (hg : t * u ∈ X₀) (hcov : X₀ ⊔ Y = X) {S : Subgroup G}
    (hS : IsSylowOf p S Y) (hSX₀ : S ≤ X₀) :
    FrobConfig p r t u X₀ (Y ⊓ X₀) (K ⊓ X₀) := by
  have : Fact p.Prime := ⟨c.hp⟩
  have hX₀Y : X₀ ≤ normalizer (Y : Set G) := hX₀.trans c.hYn
  have hKdec : K ⊓ X₀ ⊔ Y = K := by
    refine le_antisymm (sup_le inf_le_left c.hYK) fun k hk => ?_
    have hkX : k ∈ (X₀ ⊔ Y : Subgroup G) := hcov ▸ c.hKX hk
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right X₀ Y hX₀Y] at hkX
    obtain ⟨x, hx, y, hy, rfl⟩ := hkX
    have hxK : x ∈ K := by
      have := K.mul_mem hk (K.inv_mem (c.hYK hy))
      simpa using this
    exact mul_mem (mem_sup_left ⟨hxK, hx⟩) (mem_sup_right hy)
  have hgz : zpowers (t * u) ≤ X₀ := zpowers_le.mpr hg
  refine
    { hYK := inf_le_inf_right _ c.hYK
      hKX := inf_le_right
      hYn := fun x hx => mem_normalizer_inf (c.hYn (hX₀ hx)) (le_normalizer hx)
      hKn := fun x hx => mem_normalizer_inf (c.hKn (hX₀ hx)) (le_normalizer hx)
      hYodd := c.hYodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
      hp := c.hp
      hr := c.hr
      hp2 := c.hp2
      hr2 := c.hr2
      hpr := c.hpr
      hXY := ?_
      hKY := ?_
      htX := hgz c.t_mem_zpowers
      huX := hgz c.u_mem_zpowers
      ht := c.ht
      hu := c.hu
      htu := c.htu
      hcomp := fun k => ?_
      hfrob := fun g hg' hgY k hk hgk => ?_
      hcent := fun R hR => ?_ }
  · rw [inf_relIndex_right, ← relIndex_sup_right_of_le_normalizer hX₀Y, hcov, c.hXY]
  · have h1 : Y ⊓ X₀ = Y ⊓ (K ⊓ X₀) := by
      rw [← inf_assoc, inf_eq_left.mpr c.hYK]
    rw [h1, inf_relIndex_right,
      ← relIndex_sup_right_of_le_normalizer (inf_le_right.trans hX₀Y), hKdec, c.hKY]
  · rw [mem_inf, and_iff_left (pow_mem hg k), c.hcomp]
  · have hgY' : g ∉ Y := fun h => hgY ⟨h, hgz hg'⟩
    exact ⟨c.hfrob g hg' hgY' k hk.1 hgk.1, hk.2⟩
  · have hR' := isSylowOf_of_isSylowOf_le hS (le_inf hS.le hSX₀) inf_le_left hR
    intro x hx
    exact ⟨c.hcent R hR' ⟨hX₀ hx.1, hx.2⟩, hx.1⟩

private theorem concl_of_restrict [Finite G] (c : FrobConfig p r t u X Y K) {X₀ S : Subgroup G}
    (hS : IsSylowOf p S Y) (hSX₀ : S ≤ X₀) (h : FrobConcl p t u (Y ⊓ X₀)) :
    FrobConcl p t u Y := by
  have : Fact p.Prime := ⟨c.hp⟩
  obtain ⟨R, hR, hgR, hz⟩ := h
  exact ⟨R, isSylowOf_of_isSylowOf_le hS (le_inf hS.le hSX₀) inf_le_left hR, hgR, hz⟩

end FrobConfig

end Config2

section Minimal

open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

private def MinConfig (p : ℕ) (t u : G) (X Y : Subgroup G) : Prop :=
  ∀ X₁ : Subgroup G, X₁ ≤ X → t * u ∈ X₁ → X₁ ⊔ Y = X → (∃ S, IsSylowOf p S Y ∧ S ≤ X₁) →
    X₁ = X

namespace FrobConfig

variable {p r : ℕ} {t u : G} {X Y K : Subgroup G}

private theorem sup_eq_K (c : FrobConfig p r t u X Y K) {L : Subgroup G} (hLK : L ≤ K)
    (hLY : ¬ L ≤ Y) : L ⊔ Y = K :=
  sup_eq_of_relIndex_prime c.hYK hLK (c.hKY ▸ c.hr) hLY

private theorem sup_eq_X [Finite G] (c : FrobConfig p r t u X Y K) {X₂ : Subgroup G}
    (hX₂ : X₂ ≤ X) (hg : t * u ∈ X₂) (hK : K ≤ X₂ ⊔ Y) : X₂ ⊔ Y = X := by
  refine le_antisymm (sup_le hX₂ (c.hYK.trans c.hKX)) ?_
  refine c.X_le.trans (sup_le hK ?_)
  exact (zpowers_le.mpr hg).trans le_sup_left

private theorem gpow_two_p_pow (c : FrobConfig p r t u X Y K) :
    ∃ n, u ^ p ^ n = 1 ∧ (t * u) ^ (2 * p ^ n) = 1 := by
  obtain ⟨n, hn, -, -⟩ := c.t_u_pow
  refine ⟨n, hn, ?_⟩
  rw [(Commute.mul_pow c.htu), pow_mul t, pow_two, c.mul_self_t, one_pow, one_mul, mul_comm,
    pow_mul, hn, one_pow]

private theorem prime_dvd_card_zpowers (c : FrobConfig p r t u X Y K) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card (zpowers (t * u))) : q = 2 ∨ q = p := by
  obtain ⟨n, -, hn⟩ := c.gpow_two_p_pow
  rw [Nat.card_zpowers] at hdvd
  have h := hdvd.trans (orderOf_dvd_of_pow_eq_one hn)
  rcases (Nat.Prime.dvd_mul hq).mp h with h2 | hpn
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq c.hp).mp (hq.dvd_of_dvd_pow hpn))

private theorem exists_sylow_normalized [Finite G] (c : FrobConfig p r t u X Y K) :
    ∃ R, IsSylowOf p R Y ∧ t * u ∈ normalizer (R : Set G) := by
  have : Fact p.Prime := ⟨c.hp⟩
  obtain ⟨B, hgB, hBX, hBcard, hBidx⟩ := exists_hall_ge (zpowers_le.mpr c.hgX) c.solvable {2, p}
    (fun q hq hdvd => by rcases c.prime_dvd_card_zpowers hq hdvd with h | h <;> simp [h])
  refine ⟨B ⊓ Y, ?_, mem_normalizer_inf (le_normalizer (zpowers_le.mp hgB)) (c.hYn c.hgX)⟩
  rw [isSylowOf_iff]
  refine ⟨inf_le_right, ?_, ?_⟩
  · have hall : ∀ {q}, q.Prime → q ∣ Nat.card (B ⊓ Y : Subgroup G) → q = p := by
      intro q hq hdvd
      have h1 := hBcard q hq (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
      have h2 : q ≠ 2 := by
        rintro rfl
        exact c.hYodd.not_two_dvd_nat (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      exact h1.resolve_left h2
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hall)
  · rw [inf_relIndex_right, ← relIndex_sup_eq_relIndex_of_le_normalizer (hBX.trans c.hYn)]
    intro hdvd
    have hle : Y ⊔ B ≤ X := sup_le (c.hYK.trans c.hKX) hBX
    have hdvd' : p ∣ B.relIndex X :=
      hdvd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex B (Y ⊔ B) X le_sup_right hle))
    exact hBidx p c.hp hdvd' (by simp)

private theorem le_normalizer_sylow [Finite G] (c : FrobConfig p r t u X Y K)
    (hmin : MinConfig p t u X Y) {R : Subgroup G} (hR : IsSylowOf p R Y)
    (hgR : t * u ∈ normalizer (R : Set G)) : X ≤ normalizer (R : Set G) := by
  have : Fact p.Prime := ⟨c.hp⟩
  have hYX : Y ≤ X := c.hYK.trans c.hKX
  have hcov : X ⊓ normalizer (R : Set G) ⊔ Y = X := by
    refine le_antisymm (sup_le inf_le_left hYX) fun x hx => ?_
    have hR' : IsSylowOf p (R.map (MulAut.conj x).toMonoidHom) Y := by
      apply isSylowOf_of_card
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (c.hYn hx) y).mp (hR.le hy)
      · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hR.card_eq]
    obtain ⟨k, hkY, hk⟩ := hR.exists_mem_conj hR'
    have hkx : k⁻¹ * x ∈ X ⊓ normalizer (R : Set G) := by
      refine mem_inf.mpr ⟨X.mul_mem (X.inv_mem (hYX hkY)) hx, ?_⟩
      rw [mem_normalizer_iff]
      intro ρ
      have h2 : x * ρ * x⁻¹ ∈ R.map (MulAut.conj x).toMonoidHom ↔ ρ ∈ R := by
        constructor
        · rintro ⟨y, hy, hyx⟩
          have hyρ : y = ρ := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
            simpa using hyx
          rwa [← hyρ]
        · intro hρ
          exact ⟨ρ, hρ, rfl⟩
      rw [← h2, hk (x * ρ * x⁻¹)]
      have : k⁻¹ * x * ρ * (k⁻¹ * x)⁻¹ = k⁻¹ * (x * ρ * x⁻¹) * k := by group
      rw [this]
    have : x = k * (k⁻¹ * x) := by group
    rw [this, sup_comm]
    exact mul_mem (mem_sup_left hkY) (mem_sup_right hkx)
  have h := hmin _ inf_le_left ⟨c.hgX, hgR⟩ hcov
    ⟨R, hR, le_inf (hR.le.trans hYX) le_normalizer⟩
  rw [← h]
  exact inf_le_right

private theorem prime_dvd_card_X [Finite G] (c : FrobConfig p r t u X Y K)
    (hmin : MinConfig p t u X Y) {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card X) :
    q = 2 ∨ q = p ∨ q = r := by
  have : Fact p.Prime := ⟨c.hp⟩
  obtain ⟨X₁, hgX₁, hX₁X, hX₁card, hX₁idx⟩ := exists_hall_ge (zpowers_le.mpr c.hgX) c.solvable
    {2, p, r} (fun q hq hdvd => by rcases c.prime_dvd_card_zpowers hq hdvd with h | h <;> simp [h])
  have hcov : X₁ ⊔ Y = X := by
    have hle : X₁ ⊔ Y ≤ X := sup_le hX₁X (c.hYK.trans c.hKX)
    have h1 := Subgroup.relIndex_mul_relIndex X₁ (X₁ ⊔ Y) X le_sup_left hle
    have h2 := Subgroup.relIndex_mul_relIndex Y (X₁ ⊔ Y) X le_sup_right hle
    rw [c.hXY] at h2
    by_contra hne
    have hidx : (X₁ ⊔ Y).relIndex X ≠ 1 := fun h => hne (le_antisymm hle (relIndex_eq_one.mp h))
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hidx
    have hq1 : q ∣ X₁.relIndex X := hqd.trans (Dvd.intro_left _ h1)
    have hq2 : q ∣ 2 * p * r := hqd.trans (Dvd.intro_left _ h2)
    apply hX₁idx q hq hq1
    rcases (Nat.Prime.dvd_mul hq).mp hq2 with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · simp [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h]
      · simp [(Nat.prime_dvd_prime_iff_eq hq c.hp).mp h]
    · simp [(Nat.prime_dvd_prime_iff_eq hq c.hr).mp h]
  obtain ⟨S, hS⟩ := exists_isSylowOf p (X₁ ⊓ Y)
  have hSY : IsSylowOf p S Y := by
    rw [isSylowOf_iff] at hS ⊢
    refine ⟨hS.1.trans inf_le_right, hS.2.1, fun hdvd => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S (X₁ ⊓ Y) Y hS.1 inf_le_right] at hdvd
    rcases (Nat.Prime.dvd_mul c.hp).mp hdvd with h | h
    · exact hS.2.2 h
    · rw [inf_relIndex_right, ← relIndex_sup_eq_relIndex_of_le_normalizer (hX₁X.trans c.hYn)] at h
      have hle : Y ⊔ X₁ ≤ X := sup_le (c.hYK.trans c.hKX) hX₁X
      exact hX₁idx p c.hp (h.trans (Dvd.intro _
        (Subgroup.relIndex_mul_relIndex X₁ (Y ⊔ X₁) X le_sup_right hle))) (by simp)
  have hX₁ := hmin X₁ hX₁X (zpowers_le.mp hgX₁) hcov ⟨S, hSY, hS.le.trans inf_le_left⟩
  rw [← hX₁] at hdvd
  have h := hX₁card q hq hdvd
  simpa using h

private theorem relIndex_sylow_K [Finite G] (c : FrobConfig p r t u X Y K)
    (hmin : MinConfig p t u X Y) {R : Subgroup G} (hR : IsSylowOf p R Y) :
    ∃ e, R.relIndex K = r ^ e := by
  have : Fact p.Prime := ⟨c.hp⟩
  have hRY : ∀ {q}, q.Prime → q ∣ R.relIndex Y → q = r := by
    intro q hq hdvd
    have hqY : q ∣ Nat.card Y := hdvd.trans (Subgroup.index_dvd_card _)
    rcases c.prime_dvd_card_X hmin hq
        (hqY.trans (Subgroup.card_dvd_of_le (c.hYK.trans c.hKX))) with h | h | h
    · exact absurd (h ▸ hqY) c.hYodd.not_two_dvd_nat
    · exact absurd (h ▸ hdvd) (isSylowOf_iff.mp hR).2.2
    · exact h
  have hne : R.relIndex Y ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨(R.relIndex Y).primeFactorsList.length + 1, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex R Y K hR.le c.hYK, c.hKY, pow_succ,
    ← Nat.eq_prime_pow_of_unique_prime_dvd hne hRY]

private theorem gpow_two_p_mem [Finite G] (c : FrobConfig p r t u X Y K) {R : Subgroup G}
    (hR : IsSylowOf p R Y) (hgR : t * u ∈ normalizer (R : Set G)) : (t * u) ^ (2 * p) ∈ R := by
  have : Fact p.Prime := ⟨c.hp⟩
  obtain ⟨n, hn, -⟩ := c.gpow_two_p_pow
  have hzY : (t * u) ^ (2 * p) ∈ Y := (c.hcomp _).mpr dvd_rfl
  have hz : (t * u) ^ (2 * p) = u ^ (2 * p) := by
    rw [(Commute.mul_pow c.htu), pow_mul t, pow_two, c.mul_self_t, one_pow, one_mul]
  have hzp : IsPGroup p (zpowers ((t * u) ^ (2 * p))) := by
    have hdvd : orderOf ((t * u) ^ (2 * p)) ∣ p ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hz, ← pow_mul, mul_comm, pow_mul, hn, one_pow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow c.hp).mp hdvd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hP := IsPGroup.to_sup_of_normal_left' hR.isPGroup hzp (zpowers_le.mpr (pow_mem hgR _))
  have heq := hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hzY)) hP
  exact heq ▸ mem_sup_right (mem_zpowers _)

private theorem zpow_mem_of_mem_K [Finite G] (c : FrobConfig p r t u X Y K) {R : Subgroup G}
    (hR : IsSylowOf p R Y) (hgR : t * u ∈ normalizer (R : Set G)) {j : ℤ}
    (h : (t * u) ^ j ∈ K) : (t * u) ^ j ∈ R := by
  have hmem : (t * u) ^ j ∈ Submonoid.powers (t * u) :=
    mem_powers_iff_mem_zpowers.mpr (zpow_mem (mem_zpowers _) j)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
  rw [← hn] at h ⊢
  obtain ⟨m, rfl⟩ := (c.gpow_mem_K_iff n).mp h
  rw [pow_mul]
  exact pow_mem (c.gpow_two_p_mem hR hgR) m

private theorem eq_K_of_invariant [Finite G] (c : FrobConfig p r t u X Y K)
    (hmin : MinConfig p t u X Y) {R : Subgroup G} (hR : IsSylowOf p R Y)
    (hgR : t * u ∈ normalizer (R : Set G)) {L : Subgroup G} (hRL : R ≤ L) (hLK : L ≤ K)
    (hgL : ∀ x ∈ L, t * u * x * (t * u)⁻¹ ∈ L) (hLY : ¬ L ≤ Y) : L = K := by
  have hgN : t * u ∈ normalizer (L : Set G) := mem_normalizer_of_conj_mem hgL
  have hzL : zpowers (t * u) ≤ normalizer (L : Set G) := zpowers_le.mpr hgN
  have hX₂X : zpowers (t * u) ⊔ L ≤ X := sup_le (zpowers_le.mpr c.hgX) (hLK.trans c.hKX)
  have hgX₂ : t * u ∈ zpowers (t * u) ⊔ L := mem_sup_left (mem_zpowers _)
  have hX₂ : zpowers (t * u) ⊔ L = X := hmin _ hX₂X hgX₂
    (c.sup_eq_X hX₂X hgX₂ ((c.sup_eq_K hLK hLY).symm.le.trans (sup_le_sup_right le_sup_right Y)))
    ⟨R, hR, hRL.trans le_sup_right⟩
  refine le_antisymm hLK fun k hk => ?_
  have hkX₂ : k ∈ zpowers (t * u) ⊔ L := hX₂ ▸ c.hKX hk
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hzL] at hkX₂
  obtain ⟨g', hg', l, hl, rfl⟩ := hkX₂
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg'
  have hgK : (t * u) ^ j ∈ K := by
    have := K.mul_mem hk (K.inv_mem (hLK hl))
    simpa using this
  exact L.mul_mem (hRL (c.zpow_mem_of_mem_K hR hgR hgK)) hl

end FrobConfig

end Minimal

section Cyclic

open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

private theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {x : G} {a b : ℕ}
    (hab : a.Coprime b) (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ∈ H := by
  have h : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← Nat.gcd_eq_gcd_ab, hab.gcd_eq_one, Nat.cast_one, zpow_one]
  rw [h]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

namespace FrobConfig

variable {p r : ℕ} {t u : G} {X Y K : Subgroup G}

private theorem exists_r_elt [Finite G] (c : FrobConfig p r t u X Y K) :
    ∃ k ∈ K, k ∉ Y ∧ ∃ a, orderOf k = r ^ a := by
  have hYK : ¬ K ≤ Y := by
    intro h
    have := relIndex_eq_one.mpr h
    rw [c.hKY] at this
    exact c.hr.one_lt.ne' this
  obtain ⟨y, hyK, hyY⟩ := IsConcreteLE.not_le_iff_exists.mp hYK
  obtain ⟨a, m, hm, hym⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' r c.hr.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero r)
  refine ⟨y ^ m, pow_mem hyK m, fun h => hyY ?_, a, ?_⟩
  · exact mem_of_pow_mem_of_coprime (Nat.coprime_comm.mp ((c.hr.coprime_iff_not_dvd).mpr hm)) h
      (c.pow_r_mem hyK)
  · rw [orderOf_pow_of_dvd hm0 ⟨r ^ a, by rw [hym, mul_comm]⟩, hym,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

private theorem forall_mem_K [Finite G] (c : FrobConfig p r t u X Y K)
    (hmin : MinConfig p t u X Y) {R : Subgroup G} (hR : IsSylowOf p R Y)
    (hgR : t * u ∈ normalizer (R : Set G)) (hRX : X ≤ normalizer (R : Set G)) {k : G}
    (hkK : k ∈ K) (hkY : k ∉ Y) : ∀ z ∈ K, ∃ ρ ∈ R, ∃ i : ℕ, z = ρ * k ^ i := by
  have : Fact r.Prime := ⟨c.hr⟩
  have hRK : R ≤ K := hR.le.trans c.hYK
  have : (R.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRK).mpr (c.hKX.trans hRX)
  set Q := ↥K ⧸ R.subgroupOf K
  set π := QuotientGroup.mk' (R.subgroupOf K)
  obtain ⟨e, he⟩ := c.relIndex_sylow_K hmin hR
  have hQ : IsPGroup r Q := IsPGroup.of_card (n := e) he
  have hgK : t * u ∈ normalizer (K : Set G) := c.hKn c.hgX
  have hgR' : t * u ∈ normalizer (R : Set G) := hgR
  set T := quotConj K R (t * u) hgK hgR'
  have hT : ∀ x : ↥K, T (π x) = π ⟨t * u * x * (t * u)⁻¹,
      (mem_normalizer_iff.mp hgK x).mp x.2⟩ := fun x => quotConj_mk K R _ hgK hgR' x
  have hTN : ∀ q, T^[orderOf (t * u)] q = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf K) q
    change T^[orderOf (t * u)] (x : Q) = x
    rw [quotConj_iterate_mk]
    congr 1
    apply Subtype.ext
    simp [pow_orderOf_eq_one]
  have hrN : ¬ r ∣ orderOf (t * u) := by
    intro hdvd
    obtain ⟨n, -, hn⟩ := c.gpow_two_p_pow
    have h1 := hdvd.trans (orderOf_dvd_of_pow_eq_one hn)
    rcases (Nat.Prime.dvd_mul c.hr).mp h1 with h | h
    · exact c.hr2 ((Nat.prime_dvd_prime_iff_eq c.hr Nat.prime_two).mp h)
    · exact c.hpr ((Nat.prime_dvd_prime_iff_eq c.hr c.hp).mp (c.hr.dvd_of_dvd_pow h)).symm
  set Y₁ : Subgroup Q := (Y.subgroupOf K).map π
  have : Y₁.Normal := by
    have := c.normal_Y_K
    exact Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hmemY₁ : ∀ x : ↥K, π x ∈ Y₁ ↔ (x : G) ∈ Y := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
      have h := QuotientGroup.eq.mp hyx
      rw [mem_subgroupOf] at h hy
      have := Y.mul_mem hy (hR.le h)
      simpa using this
    · intro hx
      exact mem_map_of_mem π (mem_subgroupOf.mpr hx)
  have hTY : ∀ y ∈ Y₁, T y ∈ Y₁ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    rw [hT, hmemY₁]
    exact (mem_normalizer_iff.mp (c.hYn c.hgX) x).mp (mem_subgroupOf.mp hx)
  have hY₁ : Y₁.index = r := by
    rw [Subgroup.index_map, (MonoidHom.range_eq_top_of_surjective _
      (QuotientGroup.mk'_surjective _)), Subgroup.index_top, mul_one, QuotientGroup.ker_mk',
      sup_eq_left.mpr (fun x hx => mem_subgroupOf.mpr (hR.le (mem_subgroupOf.mp hx)))]
    exact c.hKY
  have hinv : ∀ L : Subgroup Q, (∀ x ∈ L, T x ∈ L) → ¬ L ≤ Y₁ → L = ⊤ := by
    intro L hLT hLY
    set L' : Subgroup G := (L.comap π).map K.subtype
    have hRL : R ≤ L' := by
      intro ρ hρ
      refine ⟨⟨ρ, hRK hρ⟩, ?_, rfl⟩
      have h1 : π ⟨ρ, hRK hρ⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hρ
      change π _ ∈ L
      rw [h1]
      exact L.one_mem
    have hLK : L' ≤ K := map_subtype_le _
    have hgL : ∀ x ∈ L', t * u * x * (t * u)⁻¹ ∈ L' := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨t * u * x * (t * u)⁻¹, (mem_normalizer_iff.mp hgK x).mp x.2⟩, ?_, rfl⟩
      change π _ ∈ L
      rw [← hT]
      exact hLT _ hx
    have hL'Y : ¬ L' ≤ Y := by
      intro h
      apply hLY
      intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf K) q
      exact (hmemY₁ x).mpr (h ⟨x, hq, rfl⟩)
    have hL'K := c.eq_K_of_invariant hmin hR hgR hRL hLK hgL hL'Y
    rw [eq_top_iff]
    rintro q -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf K) q
    have hx : (x : G) ∈ L' := by
      rw [hL'K]
      exact x.2
    obtain ⟨x', hx', hxx'⟩ := hx
    rw [Subtype.ext hxx'] at hx'
    exact hx'
  have hk1 : zpowers (π ⟨k, hkK⟩) = ⊤ := by
    apply eq_top_of_not_le_of_invariant hQ T hTN hrN Y₁ hTY hY₁ hinv
    intro h
    exact hkY ((hmemY₁ _).mp (h (mem_zpowers _)))
  intro z hz
  have hzQ : π ⟨z, hz⟩ ∈ Submonoid.powers (π ⟨k, hkK⟩) := by
    rw [mem_powers_iff_mem_zpowers, hk1]
    exact mem_top _
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp hzQ
  rw [← map_pow, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    mem_subgroupOf] at hi
  refine ⟨z * (k ^ i)⁻¹, ?_, i, by group⟩
  have h2 := (mem_normalizer_iff.mp (hRX (c.hKX hz)) _).mp (R.inv_mem hi)
  convert h2 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  group

end FrobConfig

end Cyclic

section Core

open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

private theorem fix_pow {H₀ : Subgroup G} {g x : G} (hg : g ∈ normalizer (H₀ : Set G))
    (h : g * x * g⁻¹ * x⁻¹ ∈ H₀) (n : ℕ) : g ^ n * x * (g ^ n)⁻¹ * x⁻¹ ∈ H₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := H₀.mul_mem ((mem_normalizer_iff.mp hg _).mp ih) h
    convert h1 using 1
    rw [pow_succ']
    group

private theorem fix_mul {H H₀ : Subgroup G} {ρ g x : G} (hρ : ∀ y ∈ H, ρ * y * ρ⁻¹ * y⁻¹ ∈ H₀)
    (hgH : g ∈ normalizer (H : Set G)) (hx : x ∈ H) (h : g * x * g⁻¹ * x⁻¹ ∈ H₀) :
    ρ * g * x * (ρ * g)⁻¹ * x⁻¹ ∈ H₀ := by
  have h1 := H₀.mul_mem (hρ _ ((mem_normalizer_iff.mp hgH x).mp hx)) h
  convert h1 using 1
  group

namespace FrobConfig

variable {p r : ℕ} {t u : G} {X Y K : Subgroup G}

private theorem exists_exponent_p_subgroup [Finite G] (c : FrobConfig p r t u X Y K)
    {R : Subgroup G} (hR : IsSylowOf p R Y) (hRX : X ≤ normalizer (R : Set G)) {k : G}
    (hkK : k ∈ K) (hkY : k ∉ Y) {a : ℕ} (hka : orderOf k = r ^ a) :
    ∃ D : Subgroup G, D ≤ R ∧ X ≤ normalizer (D : Set G) ∧ (∀ z ∈ D, z ^ p = 1) ∧
      ¬ ∀ z ∈ D, k * z = z * k := by
  have : Fact p.Prime := ⟨c.hp⟩
  have hkX : k ∈ X := c.hKX hkK
  have hRne : R ≠ ⊥ := by
    rintro rfl
    have h : X ≤ Y := fun x hx => c.hcent ⊥ hR (mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr
      fun y hy => by
        rw [SetLike.mem_coe, mem_bot] at hy
        rw [hy, one_mul, mul_one]⟩)
    have h1 := relIndex_eq_one.mpr h
    rw [c.hXY] at h1
    have := c.hp.two_le
    have := c.hr.two_le
    nlinarith
  have : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hRne
  obtain ⟨D, hDchar, -, -, hDp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup c.hp2 hR.isPGroup
  refine ⟨D.map R.subtype, map_subtype_le D, fun x hx => ?_, ?_, fun hcomm => ?_⟩
  · apply mem_normalizer_of_conj_mem
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨R.normalizerMonoidHom ⟨x, hRX hx⟩ d,
      CFSG.SectionRank.Ccomm.char_apply_mem hDchar _ hd, ?_⟩
    rw [subtype_apply, normalizerMonoidHom_apply_apply_coe]
    rfl
  · rintro _ ⟨d, hd, rfl⟩
    rw [subtype_apply, ← Subgroup.coe_pow, hDp d hd, Subgroup.coe_one]
  · set φ := R.normalizerMonoidHom ⟨k, hRX hkX⟩
    have hφfix : φ ∈ fixingSubgroup (MulAut R) (D : Set R) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      rw [MulAut.smul_def, normalizerMonoidHom_apply_apply_coe]
      change k * (d : G) * k⁻¹ = d
      rw [hcomm d ⟨d, hd, rfl⟩, mul_inv_cancel_right]
    obtain ⟨n, hn⟩ := hfix ⟨φ, hφfix⟩
    have h1 : orderOf φ ∣ p ^ n := by
      rw [← Subgroup.orderOf_mk φ hφfix]
      exact orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf φ ∣ r ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have : (⟨k, hRX hkX⟩ : ↥(normalizer (R : Set G))) ^ r ^ a = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hka, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [this, map_one]
    have hcop : (p ^ n).Coprime (r ^ a) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes c.hp c.hr).mpr c.hpr)
    have hφ1 : φ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    apply hkY
    refine c.hcent R hR (mem_inf.mpr ⟨hkX, mem_centralizer_iff.mpr fun ρ hρ => ?_⟩)
    have h3 := congrArg (fun ψ : MulAut R => ((ψ ⟨ρ, hρ⟩ : R) : G)) hφ1
    simp only [φ, normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
    calc ρ * k = k * ρ * k⁻¹ * k := by rw [h3]
      _ = k * ρ := by group

end FrobConfig

end Core

section Core2

open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

namespace FrobConfig

variable {p r : ℕ} {t u : G} {X Y K : Subgroup G}

private theorem core [Finite G] (c : FrobConfig p r t u X Y K) (hmin : MinConfig p t u X Y)
    {R : Subgroup G} (hR : IsSylowOf p R Y) (hgR : t * u ∈ normalizer (R : Set G)) :
    ∃ z ∈ R, z * t = t * z ∧ z ^ p = 1 ∧ z * u ≠ u * z := by
  have : Fact p.Prime := ⟨c.hp⟩
  have hRX := c.le_normalizer_sylow hmin hR hgR
  obtain ⟨k, hkK, hkY, a, hka⟩ := c.exists_r_elt
  have hKk := c.forall_mem_K hmin hR hgR hRX hkK hkY
  obtain ⟨D, hDR, hXD, hDp, hkD⟩ := c.exists_exponent_p_subgroup hR hRX hkK hkY hka
  have hkX : k ∈ X := c.hKX hkK
  have hYX : Y ≤ X := c.hYK.trans c.hKX
  have hRXle : R ≤ X := hR.le.trans hYX
  have hkcop : (orderOf k).Coprime p := by
    rw [hka]
    exact Nat.Coprime.pow_left a ((Nat.coprime_primes c.hr c.hp).mpr c.hpr.symm)
  let 𝓗 : Set (Subgroup G) :=
    {H | H ≤ D ∧ X ≤ normalizer (H : Set G) ∧ ¬ ∀ z ∈ H, k * z = z * k}
  obtain ⟨H, hHmin⟩ := 𝓗.toFinite.exists_minimal ⟨D, le_rfl, hXD, hkD⟩
  obtain ⟨hHD, hXH, hkH⟩ := hHmin.prop
  have hHR : H ≤ R := hHD.trans hDR
  have hHne : H ≠ ⊥ := by
    rintro rfl
    exact hkH fun z hz => by rw [mem_bot.mp hz, one_mul, mul_one]
  let 𝓜 : Set (Subgroup G) := {M | M < H ∧ X ≤ normalizer (M : Set G)}
  have hbot : (⊥ : Subgroup G) ∈ 𝓜 := ⟨bot_lt_iff_ne_bot.mpr hHne, fun x _ => by
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_bot]⟩
  obtain ⟨H₀, hH₀max⟩ := 𝓜.toFinite.exists_maximal ⟨⊥, hbot⟩
  obtain ⟨hH₀H, hXH₀⟩ := hH₀max.prop
  have hmax : ∀ M : Subgroup G, H₀ < M → M ≤ H → X ≤ normalizer (M : Set G) → M = H := by
    intro M hM hMH hXM
    by_contra hne
    exact hM.not_ge (hH₀max.le_of_ge ⟨lt_of_le_of_ne hMH hne, hXM⟩ hM.le)
  have hH₀n : H ≤ normalizer (H₀ : Set G) := fun h hh => hXH₀ (hRXle (hHR hh))
  have hH₀p : IsPGroup p H₀ := hR.isPGroup.to_le (hH₀H.le.trans hHR)
  have hHp : IsPGroup p H := hR.isPGroup.to_le hHR
  have hHodd : Odd (Nat.card H) := by
    obtain ⟨m, hm⟩ := hHp.exists_card_eq
    rw [hm]
    exact c.odd_p.pow
  have hH₀odd : Odd (Nat.card H₀) := hHodd.of_dvd_nat (Subgroup.card_dvd_of_le hH₀H.le)
  have hH₀cent : ∀ B : Subgroup G, B ≤ X → H₀ ≤ centSub H (B : Set G) H₀ hH₀n := by
    intro B hBX h hh
    refine ⟨hH₀H.le hh, fun β hβ => ?_⟩
    have := H₀.mul_mem hh ((mem_normalizer_iff.mp (hXH₀ (hBX hβ)) _).mp (H₀.inv_mem hh))
    convert this using 1
    group
  obtain ⟨b, hbH, hbH₀, hb⟩ := exists_mem_forall_commutator_mem hR.isPGroup hH₀H hHR
    (hRXle.trans hXH₀) (hRXle.trans hXH)
  have hC₃ : centSub H (R : Set G) H₀ hH₀n = H :=
    hmax _ (lt_of_le_of_ne (hH₀cent R hRXle) fun h => hbH₀ (h ▸ ⟨hbH, hb⟩))
      (fun x hx => hx.1) (le_normalizer_centSub hH₀n hXH hRX hXH₀)
  have hRtriv : ∀ ρ ∈ R, ∀ y ∈ H, ρ * y * ρ⁻¹ * y⁻¹ ∈ H₀ := by
    intro ρ hρ y hy
    have hyC : y ∈ centSub H (R : Set G) H₀ hH₀n := by rw [hC₃]; exact hy
    have := H₀.inv_mem (hyC.2 ρ hρ)
    convert this using 1
    group
  have hab : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ H₀ := fun a ha b hb =>
    hRtriv a (hHR ha) b hb
  have hkH₀ : ∀ z ∈ H₀, k * z = z * k := by
    by_contra h
    exact hH₀H.not_ge (hHmin.le_of_le ⟨hH₀H.le.trans hHD, hXH₀, h⟩ hH₀H.le)
  have hkfix : ∀ h ∈ H, k * h * k⁻¹ * h⁻¹ ∈ H₀ → h ∈ H₀ := by
    have hC₄ne : centSub H (K : Set G) H₀ hH₀n ≠ H := by
      intro hC₄
      apply hkH
      intro z hz
      have hzC : z ∈ centSub H (K : Set G) H₀ hH₀n := by rw [hC₄]; exact hz
      have h1 := H₀.inv_mem (hzC.2 k hkK)
      have h2 : z⁻¹ * (k * z * k⁻¹) ∈ H₀ := by
        have := (mem_normalizer_iff.mp (hH₀n (H.inv_mem hz)) _).mp h1
        convert this using 1
        group
      have h3 := conj_eq_of_mem_of_coprime hH₀p hkcop hkH₀ h2
      calc k * z = k * z * k⁻¹ * k := by group
        _ = z * k := by rw [h3]
    have hC₄ : centSub H (K : Set G) H₀ hH₀n = H₀ := by
      by_contra hne
      exact hC₄ne (hmax _ (lt_of_le_of_ne (hH₀cent K c.hKX) (Ne.symm hne)) (fun x hx => hx.1)
        (le_normalizer_centSub hH₀n hXH c.hKn hXH₀))
    intro h hh hkh
    rw [← hC₄]
    refine ⟨hh, fun κ hκ => ?_⟩
    obtain ⟨ρ, hρ, i, rfl⟩ := hKk κ hκ
    have h1 := fix_mul (hRtriv ρ hρ) (pow_mem (hXH hkX) i) hh (fix_pow (hXH₀ hkX) hkh i)
    have := H₀.inv_mem h1
    convert this using 1
    group
  have hfpf : ∀ m ∈ K, m ∉ Y → ∀ h ∈ H, m * h * m⁻¹ * h⁻¹ ∈ H₀ → h ∈ H₀ := by
    intro m hm hmY h hh hmh
    obtain ⟨ρ, hρ, i, rfl⟩ := hKk m hm
    have hi : ¬ r ∣ i := by
      rintro ⟨j, rfl⟩
      apply hmY
      rw [pow_mul]
      exact mul_mem (hR.le hρ) (pow_mem (c.pow_r_mem hkK) j)
    have h1 : k ^ i * h * (k ^ i)⁻¹ * h⁻¹ ∈ H₀ := by
      have := fix_mul (hRtriv ρ⁻¹ (R.inv_mem hρ))
        (mul_mem (hXH (hRXle hρ)) (pow_mem (hXH hkX) i)) hh hmh
      convert this using 1
      group
    have hcop : i.Coprime (orderOf k) := by
      rw [hka]
      exact Nat.Coprime.pow_right a (Nat.coprime_comm.mp ((c.hr.coprime_iff_not_dvd).mpr hi))
    obtain ⟨j, hj⟩ : ∃ j, k ^ (i * j) = k := by
      rcases Nat.lt_or_ge 1 (orderOf k) with h1 | h1
      · obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
        exact ⟨j, by rw [← pow_mod_orderOf, hj, pow_one]⟩
      · have hk1 : orderOf k = 1 := le_antisymm h1 (orderOf_pos k)
        rw [orderOf_eq_one_iff] at hk1
        exact ⟨0, by simp [hk1]⟩
    have h2 := fix_pow (pow_mem (hXH₀ hkX) i) h1 j
    rw [← pow_mul, hj] at h2
    exact hkfix h hh h2
  have hcommK : ∀ g ∈ X, g * k * g⁻¹ * k⁻¹ ∈ K := fun g hg =>
    mul_mem ((mem_normalizer_iff.mp (c.hKn hg) k).mp hkK) (K.inv_mem hkK)
  have hcommY : ∀ g ∈ zpowers (t * u), g ∉ Y → g * k * g⁻¹ * k⁻¹ ∉ Y := fun g hg hgY h =>
    hkY (c.hfrob g hg hgY k hkK h)
  obtain ⟨n, hn⟩ := c.hu
  obtain ⟨h, hh, hth, huh⟩ := exists_fixed_not_fixed_mod hH₀H hH₀n hab hHp hHodd
    (hXH c.htX) (hXH₀ c.htX) (hXH c.huX) (hXH₀ c.huX) (hXH hkX) (hXH₀ hkX) c.mul_self_t hn c.htu
    (hfpf _ (hcommK t c.htX) (hcommY t c.t_mem_zpowers c.t_not_mem))
    (hfpf _ (hcommK u c.huX) (hcommY u c.u_mem_zpowers c.u_not_mem))
  have hc : h⁻¹ * (t * h * t⁻¹) ∈ H₀ := by
    have := (mem_normalizer_iff.mp (hH₀n (H.inv_mem hh)) _).mp hth
    convert this using 1
    group
  obtain ⟨a, ha, hta⟩ := exists_mem_commute_mul hH₀odd c.mul_self_t hc
  have hzH : h * a ∈ H := H.mul_mem hh (hH₀H.le ha)
  refine ⟨h * a, hHR hzH, hta.symm, hDp _ (hHD hzH), fun hzu => huh ?_⟩
  have h1 : u * a⁻¹ * u⁻¹ * a ∈ H₀ :=
    H₀.mul_mem ((mem_normalizer_iff.mp (hXH₀ c.huX) _).mp (H₀.inv_mem ha)) ha
  have h2 := (mem_normalizer_iff.mp (hH₀n hzH) _).mp h1
  have hz : u * (h * a) * u⁻¹ = h * a := by
    rw [← hzu, mul_inv_cancel_right]
  have h3 : u * h * u⁻¹ * h⁻¹ = h * a * (u * a⁻¹ * u⁻¹ * a) * (h * a)⁻¹ := by
    calc u * h * u⁻¹ * h⁻¹ = (u * (h * a) * u⁻¹) * (u * a⁻¹ * u⁻¹ * a) * (h * a)⁻¹ := by group
      _ = h * a * (u * a⁻¹ * u⁻¹ * a) * (h * a)⁻¹ := by rw [hz]
  rw [h3]
  exact h2

end FrobConfig

end Core2

theorem exists_sylow_not_centralizes_fixed_omega {G : Type u} [Group G] [Finite G]
    {X Y K : Subgroup G} (hYK : Y ≤ K) (hKX : K ≤ X)
    (hYn : X ≤ Subgroup.normalizer (Y : Set G)) (hKn : X ≤ Subgroup.normalizer (K : Set G))
    (hYodd : Odd (Nat.card Y)) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2)
    (hr2 : r ≠ 2) (hpr : p ≠ r) (hXY : Y.relIndex X = 2 * p * r) (hKY : Y.relIndex K = r)
    {t u : G} (htX : t ∈ X) (huX : u ∈ X) (ht : orderOf t = 2) (hu : ∃ n : ℕ, u ^ p ^ n = 1)
    (htu : t * u = u * t) (hcomp : ∀ k : ℕ, (t * u) ^ k ∈ Y ↔ 2 * p ∣ k)
    (hfrob : ∀ g ∈ Subgroup.zpowers (t * u), g ∉ Y → ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ Y → k ∈ Y)
    (hcent : ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p R Y →
      X ⊓ Subgroup.centralizer (R : Set G) ≤ Y) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p R Y ∧
      t * u ∈ Subgroup.normalizer (R : Set G) ∧
        ∃ z ∈ R, z * t = t * z ∧ z ^ p = 1 ∧ z * u ≠ u * z := by
  have c : FrobConfig p r t u X Y K := ⟨hYK, hKX, hYn, hKn, hYodd, hp, hr, hp2, hr2, hpr, hXY,
    hKY, htX, huX, ht, hu, htu, hcomp, hfrob, hcent⟩
  have : Fact p.Prime := ⟨hp⟩
  let F : Set (Subgroup G) := {X₀ | X₀ ≤ X ∧ t * u ∈ X₀ ∧ X₀ ⊔ Y = X ∧
    ∃ S, CFSG.ABGLocalTools.IsSylowOf p S Y ∧ S ≤ X₀}
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf p Y
  have hXF : X ∈ F :=
    ⟨le_rfl, c.hgX, sup_eq_left.mpr (hYK.trans hKX), S, hS, hS.le.trans (hYK.trans hKX)⟩
  obtain ⟨X₀, hX₀⟩ := F.toFinite.exists_minimal ⟨X, hXF⟩
  obtain ⟨hX₀X, hgX₀, hcov, S₀, hS₀, hS₀X₀⟩ := hX₀.prop
  have c₀ := c.restrict hX₀X hgX₀ hcov hS₀ hS₀X₀
  have hmin : MinConfig p t u X₀ (Y ⊓ X₀) := by
    rintro X₁ hX₁ hgX₁ hcov₁ ⟨S₁, hS₁, hS₁X₁⟩
    have hS₁Y := isSylowOf_of_isSylowOf_le hS₀ (le_inf hS₀.le hS₀X₀) inf_le_left hS₁
    have hcov₁' : X₁ ⊔ Y = X := by
      refine le_antisymm (sup_le (hX₁.trans hX₀X) (hYK.trans hKX)) ?_
      rw [← hcov, ← hcov₁]
      exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
    exact le_antisymm hX₁ (hX₀.le_of_le ⟨hX₁.trans hX₀X, hgX₁, hcov₁', S₁, hS₁Y, hS₁X₁⟩ hX₁)
  obtain ⟨R, hR, hgR⟩ := c₀.exists_sylow_normalized
  exact c.concl_of_restrict hS₀ hS₀X₀ ⟨R, hR, hgR, c₀.core hmin hR hgR⟩

end CFSG.ABGTheoremB
