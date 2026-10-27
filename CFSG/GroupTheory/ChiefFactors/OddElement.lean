module

import CFSG.GroupTheory.CommutatorMemSubgroup
public import Mathlib.GroupTheory.PGroup

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

private def chiefCentralizer (K R₁ R₂ : Subgroup G)
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G)) : Subgroup G :=
  ⨅ k : K, commMemSubgroup R₁ R₂ hR₁₂ (k : G)

private lemma mem_chiefCentralizer {K R₁ R₂ : Subgroup G}
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G)) {r : G} :
    r ∈ chiefCentralizer K R₁ R₂ hR₁₂ ↔
      r ∈ R₁ ∧ ∀ k : K, ⁅r, (k : G)⁆ ∈ R₂ := by
  constructor
  · intro hr
    change r ∈ ⨅ k : K, commMemSubgroup R₁ R₂ hR₁₂ (k : G) at hr
    have h1 : r ∈ R₁ := (Subgroup.mem_iInf.mp hr ⟨1, K.one_mem⟩).1
    exact ⟨h1, fun k => (Subgroup.mem_iInf.mp hr k).2⟩
  · rintro ⟨hrR, hk⟩
    change r ∈ ⨅ k : K, commMemSubgroup R₁ R₂ hR₁₂ (k : G)
    rw [Subgroup.mem_iInf]
    intro k
    exact ⟨hrR, hk k⟩

private lemma chiefCentralizer_le (K R₁ R₂ : Subgroup G)
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G)) :
    chiefCentralizer K R₁ R₂ hR₁₂ ≤ R₁ := by
  intro r hr
  exact (mem_chiefCentralizer hR₁₂).mp hr |>.1

private lemma le_chiefCentralizer {N K R₁ R₂ : Subgroup G} (hR : R₂ < R₁)
    (hN₂ : N ≤ Subgroup.normalizer (R₂ : Set G)) (hKN : K ≤ N)
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G)) :
    R₂ ≤ chiefCentralizer K R₁ R₂ hR₁₂ := by
  intro r hr
  rw [mem_chiefCentralizer]
  refine ⟨le_of_lt hR hr, fun k => ?_⟩
  have h1 : (k : G) * r⁻¹ * (k : G)⁻¹ ∈ R₂ :=
    (Subgroup.mem_normalizer_iff.mp (hN₂ (hKN k.2)) r⁻¹).mp (R₂.inv_mem hr)
  have h2 : r * ((k : G) * r⁻¹ * (k : G)⁻¹) ∈ R₂ := R₂.mul_mem hr h1
  simpa [commutatorElement_def, mul_assoc] using h2

private lemma chiefCentralizer_normal {N K R₁ R₂ : Subgroup G}
    (hN₁ : N ≤ Subgroup.normalizer (R₁ : Set G))
    (hN₂ : N ≤ Subgroup.normalizer (R₂ : Set G))
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hKN : K ≤ N)
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G)) :
    N ≤ Subgroup.normalizer (chiefCentralizer K R₁ R₂ hR₁₂ : Set G) := by
  intro n hn r
  have hstep : ∀ {m : G}, m ∈ N → ∀ {s : G},
      s ∈ chiefCentralizer K R₁ R₂ hR₁₂ →
      m * s * m⁻¹ ∈ chiefCentralizer K R₁ R₂ hR₁₂ := by
    intro m hm s hs
    rw [mem_chiefCentralizer] at hs ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hN₁ hm) s).mp hs.1, fun k => ?_⟩
    have hkK : m⁻¹ * (k : G) * m ∈ K := by
      have h := (Subgroup.mem_normalizer_iff.mp (hNK (N.inv_mem hm)) (k : G))
      simpa using h.mp k.2
    have hinner : ⁅s, m⁻¹ * (k : G) * m⁆ ∈ R₂ := hs.2 ⟨_, hkK⟩
    have hconj : m * ⁅s, m⁻¹ * (k : G) * m⁆ * m⁻¹ =
        ⁅m * s * m⁻¹, (k : G)⁆ := by
      simp only [commutatorElement_def]
      group
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hN₂ hm) _).mp hinner
  constructor
  · exact hstep hn
  · intro hr
    have h := hstep (N.inv_mem hn) hr
    simpa [mul_assoc] using h

theorem mem_of_commutator_mem_of_chief {N K R₁ R₂ : Subgroup G} (hKN : K ≤ N)
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hR : R₂ < R₁)
    (hN₁ : N ≤ Subgroup.normalizer (R₁ : Set G))
    (hN₂ : N ≤ Subgroup.normalizer (R₂ : Set G))
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G))
    (hchief : ∀ X : Subgroup G, R₂ ≤ X → X ≤ R₁ →
      N ≤ Subgroup.normalizer (X : Set G) → X = R₂ ∨ X = R₁)
    (hK : ∃ k ∈ K, ∃ r ∈ R₁, k * r * k⁻¹ * r⁻¹ ∉ R₂) {r : G} (hr : r ∈ R₁)
    (hrK : ∀ k ∈ K, k * r * k⁻¹ * r⁻¹ ∈ R₂) : r ∈ R₂ := by
  let A := chiefCentralizer K R₁ R₂ hR₁₂
  have hA_le : A ≤ R₁ := chiefCentralizer_le K R₁ R₂ hR₁₂
  have hR₂A : R₂ ≤ A := le_chiefCentralizer hR hN₂ hKN hR₁₂
  have hA_norm : N ≤ Subgroup.normalizer (A : Set G) :=
    chiefCentralizer_normal hN₁ hN₂ hNK hKN hR₁₂
  rcases hchief A hR₂A hA_le hA_norm with hA_bot | hA_top
  · have hrA : r ∈ A := by
      rw [mem_chiefCentralizer]
      refine ⟨hr, fun k => ?_⟩
      have hk : (k : G) * r * (k : G)⁻¹ * r⁻¹ ∈ R₂ := hrK (k : G) k.2
      have hk' : ⁅(k : G), r⁆ ∈ R₂ := by simpa [commutatorElement_def] using hk
      simpa [commutatorElement_inv] using R₂.inv_mem hk'
    rwa [hA_bot] at hrA
  · exfalso
    obtain ⟨k, hk, x, hx, hxnot⟩ := hK
    have hxA : x ∈ A := by
      rw [hA_top]
      exact hx
    have hcomm : ⁅x, (k : G)⁆ ∈ R₂ :=
      ((mem_chiefCentralizer hR₁₂).mp hxA).2 ⟨k, hk⟩
    have hkx : ⁅(k : G), x⁆ ∈ R₂ := by
      simpa [commutatorElement_inv] using R₂.inv_mem hcomm
    exact hxnot (by simpa [commutatorElement_def] using hkx)

variable [Finite G]

private lemma chiefCentralizer_ne_lower {N P R₁ R₂ : Subgroup G}
    (hP : IsPGroup 2 P) (hPN : P ≤ N)
    (hN₁ : N ≤ Subgroup.normalizer (R₁ : Set G))
    (hN₂ : N ≤ Subgroup.normalizer (R₂ : Set G))
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G)) (hR : R₂ < R₁)
    (hR₁ : IsPGroup 2 R₁) :
    chiefCentralizer P R₁ R₂ hR₁₂ ≠ R₂ := by
  intro hEq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := R₂.subgroupOf R₁
  haveI hHn : H.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hR₁₂
  letI : MulDistribMulAction P R₁ :=
    MulDistribMulAction.compHom R₁ (Subgroup.inclusion (hPN.trans hN₁))
  haveI hQA : MulAction.QuotientAction P H := by
    refine ⟨fun p a a' h => ?_⟩
    have hpN : (p : G) ∈ N := hPN p.2
    have hp₂ : (p : G) ∈ Subgroup.normalizer (R₂ : Set G) := hN₂ hpN
    rw [Subgroup.mem_subgroupOf] at h ⊢
    change (((p • a)⁻¹ * (p • a') : R₁) : G) ∈ R₂
    have hpa : ((p • a : R₁) : G) = (p : G) * (a : G) * (p : G)⁻¹ := rfl
    have hpa' : ((p • a' : R₁) : G) = (p : G) * (a' : G) * (p : G)⁻¹ := rfl
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hpa, hpa']
    have hcalc : ((p : G) * (a : G) * (p : G)⁻¹)⁻¹ *
        ((p : G) * (a' : G) * (p : G)⁻¹) =
        (p : G) * ((a : G)⁻¹ * (a' : G)) * (p : G)⁻¹ := by
      group
    rw [hcalc]
    exact (Subgroup.mem_normalizer_iff.mp hp₂ ((a : G)⁻¹ * (a' : G))).mp h
  let Q := R₁ ⧸ H
  haveI : Finite Q :=
    Finite.of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  have hQ : IsPGroup 2 Q := hR₁.to_quotient H
  have hHne : H ≠ ⊤ := by
    intro htop
    apply not_le_of_gt hR
    intro x hx
    have hxH : (⟨x, hx⟩ : R₁) ∈ H := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hxH
  haveI hQnt : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hHne
  obtain ⟨e, he⟩ := hQ.exists_card_eq
  have hcard_gt : 1 < Nat.card Q := Finite.one_lt_card_iff_nontrivial.mpr hQnt
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with he0 | hpos
    · rw [he, he0, pow_zero] at hcard_gt
      omega
    · exact hpos
  have hdvd : 2 ∣ Nat.card Q := by
    rw [he]
    exact dvd_pow_self 2 (Nat.ne_of_gt hepos)
  have hfix_id : (1 : Q) ∈ MulAction.fixedPoints P Q := by
    rw [MulAction.mem_fixedPoints]
    intro p
    change p • (QuotientGroup.mk (1 : R₁) : Q) = QuotientGroup.mk (1 : R₁)
    rw [MulAction.Quotient.smul_mk, smul_one]
  obtain ⟨b, hb, hbne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q hdvd hfix_id
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective b
  have hr_not : (r : G) ∉ R₂ := by
    intro hr₂
    have hrH : r ∈ H := hr₂
    exact hbne ((QuotientGroup.eq_one_iff r).mpr hrH).symm
  have hcomm : ∀ p : P,
      (p : G) * (r : G) * (p : G)⁻¹ * (r : G)⁻¹ ∈ R₂ := by
    intro p
    have hfp : p • (r : Q) = (r : Q) := (MulAction.mem_fixedPoints.mp hb) p
    have hm : ((p • r) / r : R₁) ∈ H := QuotientGroup.eq_iff_div_mem.mp hfp
    have hpsmul : ((p • r : R₁) : G) = (p : G) * (r : G) * (p : G)⁻¹ := rfl
    have hcoe : (((p • r) / r : R₁) : G) =
        (p : G) * (r : G) * (p : G)⁻¹ * (r : G)⁻¹ := by
      rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, hpsmul]
    have hm' : (((p • r) / r : R₁) : G) ∈ R₂ := Subgroup.mem_subgroupOf.mp hm
    rwa [← hcoe]
  have hmemA : (r : G) ∈ chiefCentralizer P R₁ R₂ hR₁₂ := by
    rw [mem_chiefCentralizer]
    refine ⟨r.2, fun p => ?_⟩
    have hp : ⁅(p : G), (r : G)⁆ ∈ R₂ := by
      simpa [commutatorElement_def] using hcomm p
    simpa [commutatorElement_inv] using R₂.inv_mem hp
  rw [hEq] at hmemA
  exact hr_not hmemA

theorem commutator_mem_of_chief {N P R₁ R₂ : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ N)
    (hNP : N ≤ Subgroup.normalizer (P : Set G)) (hR₁ : IsPGroup 2 R₁) (hR : R₂ < R₁)
    (hN₁ : N ≤ Subgroup.normalizer (R₁ : Set G))
    (hN₂ : N ≤ Subgroup.normalizer (R₂ : Set G))
    (hR₁₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G))
    (hchief : ∀ X : Subgroup G, R₂ ≤ X → X ≤ R₁ →
      N ≤ Subgroup.normalizer (X : Set G) → X = R₂ ∨ X = R₁) :
    ∀ p ∈ P, ∀ r ∈ R₁, p * r * p⁻¹ * r⁻¹ ∈ R₂ := by
  intro p hp r hr
  let A := chiefCentralizer P R₁ R₂ hR₁₂
  have hA_le : A ≤ R₁ := chiefCentralizer_le P R₁ R₂ hR₁₂
  have hR₂A : R₂ ≤ A := le_chiefCentralizer hR hN₂ hPN hR₁₂
  have hA_norm : N ≤ Subgroup.normalizer (A : Set G) :=
    chiefCentralizer_normal hN₁ hN₂ hNP hPN hR₁₂
  have hA_ne : A ≠ R₂ := chiefCentralizer_ne_lower hP hPN hN₁ hN₂ hR₁₂ hR hR₁
  rcases hchief A hR₂A hA_le hA_norm with hA_bot | hA_top
  · exact absurd hA_bot hA_ne
  · have hrA : r ∈ A := by
      rw [hA_top]
      exact hr
    have h := ((mem_chiefCentralizer hR₁₂).mp hrA).2 ⟨p, hp⟩
    have hpR : ⁅(p : G), r⁆ ∈ R₂ := by
      simpa [commutatorElement_inv] using R₂.inv_mem h
    simpa [commutatorElement_def] using hpR

private lemma exists_maximal_invariant_lt {N X : Subgroup G} (hX : X ≠ ⊥) :
    ∃ X₂ : Subgroup G, X₂ < X ∧ N ≤ Subgroup.normalizer (X₂ : Set G) ∧
      ∀ Y : Subgroup G, X₂ ≤ Y → Y < X → N ≤ Subgroup.normalizer (Y : Set G) →
        Y = X₂ := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hbot_lt : ⊥ < X := bot_lt_iff_ne_bot.mpr hX
  have hbotN : N ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨X₂, -, hmax⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup G => Y < X ∧ N ≤ Subgroup.normalizer (Y : Set G))
    ⟨hbot_lt, hbotN⟩
  refine ⟨X₂, hmax.prop.1, hmax.prop.2, fun Y hX₂Y hYX hNY => ?_⟩
  exact (hmax.eq_of_le ⟨hYX, hNY⟩ hX₂Y).symm

private lemma centralizes_step {R X X₂ : Subgroup G} {j : G} (hj : Odd (orderOf j))
    (hR : IsPGroup 2 R) (hX₂X : X₂ < X) (hXR : X ≤ R)
    (hX₂Xnorm : X ≤ Subgroup.normalizer (X₂ : Set G))
    (htriv : ∀ y ∈ X, j * y * j⁻¹ * y⁻¹ ∈ X₂)
    (hih : ∀ y ∈ X₂, j * y * j⁻¹ = y) :
    ∀ x ∈ X, j * x * j⁻¹ = x := by
  intro x hx
  set z : G := x⁻¹ * j * x * j⁻¹ with hzdef
  have hzX₂ : z ∈ X₂ := by
    have hc : j * x * j⁻¹ * x⁻¹ ∈ X₂ := htriv x hx
    have hconj : x⁻¹ * (j * x * j⁻¹ * x⁻¹) * x = z := by
      rw [hzdef]
      group
    rw [← hconj]
    exact (Subgroup.mem_normalizer_iff''.mp (hX₂Xnorm hx) _).mp hc
  have hzj : j * z * j⁻¹ = z := hih z hzX₂
  have hcomm : Commute j z := by
    show j * z = z * j
    calc j * z = (j * z * j⁻¹) * j := by group
      _ = z * j := by rw [hzj]
  have hjx : j * x * j⁻¹ = x * z := by
    rw [hzdef]
    group
  have hpow : ∀ m : ℕ, j ^ m * x * (j ^ m)⁻¹ = x * z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      have hzm : j * z ^ m * j⁻¹ = z ^ m := by
        rw [(hcomm.pow_right m).eq, mul_inv_cancel_right]
      calc j ^ (m + 1) * x * (j ^ (m + 1))⁻¹
          = j * (j ^ m * x * (j ^ m)⁻¹) * j⁻¹ := by
            rw [pow_succ]
            group
        _ = j * (x * z ^ m) * j⁻¹ := by rw [ihm]
        _ = (j * x * j⁻¹) * (j * z ^ m * j⁻¹) := by group
        _ = (x * z) * z ^ m := by rw [hjx, hzm]
        _ = x * z ^ (m + 1) := by
            rw [pow_succ]
            group
  have hzk : z ^ orderOf j = 1 := by
    have h := hpow (orderOf j)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    have h' := congrArg (fun t => x⁻¹ * t) h
    simpa [mul_assoc] using h'.symm
  have hzR : z ∈ R := hX₂X.le.trans hXR hzX₂
  obtain ⟨e, he⟩ := hR.exists_orderOf_dvd_pow ⟨z, hzR⟩
  rw [Subgroup.orderOf_mk] at he
  have hcop : Nat.Coprime (2 ^ e) (orderOf j) :=
    (hj.coprime_two_right.symm).pow_left e
  have hzkdvd : orderOf z ∣ orderOf j := orderOf_dvd_of_pow_eq_one hzk
  have hone : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop he hzkdvd
  have hz1 : z = 1 := orderOf_eq_one_iff.mp hone
  have hxj : j * x = x * j := by
    calc j * x = x * z * j := by
          rw [hzdef]
          group
      _ = x * 1 * j := by rw [hz1]
      _ = x * j := by group
  calc j * x * j⁻¹ = x * j * j⁻¹ := by rw [hxj]
    _ = x := by group

private lemma centralizes_of_forall_chief_trivial {N R : Subgroup G} {j : G}
    (hR : IsPGroup 2 R) (hRN : R ≤ N) (hj : Odd (orderOf j))
    (hno : ∀ R₁ R₂ : Subgroup G, R₂ < R₁ → R₁ ≤ R →
      N ≤ Subgroup.normalizer (R₁ : Set G) → N ≤ Subgroup.normalizer (R₂ : Set G) →
      R₁ ≤ Subgroup.normalizer (R₂ : Set G) →
      (∀ X : Subgroup G, R₂ ≤ X → X ≤ R₁ → N ≤ Subgroup.normalizer (X : Set G) →
        X = R₂ ∨ X = R₁) →
      ∀ r ∈ R₁, j * r * j⁻¹ * r⁻¹ ∈ R₂) :
    ∀ X : Subgroup G, X ≤ R → N ≤ Subgroup.normalizer (X : Set G) →
      ∀ x ∈ X, j * x * j⁻¹ = x := by
  let P : ℕ → Prop := fun n => ∀ X : Subgroup G, Nat.card X = n → X ≤ R →
    N ≤ Subgroup.normalizer (X : Set G) → ∀ x ∈ X, j * x * j⁻¹ = x
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X hXcard hXR hNX x hx
      by_cases hXbot : X = ⊥
      · subst X
        rw [Subgroup.mem_bot.mp hx]
        simp
      · obtain ⟨X₂, hX₂X, hNX₂, hmax⟩ := exists_maximal_invariant_lt (N := N) hXbot
        have hX₂Xnorm : X ≤ Subgroup.normalizer (X₂ : Set G) :=
          hXR.trans (hRN.trans hNX₂)
        have hih : ∀ y ∈ X₂, j * y * j⁻¹ = y :=
          ih (Nat.card X₂) (hXcard ▸ Subgroup.card_lt_of_lt hX₂X) X₂ rfl
            (hX₂X.le.trans hXR) hNX₂
        have hchief : ∀ Y : Subgroup G, X₂ ≤ Y → Y ≤ X →
            N ≤ Subgroup.normalizer (Y : Set G) → Y = X₂ ∨ Y = X := by
          intro Y hX₂Y hYX hNY
          by_cases hYX' : Y = X
          · exact Or.inr hYX'
          · exact Or.inl (hmax Y hX₂Y (lt_of_le_of_ne hYX hYX') hNY)
        have htriv : ∀ y ∈ X, j * y * j⁻¹ * y⁻¹ ∈ X₂ := by
          intro y hy
          exact hno X X₂ hX₂X hXR hNX hNX₂ hX₂Xnorm hchief y hy
        exact centralizes_step hj hR hX₂X hXR hX₂Xnorm htriv hih x hx
  exact fun X hXR hNX x hx => hP (Nat.card X) X rfl hXR hNX x hx

theorem exists_chief_factor_of_odd {N R : Subgroup G} (hR : IsPGroup 2 R) (hRN : R ≤ N)
    (hNR : N ≤ Subgroup.normalizer (R : Set G)) {j : G} (hjN : j ∈ N) (hj : Odd (orderOf j))
    (hjR : ∃ r ∈ R, j * r * j⁻¹ * r⁻¹ ≠ 1) :
    ∃ R₁ R₂ : Subgroup G, R₂ < R₁ ∧ R₁ ≤ R ∧ N ≤ Subgroup.normalizer (R₁ : Set G) ∧
      N ≤ Subgroup.normalizer (R₂ : Set G) ∧ R₁ ≤ Subgroup.normalizer (R₂ : Set G) ∧
      (∀ X : Subgroup G, R₂ ≤ X → X ≤ R₁ → N ≤ Subgroup.normalizer (X : Set G) →
        X = R₂ ∨ X = R₁) ∧
      ∃ r ∈ R₁, j * r * j⁻¹ * r⁻¹ ∉ R₂ := by
  by_contra hcon
  have hno : ∀ R₁ R₂ : Subgroup G, R₂ < R₁ → R₁ ≤ R →
      N ≤ Subgroup.normalizer (R₁ : Set G) → N ≤ Subgroup.normalizer (R₂ : Set G) →
      R₁ ≤ Subgroup.normalizer (R₂ : Set G) →
      (∀ X : Subgroup G, R₂ ≤ X → X ≤ R₁ → N ≤ Subgroup.normalizer (X : Set G) →
        X = R₂ ∨ X = R₁) →
      ∀ r ∈ R₁, j * r * j⁻¹ * r⁻¹ ∈ R₂ := by
    intro R₁ R₂ hlt hR₁R hN₁ hN₂ hR₁₂ hchief r hr
    by_contra hcomm
    exact hcon ⟨R₁, R₂, hlt, hR₁R, hN₁, hN₂, hR₁₂, hchief, r, hr, hcomm⟩
  have hcentral := centralizes_of_forall_chief_trivial hR hRN hj hno
  obtain ⟨r, hrR, hrne⟩ := hjR
  have hcent := hcentral R le_rfl hNR r hrR
  exact hrne (by simpa [hcent])

end CFSG.GroupTheory
