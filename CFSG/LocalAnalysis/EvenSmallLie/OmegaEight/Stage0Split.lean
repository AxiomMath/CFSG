module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Shape

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SplitC
open CFSG.EvenSmallLie.OmegaEight.CPrime

variable {G : Type} [Group G] {t : G} {L : Subgroup G}

namespace StepK

variable (hK : StepK t L)
include hK

theorem relIndex_dvd_card_outer :
    (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ Nat.card (Outer L) := by
  obtain ⟨θ, hθ, -, hinn⟩ := exists_automizer hK.le_centralizer hK.le_normalizer hK.inf_eq
  have hcomap : (L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G)) = (inner L).comap θ := by
    ext h
    rw [mem_subgroupOf, mem_comap, ← hinn h]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, hm.symm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, hm.symm⟩
  have hle : inner L ≤ θ.range := by
    rintro _ ⟨m, rfl⟩
    exact ⟨⟨m, hK.le_centralizer m.2⟩, MulEquiv.ext fun l => Subtype.ext (by rw [hθ]; rfl)⟩
  change ((L ⊔ zpowers t).subgroupOf _).index ∣ Nat.card (MulAut L ⧸ inner L)
  rw [hcomap, index_comap, ← index_eq_card]
  exact relIndex_dvd_index_of_le hle

theorem exists_mul_sq (hlift : InvolutionLifting L) {h : G}
    (hh : h ∈ centralizer ({t} : Set G)) (hN : h ∉ L ⊔ zpowers t) (h2 : h * h ∈ L ⊔ zpowers t) :
    ∃ m ∈ L, h * m * (h * m) = 1 ∨ h * m * (h * m) = t := by
  obtain ⟨θ, hθ, hker, hinn⟩ := exists_automizer hK.le_centralizer hK.le_normalizer hK.inf_eq
  have hθL : ∀ m : L, θ ⟨m, hK.le_centralizer m.2⟩ = MulAut.conj m := fun m =>
    MulEquiv.ext fun l => Subtype.ext (by rw [hθ]; rfl)
  set hC : centralizer ({t} : Set G) := ⟨h, hh⟩ with hCdef
  have h1 : θ hC ∉ inner L := fun ⟨m, hm⟩ => hN ((hinn hC).1 ⟨m, hm.symm⟩)
  have h2' : θ hC * θ hC ∈ inner L := by
    rw [← map_mul]
    obtain ⟨m, hm⟩ := (hinn (hC * hC)).2 h2
    exact ⟨m, hm.symm⟩
  obtain ⟨β, hβ, m, hm⟩ := hlift _ h1 h2'
  refine ⟨m, m.2, ?_⟩
  have hb : θ (hC * ⟨m, hK.le_centralizer m.2⟩) = β := by
    rw [map_mul, hθL m, hm, mul_inv_cancel_left]
  have hb2 : θ (hC * ⟨m, hK.le_centralizer m.2⟩ * (hC * ⟨m, hK.le_centralizer m.2⟩)) = 1 := by
    rw [map_mul, hb, hβ]
  exact hK.mem_zpowers_iff.1 ((hker _).1 hb2)

theorem shapeA_of_relIndex_eq_one
    (h1 : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 1) : ShapeA t L :=
  ⟨hK.orderOf_eq, hK.not_mem, hK.le_centralizer,
    le_antisymm (relIndex_eq_one.1 h1) hK.sup_le_centralizer⟩

theorem exists_shapeB [Finite G]
    (h3 : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 3) : ∃ r, ShapeB t L r := by
  have hn : ∀ m ∈ centralizer ({t} : Set G), ∀ y ∈ L ⊔ zpowers t,
      m * y * m⁻¹ ∈ L ⊔ zpowers t := fun m hm y hy => hK.conj_mem_sup hm hy
  obtain ⟨h, hh, hhN, -⟩ := exists_not_mem_pow_mem hn Nat.prime_three (h3 ▸ dvd_rfl)
  have hpow : ∀ x ∈ centralizer ({t} : Set G), x ^ 3 ∈ L ⊔ zpowers t := fun x hx =>
    h3 ▸ pow_relIndex_mem_of_le hn hx
  obtain ⟨m, k, hm3, hord⟩ := exists_pow_coprime_orderOf_eq (orderOf_pos h).ne' Nat.prime_three
  have hrH : h ^ m ∈ centralizer ({t} : Set G) := pow_mem hh m
  have hrN : h ^ m ∉ L ⊔ zpowers t := fun hr => hhN (mem_of_pow_mem_of_coprime (hpow h hh) hr hm3)
  have hodd : Odd (orderOf (h ^ m)) := by
    rw [hord]
    exact Odd.pow (by decide)
  have hsup : L ⊔ zpowers t ⊔ zpowers (h ^ m) = centralizer ({t} : Set G) :=
    eq_of_relIndex_prime le_sup_left (sup_le hK.sup_le_centralizer (zpowers_le.2 hrH))
      (h3 ▸ Nat.prime_three) (mem_sup_right (mem_zpowers _)) hrN
  refine ⟨h ^ m, ⟨hK.orderOf_eq, sup_le hK.le_centralizer (zpowers_le.2 hrH),
    hK.not_mem_sup_of_odd (hK.le_normalizer hrH) hodd, ?_, le_sup_left⟩, hrH, hrN,
    hpow _ hrH, ⟨k, hord⟩, h3⟩
  rw [← hsup]
  exact sup_right_comm _ _ _

theorem not_mem_sup_of_sq {b : G} (hbL : b ∈ normalizer (L : Set G)) (hb : b * b = 1)
    (hbN : b ∉ L ⊔ zpowers t) : t ∉ L ⊔ zpowers b := by
  have hb1 : b ≠ 1 := fun h => hbN (h ▸ one_mem _)
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb) hb1
  intro ht
  obtain ⟨l, hl, n, hln⟩ := (mem_sup_zpowers_iff hbL).1 ht
  by_cases hn : b ^ n = 1
  · rw [hn, mul_one] at hln
    exact hK.not_mem (hln ▸ hl)
  · rw [eq_of_mem_zpowers_of_orderOf_eq_two hbo (zpow_mem (mem_zpowers b) n) hn] at hln
    apply hbN
    have : b = l⁻¹ * t := by rw [hln]; group
    rw [this]
    exact mul_mem (mem_sup_left (inv_mem hl)) (mem_sup_right (mem_zpowers t))

theorem shapeC_or_shapeC' [Finite G] (hlift : InvolutionLifting L)
    (h2 : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2) :
    (∃ b, ShapeC t L b) ∨ ∃ c, ShapeC' t L c := by
  have hn : ∀ m ∈ centralizer ({t} : Set G), ∀ y ∈ L ⊔ zpowers t,
      m * y * m⁻¹ ∈ L ⊔ zpowers t := fun m hm y hy => hK.conj_mem_sup hm hy
  obtain ⟨h, hh, hhN, -⟩ := exists_not_mem_pow_mem hn Nat.prime_two (h2 ▸ dvd_rfl)
  obtain ⟨m, hm, hb⟩ := hK.exists_mul_sq hlift hh hhN (mul_self_mem_of_relIndex_eq_two h2 hh)
  have hbH : h * m ∈ centralizer ({t} : Set G) := mul_mem hh (hK.le_centralizer hm)
  have hbN : h * m ∉ L ⊔ zpowers t := fun hb' => hhN (by
    simpa using mul_mem hb' (inv_mem (mem_sup_left hm : m ∈ L ⊔ zpowers t)))
  have hbL : h * m ∈ normalizer (L : Set G) := hK.le_normalizer hbH
  have hsup : L ⊔ zpowers t ⊔ zpowers (h * m) = centralizer ({t} : Set G) :=
    eq_of_relIndex_prime le_sup_left (sup_le hK.sup_le_centralizer (zpowers_le.2 hbH))
      (h2 ▸ Nat.prime_two) (mem_sup_right (mem_zpowers _)) hbN
  rcases hb with hb1 | hbt
  · refine Or.inl ⟨h * m, ⟨hK.orderOf_eq, sup_le hK.le_centralizer (zpowers_le.2 hbH),
      hK.not_mem_sup_of_sq hbL hb1 hbN, ?_, le_sup_left⟩, hbH, hb1, hbN, h2⟩
    rw [← hsup]
    exact sup_right_comm _ _ _
  · refine Or.inr ⟨h * m, ⟨hK.orderOf_eq, hbt, hK.not_mem, hK.le_centralizer, ?_, ?_⟩, hbL,
      ?_, hbN, h2⟩
    · intro x hx hx1
      by_contra hxN
      have hy : x * (h * m)⁻¹ ∈ L ⊔ zpowers t :=
        mul_mem_of_not_mem_of_relIndex_eq_two h2 hx (inv_mem hbH) hxN (fun h' => hbN (by
          simpa using inv_mem h'))
      have hl := hK.mul_conj_mem hbH hy
      have e : x * x = x * (h * m)⁻¹ * (h * m * (x * (h * m)⁻¹) * (h * m)⁻¹) *
          (h * m * (h * m)) := by group
      rw [hbt, hx1] at e
      apply hK.not_mem
      rw [eq_inv_of_mul_eq_one_right e.symm]
      exact inv_mem hl
    · intro htc
      have hle : closure {g : G | g * t = t * g ∧ Odd (orderOf g)} ≤ L := by
        rw [closure_le]
        rintro g ⟨hg, ho⟩
        exact mem_of_odd_of_relIndex_eq_two hK.relIndex_L
          (mem_of_odd_of_relIndex_eq_two h2 (mem_centralizer_singleton_iff.2 hg) ho) ho
      exact hK.not_mem (hle htc)
    · refine le_antisymm ?_ (sup_le hK.le_centralizer (zpowers_le.2 hbH))
      rw [← hsup]
      refine sup_le (sup_le le_sup_left ?_) le_sup_right
      rw [zpowers_le, ← hbt]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem shapeD_or_shapeD' [Finite G] (hlift : InvolutionLifting L)
    (h6 : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 6) :
    (∃ b r, ShapeD t L b r) ∨ ∃ c r, ShapeD' t L c r := by
  have hn : ∀ m ∈ centralizer ({t} : Set G), ∀ y ∈ L ⊔ zpowers t,
      m * y * m⁻¹ ∈ L ⊔ zpowers t := fun m hm y hy => hK.conj_mem_sup hm hy
  obtain ⟨h₃, hh₃, hh₃N, hh₃3⟩ := exists_not_mem_pow_mem hn Nat.prime_three
    (h6 ▸ (by norm_num : 3 ∣ 6))
  obtain ⟨m, k, hm3, hord⟩ := exists_pow_coprime_orderOf_eq (orderOf_pos h₃).ne' Nat.prime_three
  have hrH : h₃ ^ m ∈ centralizer ({t} : Set G) := pow_mem hh₃ m
  have hrN : h₃ ^ m ∉ L ⊔ zpowers t := fun hr => hh₃N (mem_of_pow_mem_of_coprime hh₃3 hr hm3)
  have hr3 : (h₃ ^ m) ^ 3 ∈ L ⊔ zpowers t := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_mem hh₃3 m
  have hodd : Odd (orderOf (h₃ ^ m)) := by
    rw [hord]
    exact Odd.pow (by decide)
  have hrL : h₃ ^ m ∈ normalizer (L : Set G) := hK.le_normalizer hrH
  obtain ⟨h₂, hh₂, hh₂N, hh₂2⟩ := exists_not_mem_pow_mem hn Nat.prime_two
    (h6 ▸ (by norm_num : 2 ∣ 6))
  rw [sq] at hh₂2
  obtain ⟨m₂, hm₂, hb⟩ := hK.exists_mul_sq hlift hh₂ hh₂N hh₂2
  have hbH : h₂ * m₂ ∈ centralizer ({t} : Set G) := mul_mem hh₂ (hK.le_centralizer hm₂)
  have hbN : h₂ * m₂ ∉ L ⊔ zpowers t := fun hb' => hh₂N (by
    simpa using mul_mem hb' (inv_mem (mem_sup_left hm₂ : m₂ ∈ L ⊔ zpowers t)))
  have hbsq : h₂ * m₂ * (h₂ * m₂) ∈ L ⊔ zpowers t := by
    rcases hb with h | h <;> rw [h]
    · exact one_mem _
    · exact mem_sup_right (mem_zpowers t)
  have hK'H : L ⊔ zpowers t ⊔ zpowers (h₃ ^ m) ≤ centralizer ({t} : Set G) :=
    sup_le hK.sup_le_centralizer (zpowers_le.2 hrH)
  have hrNN : h₃ ^ m ∈ normalizer ((L ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_iff.2 fun y => ⟨fun hy => hn _ hrH y hy, fun hy => by
      simpa [mul_assoc] using hn _ (inv_mem hrH) _ hy⟩
  have hbK' : h₂ * m₂ ∉ L ⊔ zpowers t ⊔ zpowers (h₃ ^ m) := by
    intro hbK
    obtain ⟨y, hy, n, hyn⟩ := (mem_sup_zpowers_iff hrNN).1 hbK
    have hc : (h₃ ^ m) ^ n * y * ((h₃ ^ m) ^ n)⁻¹ ∈ L ⊔ zpowers t :=
      hn _ (zpow_mem hrH n) y hy
    have e : (h₃ ^ m) ^ n * (h₃ ^ m) ^ n =
        ((h₃ ^ m) ^ n * y * ((h₃ ^ m) ^ n)⁻¹)⁻¹ * y⁻¹ * (h₂ * m₂ * (h₂ * m₂)) := by
      rw [hyn]; group
    have h2n : ((h₃ ^ m) ^ n) ^ 2 ∈ L ⊔ zpowers t := by
      rw [sq, e]
      exact mul_mem (mul_mem (inv_mem hc) (inv_mem hy)) hbsq
    have h3n : ((h₃ ^ m) ^ n) ^ 3 ∈ L ⊔ zpowers t := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact zpow_mem hr3 n
    apply hbN
    rw [hyn]
    exact mul_mem hy (mem_of_pow_mem_of_coprime h2n h3n (by norm_num))
  have hd := relIndex_mul_relIndex (L ⊔ zpowers t) _ _ le_sup_left hK'H
  rw [h6] at hd
  have hd1 : (L ⊔ zpowers t).relIndex (L ⊔ zpowers t ⊔ zpowers (h₃ ^ m)) ≠ 1 := fun h1 =>
    hrN (relIndex_eq_one.1 h1 (mem_sup_right (mem_zpowers _)))
  have hd2 : (L ⊔ zpowers t).relIndex (L ⊔ zpowers t ⊔ zpowers (h₃ ^ m)) ≠ 2 := by
    intro h2
    have hsq : (h₃ ^ m) ^ 2 ∈ L ⊔ zpowers t := by
      rw [sq]
      exact mul_self_mem_of_relIndex_eq_two h2 (mem_sup_right (mem_zpowers _))
    exact hrN (mem_of_pow_mem_of_coprime hsq hr3 (by norm_num))
  have he1 : (L ⊔ zpowers t ⊔ zpowers (h₃ ^ m)).relIndex (centralizer ({t} : Set G)) ≠ 1 :=
    fun h1 => hbK' (relIndex_eq_one.1 h1 hbH)
  have hK'2 : (L ⊔ zpowers t ⊔ zpowers (h₃ ^ m)).relIndex (centralizer ({t} : Set G)) = 2 := by
    have hdv : (L ⊔ zpowers t).relIndex (L ⊔ zpowers t ⊔ zpowers (h₃ ^ m)) ≤ 6 :=
      Nat.le_of_dvd (by norm_num) ⟨_, hd.symm⟩
    interval_cases hx : (L ⊔ zpowers t).relIndex (L ⊔ zpowers t ⊔ zpowers (h₃ ^ m)) <;> omega
  have hsup : L ⊔ zpowers t ⊔ zpowers (h₃ ^ m) ⊔ zpowers (h₂ * m₂) =
      centralizer ({t} : Set G) :=
    eq_of_relIndex_prime le_sup_left (sup_le hK'H (zpowers_le.2 hbH)) (hK'2 ▸ Nat.prime_two)
      (mem_sup_right (mem_zpowers _)) hbK'
  set r := h₃ ^ m with hrdef
  set b := h₂ * m₂ with hbdef
  have htK : t ∉ L ⊔ zpowers r := hK.not_mem_sup_of_odd hrL hodd
  have hKH : L ⊔ zpowers r ≤ centralizer ({t} : Set G) :=
    sup_le hK.le_centralizer (zpowers_le.2 hrH)
  have hK'eq : L ⊔ zpowers t ⊔ zpowers r = L ⊔ zpowers r ⊔ zpowers t := sup_right_comm _ _ _
  have hcommK : ∀ x ∈ L ⊔ zpowers r, ∀ z ∈ zpowers t, x * z = z * x := by
    intro x hx z hz
    rcases hK.mem_zpowers_iff.1 hz with rfl | rfl
    · rw [mul_one, one_mul]
    · exact mem_centralizer_singleton_iff.1 (hKH hx)
  have hKK' : (L ⊔ zpowers r).relIndex (L ⊔ zpowers t ⊔ zpowers r) = 2 := by
    rw [hK'eq, relIndex_eq_two_iff]
    refine ⟨t, mem_sup_right (mem_zpowers t), fun x hx => ?_⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommK hx
    rcases hK.mem_zpowers_iff.1 hz with rfl | rfl
    · rw [mul_one]
      exact Or.inr ⟨hu, fun h => htK (by simpa using mul_mem (inv_mem hu) h)⟩
    · rw [mul_assoc, hK.mul_self, mul_one]
      exact Or.inl ⟨hu, fun h => htK (by simpa using mul_mem (inv_mem hu) h)⟩
  have hS1 : ∀ h ∈ centralizer ({t} : Set G), ∀ x ∈ L ⊔ zpowers r,
      h * x * h⁻¹ ∈ L ⊔ zpowers r := by
    intro h hh x hx
    have hle : L ⊔ zpowers r ≤ (L ⊔ zpowers r).comap (MulAut.conj h).toMonoidHom := by
      refine sup_le (fun l hl => ?_) (zpowers_le.2 ?_)
      · exact mem_sup_left ((mem_normalizer_iff.1 (hK.le_normalizer hh) l).1 hl)
      · have h1 : h * r * h⁻¹ ∈ L ⊔ zpowers t ⊔ zpowers r :=
          conj_mem_of_relIndex_eq_two hK'2 hK'H hh (mem_sup_right (mem_zpowers r))
        have h2 : Odd (orderOf (h * r * h⁻¹)) := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
          exact hodd
        exact mem_of_odd_of_relIndex_eq_two hKK' h1 h2
    exact hle hx
  have hbNK : b ∈ normalizer ((L ⊔ zpowers r : Subgroup G) : Set G) :=
    mem_normalizer_iff.2 fun y => ⟨fun hy => hS1 _ hbH y hy, fun hy => by
      simpa [mul_assoc] using hS1 _ (inv_mem hbH) _ hy⟩
  rcases hb with hb1 | hbt
  ·
    refine Or.inl ⟨b, r, ⟨hK.orderOf_eq, sup_le hKH (zpowers_le.2 hbH), ?_, ?_,
      le_sup_left.trans le_sup_left⟩, hbH, hb1, hbN, hrH, hrN, hr3, ⟨k, hord⟩, hS1, hK'2, h6⟩
    · have hb1' : b ≠ 1 := fun h => hbN (h ▸ one_mem _)
      have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb1) hb1'
      intro ht
      obtain ⟨x, hx, n, hxn⟩ := (mem_sup_zpowers_iff hbNK).1 ht
      by_cases hn1 : b ^ n = 1
      · rw [hn1, mul_one] at hxn
        exact htK (hxn ▸ hx)
      · rw [eq_of_mem_zpowers_of_orderOf_eq_two hbo (zpow_mem (mem_zpowers b) n) hn1] at hxn
        apply hbK'
        have : b = x⁻¹ * t := by rw [hxn]; group
        rw [this, hK'eq]
        exact mul_mem (mem_sup_left (inv_mem hx)) (mem_sup_right (mem_zpowers t))
    · rw [← hsup, hK'eq]
      exact sup_right_comm _ _ _
  ·
    have : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).Normal :=
      ⟨fun y hy g => hn g g.2 y hy⟩
    have hcard : Nat.card (centralizer ({t} : Set G) ⧸
        (L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))) = 2 * 3 := by
      rw [← index_eq_card]
      exact h6
    refine Or.inr ⟨b, r, ⟨hK.orderOf_eq, hbt, hK.not_mem, hK.le_centralizer, ?_, ?_⟩, hbN,
      hrH, hrN, hr3, ⟨k, hord⟩, hKH, htK, hbNK, ?_, ?_,
      sup_le Subgroup.le_normalizer (zpowers_le.2 hrL), hK'2, h6⟩
    · intro x hx hx1
      by_contra hxN
      obtain ⟨γ, hγ⟩ := exists_conj_mem_of_card_quotient hcard (by decide : Odd 3)
        (β := (⟨b, hbH⟩ : centralizer ({t} : Set G)))
        (show b * b ∈ L ⊔ zpowers t by rw [hbt]; exact mem_sup_right (mem_zpowers t)) hbN
        (α := (⟨x, hx⟩ : centralizer ({t} : Set G))) hxN
        (show x * x ∈ L ⊔ zpowers t by rw [hx1]; exact one_mem _)
      have hy : x⁻¹ * ((γ : G) * b * (γ : G)⁻¹) ∈ L ⊔ zpowers t := hγ
      have hl := hK.mul_conj_mem (inv_mem hx) (hn x hx _ hy)
      have hγt : (γ : G) * t * (γ : G)⁻¹ = t := by
        rw [mem_centralizer_singleton_iff.1 γ.2, mul_inv_cancel_right]
      have e : x * (x⁻¹ * ((γ : G) * b * (γ : G)⁻¹)) * x⁻¹ *
          (x⁻¹ * (x * (x⁻¹ * ((γ : G) * b * (γ : G)⁻¹)) * x⁻¹) * x⁻¹⁻¹) =
          (γ : G) * b * (γ : G)⁻¹ * (x * x)⁻¹ * ((γ : G) * b * (γ : G)⁻¹) := by group
      rw [hx1, inv_one, mul_one, show (γ : G) * b * (γ : G)⁻¹ * ((γ : G) * b * (γ : G)⁻¹) =
        (γ : G) * (b * b) * (γ : G)⁻¹ by group, hbt, hγt] at e
      exact hK.not_mem (e ▸ hl)
    · intro htc
      have hle : closure {g : G | g * t = t * g ∧ Odd (orderOf g)} ≤ L ⊔ zpowers r := by
        rw [closure_le]
        rintro g ⟨hg, ho⟩
        exact mem_of_odd_of_relIndex_eq_two hKK'
          (mem_of_odd_of_relIndex_eq_two hK'2 (mem_centralizer_singleton_iff.2 hg) ho) ho
      exact htK (hle htc)
    · refine le_antisymm ?_ (sup_le hKH (zpowers_le.2 hbH))
      rw [← hsup, hK'eq]
      refine sup_le (sup_le le_sup_left ?_) le_sup_right
      rw [zpowers_le, ← hbt]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
    · intro x hx hxx
      obtain ⟨l, hl, n, rfl⟩ := (mem_sup_zpowers_iff hrL).1 hx
      have hc : r ^ n * l * (r ^ n)⁻¹ ∈ L := (mem_normalizer_iff.1 (zpow_mem hrL n) l).1 hl
      have e : r ^ n * r ^ n =
          (l * (r ^ n * l * (r ^ n)⁻¹))⁻¹ * (l * r ^ n * (l * r ^ n)) := by group
      have h2 : (r ^ n) ^ 2 ∈ L := by
        rw [sq, e]
        exact mul_mem (inv_mem (mul_mem hl hc)) hxx
      have hro : (r ^ n) ^ orderOf r ∈ L := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
          one_zpow]
        exact one_mem _
      exact mul_mem hl (mem_of_pow_mem_of_coprime h2 hro (Nat.coprime_two_left.2 hodd))

theorem exists_shape [Finite G] (hlift : InvolutionLifting L)
    (hdvd : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 6) :
    ShapeA t L ∨ (∃ r, ShapeB t L r) ∨ (∃ b, ShapeC t L b) ∨ (∃ b r, ShapeD t L b r) ∨
      (∃ c, ShapeC' t L c) ∨ ∃ c r, ShapeD' t L c r := by
  have hmem := Nat.mem_divisors.2 ⟨hdvd, (by norm_num : (6 : ℕ) ≠ 0)⟩
  have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (hK.shapeA_of_relIndex_eq_one h)
  · rcases hK.shapeC_or_shapeC' hlift h with hc | hc
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))
  · exact Or.inr (Or.inl (hK.exists_shapeB h))
  · rcases hK.shapeD_or_shapeD' hlift h with hd | hd
    · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))

theorem exists_shape_of_dvd_two [Finite G] (hlift : InvolutionLifting L)
    (hdvd : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2) :
    ShapeA t L ∨ (∃ b, ShapeC t L b) ∨ ∃ c, ShapeC' t L c := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact Or.inl (hK.shapeA_of_relIndex_eq_one h)
  · exact Or.inr (hK.shapeC_or_shapeC' hlift h)

end StepK

end CFSG.EvenSmallLie.OmegaEight.Stage0
