module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Setting

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open

section Words

variable {G : Type*} [Group G]

theorem wordEval_nil (g y : G) : wordEval g y [] = 1 := by
  simp [wordEval]

theorem wordEval_cons (g y : G) (ℓ : Letter) (w : List Letter) :
    wordEval g y (ℓ :: w) = ℓ.eval g y * wordEval g y w := by
  simp [wordEval]

theorem conj_wordEval (n g y : G) (w : List Letter) :
    n * wordEval g y w * n⁻¹ = wordEval (n * g * n⁻¹) (n * y * n⁻¹) w := by
  induction w with
  | nil => simp [wordEval_nil]
  | cons ℓ w ih =>
    rw [wordEval_cons, wordEval_cons, ← ih]
    have : n * ℓ.eval g y * n⁻¹ = ℓ.eval (n * g * n⁻¹) (n * y * n⁻¹) := by
      cases ℓ <;> simp [Letter.eval, mul_assoc]
    rw [← this]
    group

theorem wordEval_mem {L : Subgroup G} {g y : G} (hg : g ∈ L) (hy : y ∈ L) (w : List Letter) :
    wordEval g y w ∈ L := by
  induction w with
  | nil => rw [wordEval_nil]; exact one_mem _
  | cons ℓ w ih =>
    rw [wordEval_cons]
    refine mul_mem ?_ ih
    cases ℓ
    · exact hg
    · exact inv_mem hg
    · exact hy

theorem commute_wordEval {s g y : G} (hg : Commute s g) (hy : Commute s y) (w : List Letter) :
    Commute s (wordEval g y w) := by
  induction w with
  | nil => rw [wordEval_nil]; exact Commute.one_right s
  | cons ℓ w ih =>
    rw [wordEval_cons]
    refine Commute.mul_right ?_ ih
    cases ℓ
    · exact hg
    · exact hg.inv_right
    · exact hy

theorem wordEval_mul_of_commute {s g y : G} (hg : Commute s g) (hy : Commute s y)
    (w : List Letter) : wordEval g (y * s) w = wordEval g y w * s ^ yCount w := by
  induction w with
  | nil => simp [wordEval_nil, yCount]
  | cons ℓ w ih =>
    have hc := commute_wordEval hg hy w
    rw [wordEval_cons, wordEval_cons, ih]
    cases ℓ
    · simp [Letter.eval, yCount, mul_assoc]
    · simp [Letter.eval, yCount, mul_assoc]
    · simp only [Letter.eval, yCount, List.count_cons_self, pow_succ', mul_assoc]
      rw [← mul_assoc s (wordEval g y w) _, hc.eq]
      simp [mul_assoc]

theorem prod_conj_rep {α β : Type*} (act : α → G) (f : α → β → β) (rep : β → G)
    (h : ∀ o s, act o * rep s * (act o)⁻¹ = rep (f o s)) (word : List α) (s : β) :
    (word.map act).prod * rep s * ((word.map act).prod)⁻¹ = rep (word.foldr f s) := by
  induction word with
  | nil => simp
  | cons o w ih =>
    rw [List.map_cons, List.prod_cons, List.foldr_cons, ← h o, ← ih]
    group

end Words

section Setting

variable {G : Type*} [Group G]

structure InnerSetting (L : Subgroup G) (t z : G) : Prop where
  htL : t ∈ centralizer (L : Set G)
  ht2 : orderOf t = 2
  hin : centralizer ({t} : Set G) = L ⊔ zpowers t
  hLC : L ⊓ centralizer (L : Set G) = ⊥
  hzL : z ∈ L
  hzt : ∀ g : G, g * t * g⁻¹ ≠ z

def Fusing (z t n : G) : Prop := n * z * n⁻¹ = z ∧ n * t * n⁻¹ = z * t

namespace InnerSetting

variable {L : Subgroup G} {t z : G} (H : InnerSetting L t z)

include H

theorem comm_t {l : G} (hl : l ∈ L) : l * t = t * l := mem_centralizer_iff.1 H.htL l hl

theorem commute_t {l : G} (hl : l ∈ L) : Commute l t := H.comm_t hl

theorem t_pow_two : t ^ 2 = 1 := by
  have := pow_orderOf_eq_one t
  rwa [H.ht2] at this

theorem tt : t * t = 1 := by
  rw [← pow_two]
  exact H.t_pow_two

theorem t_ne_one : t ≠ 1 := by
  intro h
  have := H.ht2
  rw [h, orderOf_one] at this
  omega

theorem t_not_mem : t ∉ L := by
  intro h
  have : t ∈ L ⊓ centralizer (L : Set G) := ⟨h, H.htL⟩
  rw [H.hLC, mem_bot] at this
  exact H.t_ne_one this

theorem eq_one_of_pow_mem {k : ℕ} (h : t ^ k ∈ L) : t ^ k = 1 := by
  have : t ^ k ∈ L ⊓ centralizer (L : Set G) := ⟨h, pow_mem H.htL k⟩
  rw [H.hLC, mem_bot] at this
  exact this

theorem pow_odd {k : ℕ} (hk : Odd k) : t ^ k = t := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, H.t_pow_two, one_pow, one_mul]

theorem not_isConj : ¬ IsConj t z := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  exact H.hzt g hg

theorem eq_one_or_of_mem_zpowers {d : G} (hd : d ∈ zpowers t) : d = 1 ∨ d = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hd
  rw [← zpow_mod_orderOf, H.ht2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left
    simp [h0]
  · right
    simp [h0]

theorem exists_of_mem_centralizer {x : G} (hx : x * t = t * x) :
    ∃ l ∈ L, x = l ∨ x = l * t := by
  have hx' : x ∈ L ⊔ zpowers t := by
    rw [← H.hin]
    exact mem_centralizer_singleton_iff.2 hx
  obtain ⟨l, hl, d, hd, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 H.htL) hx'
  rcases H.eq_one_or_of_mem_zpowers hd with rfl | rfl
  · exact ⟨l, hl, Or.inl (mul_one l)⟩
  · exact ⟨l, hl, Or.inr rfl⟩

theorem split {x : G} (hxt : x * t = t * x) (hxz : x * z = z * x) :
    ∃ c ∈ L ⊓ centralizer ({z} : Set G), x = c ∨ x = c * t := by
  obtain ⟨l, hl, h | h⟩ := H.exists_of_mem_centralizer hxt
  · refine ⟨l, ⟨hl, mem_centralizer_singleton_iff.2 ?_⟩, Or.inl h⟩
    rw [← h]
    exact hxz
  · refine ⟨l, ⟨hl, mem_centralizer_singleton_iff.2 ?_⟩, Or.inr h⟩
    rw [h] at hxz
    have htz : t * z = z * t := (H.comm_t H.hzL).symm
    apply mul_right_cancel (b := t)
    calc l * z * t = l * (z * t) := mul_assoc _ _ _
      _ = l * (t * z) := by rw [htz]
      _ = l * t * z := (mul_assoc _ _ _).symm
      _ = z * (l * t) := hxz
      _ = z * l * t := (mul_assoc _ _ _).symm

theorem conj_mul_t {k y : G} (hk : k ∈ L) : k * (y * t) * k⁻¹ = k * y * k⁻¹ * t := by
  have h : k⁻¹ * t = t * k⁻¹ := (H.commute_t hk).inv_left.eq
  calc k * (y * t) * k⁻¹ = k * y * (t * k⁻¹) := by group
    _ = k * y * (k⁻¹ * t) := by rw [h]
    _ = k * y * k⁻¹ * t := by group

theorem conj_eq_of_mem_centralizer {W a : G} (ha : a ∈ L) (hW : W * t = t * W) :
    ∃ l ∈ L, W * a * W⁻¹ = l * a * l⁻¹ := by
  obtain ⟨l, hl, h | h⟩ := H.exists_of_mem_centralizer hW
  · exact ⟨l, hl, by rw [h]⟩
  · refine ⟨l, hl, ?_⟩
    rw [h]
    have hta : t * a = a * t := (H.comm_t ha).symm
    calc l * t * a * (l * t)⁻¹ = l * (t * a) * t⁻¹ * l⁻¹ := by group
      _ = l * (a * t) * t⁻¹ * l⁻¹ := by rw [hta]
      _ = l * a * l⁻¹ := by group

end InnerSetting

namespace Fusing

variable {L : Subgroup G} {t z n : G}

theorem zz (H : InnerSetting L t z) (hn : Fusing z t n) : z * z = 1 := by
  have h1 : (z * t) * (z * t) = 1 := by
    rw [← hn.2]
    calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [H.tt]; group
  have htz : t * z = z * t := (H.comm_t H.hzL).symm
  have h2 : (z * t) * (z * t) = z * z * (t * t) := by
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [htz]
      _ = z * z * (t * t) := by group
  rw [h2, H.tt, mul_one] at h1
  exact h1

theorem inv_t (H : InnerSetting L t z) (hn : Fusing z t n) : n⁻¹ * t * n = z * t := by
  have hz' : n⁻¹ * z * n = z := by
    calc n⁻¹ * z * n = n⁻¹ * (n * z * n⁻¹) * n := by rw [hn.1]
      _ = z := by group
  have h3 : t = z * (n⁻¹ * t * n) := by
    calc t = n⁻¹ * (z * t) * n := by rw [← hn.2]; group
      _ = (n⁻¹ * z * n) * (n⁻¹ * t * n) := by group
      _ = z * (n⁻¹ * t * n) := by rw [hz']
  calc n⁻¹ * t * n = 1 * (n⁻¹ * t * n) := (one_mul _).symm
    _ = z * z * (n⁻¹ * t * n) := by rw [hn.zz H]
    _ = z * (z * (n⁻¹ * t * n)) := mul_assoc _ _ _
    _ = z * t := by rw [← h3]

theorem mul_of_mem (H : InnerSetting L t z) (hn : Fusing z t n) {c : G}
    (hc : c ∈ L ⊓ centralizer ({z} : Set G)) : Fusing z t (c * n) := by
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 hc.2
  have hct : c * t = t * c := H.comm_t hc.1
  constructor
  · calc c * n * z * (c * n)⁻¹ = c * (n * z * n⁻¹) * c⁻¹ := by group
      _ = z := by rw [hn.1, hcz]; group
  · calc c * n * t * (c * n)⁻¹ = c * (n * t * n⁻¹) * c⁻¹ := by group
      _ = c * z * t * c⁻¹ := by rw [hn.2]; group
      _ = z * c * t * c⁻¹ := by rw [hcz]
      _ = z * (c * t) * c⁻¹ := by group
      _ = z * (t * c) * c⁻¹ := by rw [hct]
      _ = z * t := by group

theorem conj_comm (H : InnerSetting L t z) (hn : Fusing z t n) {x : G}
    (hx : x ∈ L ⊓ centralizer ({z} : Set G)) :
    n * x * n⁻¹ * t = t * (n * x * n⁻¹) ∧ n * x * n⁻¹ * z = z * (n * x * n⁻¹) := by
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 hx.2
  have hxt : x * t = t * x := H.comm_t hx.1
  have h1 : n * x * n⁻¹ * z = z * (n * x * n⁻¹) := by
    calc n * x * n⁻¹ * z = n * x * n⁻¹ * (n * z * n⁻¹) := by rw [hn.1]
      _ = n * (x * z) * n⁻¹ := by group
      _ = n * (z * x) * n⁻¹ := by rw [hxz]
      _ = n * z * n⁻¹ * (n * x * n⁻¹) := by group
      _ = z * (n * x * n⁻¹) := by rw [hn.1]
  have h2 : n * x * n⁻¹ * (z * t) = (z * t) * (n * x * n⁻¹) := by
    calc n * x * n⁻¹ * (z * t) = n * x * n⁻¹ * (n * t * n⁻¹) := by rw [hn.2]
      _ = n * (x * t) * n⁻¹ := by group
      _ = n * (t * x) * n⁻¹ := by rw [hxt]
      _ = n * t * n⁻¹ * (n * x * n⁻¹) := by group
      _ = (z * t) * (n * x * n⁻¹) := by rw [hn.2]
  refine ⟨?_, h1⟩
  apply mul_left_cancel (a := z)
  calc z * (n * x * n⁻¹ * t) = (z * (n * x * n⁻¹)) * t := (mul_assoc _ _ _).symm
    _ = (n * x * n⁻¹ * z) * t := by rw [h1]
    _ = n * x * n⁻¹ * (z * t) := mul_assoc _ _ _
    _ = (z * t) * (n * x * n⁻¹) := h2
    _ = z * (t * (n * x * n⁻¹)) := mul_assoc _ _ _

end Fusing

theorem conj_eq_one_iff (n A : G) : n * A * n⁻¹ = 1 ↔ A = 1 := by
  constructor
  · intro h
    have := congrArg (fun x => n⁻¹ * x * n) h
    simpa [mul_assoc] using this
  · rintro rfl
    simp

theorem orderOf_conj_eq (n g : G) : orderOf (n * g * n⁻¹) = orderOf g := by
  have := orderOf_injective (MulAut.conj n : G →* G) (MulAut.conj n).injective g
  simpa [MulAut.conj_apply] using this

end Setting

section Normalize

variable {G : Type*} [Group G] {L : Subgroup G} {t z : G}

theorem exists_fix_g₁ (H : InnerSetting L t z) (D : InnerData L z) {n : G} (hn : Fusing z t n) :
    ∃ n₁ : G, Fusing z t n₁ ∧ n₁ * D.g₁ * n₁⁻¹ = D.g₁ := by
  obtain ⟨hct, hcz⟩ := hn.conj_comm H D.g₁_mem
  have ho : orderOf (n * D.g₁ * n⁻¹) = 5 := by rw [orderOf_conj_eq, D.orderOf_g₁]
  obtain ⟨c', hc', h | h⟩ := H.split hct hcz
  · rw [h] at ho
    obtain ⟨c, hc, hcc⟩ := D.order_five c' hc' ho
    refine ⟨c * n, hn.mul_of_mem H hc, ?_⟩
    calc c * n * D.g₁ * (c * n)⁻¹ = c * (n * D.g₁ * n⁻¹) * c⁻¹ := by group
      _ = D.g₁ := by rw [h]; exact hcc
  · exfalso
    rw [h] at ho
    have h5 : (c' * t) ^ 5 = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    have hcomm : Commute c' t := H.commute_t hc'.1
    rw [hcomm.mul_pow] at h5
    have ht5 : t ^ 5 = t := H.pow_odd (by decide)
    rw [ht5] at h5
    have : t = (c' ^ 5)⁻¹ := eq_inv_of_mul_eq_one_right h5
    exact H.t_not_mem (by rw [this]; exact inv_mem (pow_mem hc'.1 5))

theorem exists_normalized (H : InnerSetting L t z) (D : InnerData L z) {n : G}
    (hn : Fusing z t n) :
    ∃ (n₂ : G) (i : Fin 4), Fusing z t n₂ ∧ n₂ * D.g₁ * n₂⁻¹ = D.g₁ ∧
      (n₂ * D.a * n₂⁻¹ = D.ys i ∨ n₂ * D.a * n₂⁻¹ = D.ys i * t) := by
  obtain ⟨n₁, hn₁, hg₁⟩ := exists_fix_g₁ H D hn
  have hg1L : D.g₁ ∈ L := D.g₁_mem.1
  obtain ⟨hct, hcz⟩ := hn₁.conj_comm H D.a_mem
  obtain ⟨y, hy, hay⟩ := H.split hct hcz
  have hconjw : ∀ w, n₁ * wordEval D.g₁ D.a w * n₁⁻¹ = wordEval D.g₁ (n₁ * D.a * n₁⁻¹) w := by
    intro w
    rw [conj_wordEval, hg₁]
  have hfilter : ∀ w, wordEval D.g₁ y w = 1 ↔ wordEval D.g₁ D.a w = 1 := by
    intro w
    have hAL : wordEval D.g₁ D.a w ∈ L := wordEval_mem hg1L D.a_mem.1 w
    have hYL : wordEval D.g₁ y w ∈ L := wordEval_mem hg1L hy.1 w
    rcases hay with hay | hay
    · have hw := hconjw w
      rw [hay] at hw
      rw [← hw, conj_eq_one_iff]
    · have hw := hconjw w
      rw [hay, wordEval_mul_of_commute (H.commute_t hg1L).symm (H.commute_t hy.1).symm] at hw
      constructor
      · intro hY
        rw [hY, one_mul] at hw
        have h3 : n₁⁻¹ * t ^ yCount w * n₁ = (z * t) ^ yCount w := by
          rw [← hn₁.inv_t H]
          have := conj_pow (a := n₁⁻¹) (b := t) (i := yCount w)
          rw [inv_inv] at this
          exact this.symm
        have h2 : wordEval D.g₁ D.a w = (z * t) ^ yCount w := by
          have : wordEval D.g₁ D.a w = n₁⁻¹ * (n₁ * wordEval D.g₁ D.a w * n₁⁻¹) * n₁ := by group
          rw [this, hw, h3]
        have hcomm : Commute z t := H.comm_t H.hzL
        have htk : t ^ yCount w = (z ^ yCount w)⁻¹ * wordEval D.g₁ D.a w := by
          rw [h2, hcomm.mul_pow, ← mul_assoc, inv_mul_cancel, one_mul]
        have h1 : t ^ yCount w = 1 :=
          H.eq_one_of_pow_mem (by rw [htk]; exact mul_mem (inv_mem (pow_mem H.hzL _)) hAL)
        rw [h1] at hw
        exact (conj_eq_one_iff n₁ _).1 (by rw [hw])
      · intro hA
        rw [hA] at hw
        have h4 : wordEval D.g₁ y w * t ^ yCount w = 1 := by
          rw [← hw]
          simp
        have h5 : t ^ yCount w = (wordEval D.g₁ y w)⁻¹ := eq_inv_of_mul_eq_one_right h4
        have h6 : t ^ yCount w = 1 := H.eq_one_of_pow_mem (by rw [h5]; exact inv_mem hYL)
        rw [h6, mul_one] at h4
        exact h4
  obtain ⟨k, i, hki⟩ := D.filter y hy hfilter
  have hhk : D.h ^ k ∈ L ⊓ centralizer ({z} : Set G) := pow_mem D.h_mem k
  have hcommk : Commute (D.h ^ k) D.g₁ := Commute.pow_left (show Commute D.h D.g₁ from D.h_comm) k
  refine ⟨D.h ^ k * n₁, i, hn₁.mul_of_mem H hhk, ?_, ?_⟩
  · calc D.h ^ k * n₁ * D.g₁ * (D.h ^ k * n₁)⁻¹
        = D.h ^ k * (n₁ * D.g₁ * n₁⁻¹) * (D.h ^ k)⁻¹ := by group
      _ = D.g₁ := by rw [hg₁, hcommk.eq, mul_inv_cancel_right]
  · have hconj : D.h ^ k * n₁ * D.a * (D.h ^ k * n₁)⁻¹ =
        D.h ^ k * (n₁ * D.a * n₁⁻¹) * (D.h ^ k)⁻¹ := by group
    rcases hay with hay | hay
    · left
      rw [hconj, hay]
      exact hki
    · right
      rw [hconj, hay, H.conj_mul_t hhk.1, hki]

end Normalize

section Cases

variable {G : Type*} [Group G] {L : Subgroup G} {t z : G}

theorem conj_wordEval_eq {n g a y : G} (hg : n * g * n⁻¹ = g) (ha : n * a * n⁻¹ = y)
    (w : List Letter) : n * wordEval g a w * n⁻¹ = wordEval g y w := by
  rw [conj_wordEval, hg, ha]

theorem conj_wordEval_mul (H : InnerSetting L t z) {n g a y : G} (hgL : g ∈ L) (hyL : y ∈ L)
    (hg : n * g * n⁻¹ = g) (ha : n * a * n⁻¹ = y * t) (w : List Letter) :
    n * wordEval g a w * n⁻¹ = wordEval g y w * t ^ yCount w := by
  rw [conj_wordEval, hg, ha,
    wordEval_mul_of_commute (H.commute_t hgL).symm (H.commute_t hyL).symm]

theorem exists_conj_t (H : InnerSetting L t z) {n k x : G} (hn : Fusing z t n) (hk : k ∈ L)
    (hx : n * x * n⁻¹ = k * z * k⁻¹ * t) : ∃ g : G, x = g * t * g⁻¹ := by
  refine ⟨n⁻¹ * k * n, ?_⟩
  have h1 : x = n⁻¹ * (n * x * n⁻¹) * n := by group
  have h2 : n⁻¹ * (z * t) * n = t := by rw [← hn.2]; group
  have h3 : k * z * k⁻¹ * t = k * (z * t) * k⁻¹ := (H.conj_mul_t hk).symm
  rw [h1, hx, h3]
  calc n⁻¹ * (k * (z * t) * k⁻¹) * n
      = (n⁻¹ * k * n) * (n⁻¹ * (z * t) * n) * (n⁻¹ * k * n)⁻¹ := by group
    _ = n⁻¹ * k * n * t * (n⁻¹ * k * n)⁻¹ := by rw [h2]

theorem false_of_pres_one (H : InnerSetting L t z) (D : InnerData L z) {n : G} {i : Fin 4}
    (hn : Fusing z t n) (hi : i.val < 2) (ha : n * D.a * n⁻¹ = D.ys i * t) : False := by
  obtain ⟨⟨k, hk, hkz⟩, -⟩ := D.pres i hi
  obtain ⟨g, hg⟩ := exists_conj_t H hn hk (x := D.a) (by rw [ha, ← hkz])
  obtain ⟨ka, hka, hkaz⟩ := D.a_conj
  refine H.hzt (ka⁻¹ * g) ?_
  calc ka⁻¹ * g * t * (ka⁻¹ * g)⁻¹ = ka⁻¹ * (g * t * g⁻¹) * ka := by group
    _ = ka⁻¹ * D.a * ka := by rw [← hg]
    _ = z := by rw [← hkaz]; group

theorem exists_orth (H : InnerSetting L t z) {b u g : G} (hbg : b = g * t * g⁻¹)
    (huc : u * b = b * u) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hub : u ≠ b) (hbu : IsConj b u)
    (hbub : IsConj b (u * b)) :
    ∃ l₀ ∈ L, l₀ ≠ 1 ∧ l₀ * l₀ = 1 ∧ IsConj t l₀ ∧ IsConj t (l₀ * t) := by
  have hbt : IsConj t b := isConj_iff.2 ⟨g, hbg.symm⟩
  have hx : (g⁻¹ * u * g) * t = t * (g⁻¹ * u * g) := by
    calc g⁻¹ * u * g * t = g⁻¹ * u * (g * t * g⁻¹) * g := by group
      _ = g⁻¹ * u * b * g := by rw [← hbg]
      _ = g⁻¹ * (u * b) * g := by group
      _ = g⁻¹ * (b * u) * g := by rw [huc]
      _ = (g⁻¹ * b * g) * (g⁻¹ * u * g) := by group
      _ = t * (g⁻¹ * u * g) := by rw [hbg]; group
  obtain ⟨l₀, hl₀, hcase⟩ := H.exists_of_mem_centralizer hx
  have hconj : ∀ w : G, IsConj b w → IsConj t (g⁻¹ * w * g) := fun w hw =>
    hbt.trans (hw.trans (isConj_iff.2 ⟨g⁻¹, by simp⟩))
  have hxub : g⁻¹ * (u * b) * g = (g⁻¹ * u * g) * t := by
    conv_lhs => rw [hbg]
    group
  have h1 := hconj u hbu
  have h2 := hconj (u * b) hbub
  rw [hxub] at h2
  have hxx : (g⁻¹ * u * g) * (g⁻¹ * u * g) = 1 := by
    calc (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hu2]; group
  have hx1 : g⁻¹ * u * g ≠ 1 := fun h => hu1 (by
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hxt' : g⁻¹ * u * g ≠ t := fun h => hub (by
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [h]
      _ = b := hbg.symm)
  rcases hcase with h | h
  · refine ⟨l₀, hl₀, ?_, ?_, ?_, ?_⟩
    · intro h0
      rw [h0] at h
      exact hx1 h
    · rw [← h]
      exact hxx
    · rw [← h]
      exact h1
    · rw [← h]
      exact h2
  · refine ⟨l₀, hl₀, ?_, ?_, ?_, ?_⟩
    · intro h0
      rw [h0, one_mul] at h
      exact hxt' h
    · have hlt : l₀ * t * (l₀ * t) = l₀ * l₀ * (t * t) := by
        calc l₀ * t * (l₀ * t) = l₀ * (t * l₀) * t := by group
          _ = l₀ * (l₀ * t) * t := by rw [← H.comm_t hl₀]
          _ = l₀ * l₀ * (t * t) := by group
      rw [h] at hxx
      rw [hlt, H.tt, mul_one] at hxx
      exact hxx
    · have : l₀ = (g⁻¹ * u * g) * t := by rw [h, mul_assoc, H.tt, mul_one]
      rw [this]
      exact h2
    · rw [← h]
      exact h1

theorem false_of_swap_one (H : InnerSetting L t z) (D : InnerData L z) {n : G} {i : Fin 4}
    (hn : Fusing z t n) (hg : n * D.g₁ * n⁻¹ = D.g₁) (hi : 2 ≤ i.val)
    (ha : n * D.a * n⁻¹ = D.ys i * t) : False := by
  have hg1L : D.g₁ ∈ L := D.g₁_mem.1
  obtain ⟨k, hk, hkz⟩ := D.swap_b i hi
  have hysL : D.ys i ∈ L := (D.ys_mem i).1
  have hb : n * wordEval D.g₁ D.a D.wb * n⁻¹ = k * z * k⁻¹ * t := by
    rw [conj_wordEval_mul H hg1L hysL hg ha, H.pow_odd D.wb_odd, hkz]
  obtain ⟨g, hbg⟩ := exists_conj_t H hn hk hb
  have hbu : IsConj (wordEval D.g₁ D.a D.wb) D.u := by
    obtain ⟨k, -, hk⟩ := D.u_conj
    exact isConj_iff.2 ⟨k, hk⟩
  have hbub : IsConj (wordEval D.g₁ D.a D.wb) (D.u * wordEval D.g₁ D.a D.wb) := by
    obtain ⟨k, -, hk⟩ := D.ub_conj
    exact isConj_iff.2 ⟨k, hk⟩
  obtain ⟨l₀, hl₀, hl1, hl2, hlt, hltt⟩ :=
    exists_orth H hbg D.u_comm D.u_sq D.u_ne_one D.u_ne_b hbu hbub
  rcases D.invol l₀ hl₀ hl1 hl2 with ⟨k₀, hk₀, hk₀z⟩ | ⟨k₀, hk₀, hk₀b⟩
  · exact H.not_isConj (hlt.trans (isConj_iff.2 ⟨k₀, hk₀z⟩).symm)
  · obtain ⟨k₁, hk₁, hk₁b⟩ := D.swap_ys i hi
    have e1 : IsConj (wordEval D.g₁ D.a D.wb * t) (D.ys i * t) :=
      isConj_iff.2 ⟨k₁, by rw [← hk₁b]; exact H.conj_mul_t hk₁⟩
    have e2 : IsConj (wordEval D.g₁ D.a D.wb * t) (l₀ * t) :=
      isConj_iff.2 ⟨k₀, by rw [← hk₀b]; exact H.conj_mul_t hk₀⟩
    have e3 : IsConj D.a (D.ys i * t) := isConj_iff.2 ⟨n, ha⟩
    have e4 : IsConj z D.a := by
      obtain ⟨k, -, hk⟩ := D.a_conj
      exact isConj_iff.2 ⟨k, hk⟩
    exact H.not_isConj (hltt.trans (e2.symm.trans (e1.trans (e3.symm.trans e4.symm))))

theorem exists_normalizer_of_pres_zero (H : InnerSetting L t z) (D : InnerData L z) {n : G}
    {i : Fin 4} (hn : Fusing z t n) (hg : n * D.g₁ * n⁻¹ = D.g₁) (hi : i.val < 2)
    (ha : n * D.a * n⁻¹ = D.ys i) :
    ∃ m ∈ normalizer ((zpowers t ⊔ closure (Set.range fun j => wordEval D.g₁ D.a (D.eW j)) :
      Subgroup G) : Set G), m * t * m⁻¹ = z * t := by
  obtain ⟨-, c, hc, hcE⟩ := D.pres i hi
  have hm := hn.mul_of_mem H hc
  set E : Subgroup G := closure (Set.range fun j => wordEval D.g₁ D.a (D.eW j)) with hE
  have hmap_le : E.map (MulAut.conj (c * n) : G →* G) ≤ E := by
    rw [hE, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have : c * n * wordEval D.g₁ D.a (D.eW j) * (c * n)⁻¹ =
        c * (n * wordEval D.g₁ D.a (D.eW j) * n⁻¹) * c⁻¹ := by group
    show c * n * wordEval D.g₁ D.a (D.eW j) * (c * n)⁻¹ ∈ E
    rw [this, conj_wordEval_eq hg ha]
    exact hcE j
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [D.E_card]; norm_num)
  have hEeq : E.map (MulAut.conj (c * n) : G →* G) = E :=
    Subgroup.eq_of_le_of_card_ge hmap_le
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (c * n)).injective])
  refine ⟨c * n, ?_, hm.2⟩
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, MonoidHom.map_zpowers, hEeq]
  have h1 : (MulAut.conj (c * n) : G →* G) t = z * t := hm.2
  rw [h1]
  have hztE : z * t ∈ zpowers t ⊔ E := mul_mem (mem_sup_right D.z_mem_E) (mem_sup_left (mem_zpowers t))
  apply le_antisymm
  · exact sup_le (zpowers_le.2 hztE) le_sup_right
  · refine sup_le (zpowers_le.2 ?_) le_sup_right
    have h := mul_mem (mem_sup_right (inv_mem D.z_mem_E) : z⁻¹ ∈ zpowers (z * t) ⊔ E)
      (mem_sup_left (mem_zpowers (z * t)) : z * t ∈ zpowers (z * t) ⊔ E)
    rwa [inv_mul_cancel_left] at h

theorem false_of_stab_zero (H : InnerSetting L t z) (D : InnerData L z) {n : G} {i : Fin 4}
    (hn : Fusing z t n) (hg : n * D.g₁ * n⁻¹ = D.g₁) (hi : 2 ≤ i.val)
    (ha : n * D.a * n⁻¹ = D.ys i) : False := by
  obtain ⟨c, ψ, m, gs, σ, word, x, hc, hψ, hgs, hrun1, hrun2, k', hk', hkb⟩ := D.stab i hi
  obtain ⟨Y, hYdef⟩ : ∃ Y : Fin 8 → G, ∀ e, Y e = wordEval D.g₁ D.a (D.yW e) :=
    ⟨fun e => wordEval D.g₁ D.a (D.yW e), fun _ => rfl⟩
  have hn₃ := hn.mul_of_mem H hc
  have hY1 : ∀ e, c * n * Y e * (c * n)⁻¹ = Y (ψ e) := by
    intro e
    have : c * n * Y e * (c * n)⁻¹ = c * (n * Y e * n⁻¹) * c⁻¹ := by group
    rw [this, hYdef e, conj_wordEval_eq hg ha, hYdef (ψ e)]
    exact hψ e
  have hY2 : ∀ j e, gs j * Y e * (gs j)⁻¹ = Y (σ j e) := fun j e => by
    rw [hYdef, hYdef]
    exact (hgs j).2 e
  have hY3 : ∀ e, Y e * z = Y (D.zmul e) := fun e => by
    rw [hYdef, hYdef]
    exact D.zmul_spec e
  have hYone : Y D.eOne = 1 := by rw [hYdef]; exact D.eOne_spec
  have hYa : Y D.eA = D.a := by rw [hYdef]; exact D.eA_spec
  let rep : Fin 8 × Bool → G := fun s => Y s.1 * (if s.2 then t else 1)
  have rep_false : ∀ e, rep (e, false) = Y e := fun e => by simp [rep]
  have rep_true : ∀ e, rep (e, true) = Y e * t := fun e => by simp [rep]
  let act : Option (Fin m) → G := fun o => o.elim (c * n) gs
  have hact : ∀ o s, act o * rep s * (act o)⁻¹ = rep (stabStep ψ D.zmul σ o s) := by
    rintro o ⟨e, ε⟩
    cases o with
    | none =>
      cases ε
      · show c * n * rep (e, false) * (c * n)⁻¹ = rep (ψ e, false)
        rw [rep_false, rep_false]
        exact hY1 e
      · show c * n * rep (e, true) * (c * n)⁻¹ = rep (D.zmul (ψ e), true)
        rw [rep_true, rep_true, ← hY3 (ψ e)]
        calc c * n * (Y e * t) * (c * n)⁻¹
            = (c * n * Y e * (c * n)⁻¹) * (c * n * t * (c * n)⁻¹) := by group
          _ = Y (ψ e) * (z * t) := by rw [hY1, hn₃.2]
          _ = Y (ψ e) * z * t := (mul_assoc _ _ _).symm
    | some j =>
      cases ε
      · show gs j * rep (e, false) * (gs j)⁻¹ = rep (σ j e, false)
        rw [rep_false, rep_false]
        exact hY2 j e
      · show gs j * rep (e, true) * (gs j)⁻¹ = rep (σ j e, true)
        rw [rep_true, rep_true, ← hY2 j e]
        exact H.conj_mul_t (hgs j).1
  have hW := prod_conj_rep act (stabStep ψ D.zmul σ) rep hact word
  have hr1 := hW (D.eOne, true)
  have hr2 := hW (D.eA, false)
  have hrun1' : word.foldr (stabStep ψ D.zmul σ) (D.eOne, true) = (D.eOne, true) := hrun1
  have hrun2' : word.foldr (stabStep ψ D.zmul σ) (D.eA, false) = (x, false) := hrun2
  rw [hrun1', rep_true, hYone, one_mul] at hr1
  rw [hrun2', rep_false, rep_false, hYa] at hr2
  set W : G := (word.map act).prod with hWdef
  have hWt : W * t = t * W := by
    have : W * t * W⁻¹ = t := hr1
    calc W * t = W * t * W⁻¹ * W := by group
      _ = t * W := by rw [this]
  obtain ⟨l, hl, hla⟩ := H.conj_eq_of_mem_centralizer D.a_mem.1 hWt
  obtain ⟨ka, hka, hkaz⟩ := D.a_conj
  have hbY : wordEval D.g₁ D.a D.wb = k'⁻¹ * Y x * k' := by
    rw [hYdef, ← hkb]
    group
  refine D.not_conj (k'⁻¹ * (l * ka)) (mul_mem (inv_mem hk') (mul_mem hl hka)) ?_
  calc k'⁻¹ * (l * ka) * z * (k'⁻¹ * (l * ka))⁻¹
      = k'⁻¹ * (l * (ka * z * ka⁻¹) * l⁻¹) * k' := by group
    _ = k'⁻¹ * (l * D.a * l⁻¹) * k' := by rw [hkaz]
    _ = k'⁻¹ * (W * D.a * W⁻¹) * k' := by rw [hla]
    _ = k'⁻¹ * Y x * k' := by rw [hr2]
    _ = wordEval D.g₁ D.a D.wb := hbY.symm

end Cases

theorem exists_fusing_of_innerData {G : Type*} [Group G] {L : Subgroup G} {t z n : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (hzL : z ∈ L) (hnz : n * z * n⁻¹ = z) (hnt : n * t * n⁻¹ = z * t)
    (hzt : ∀ g : G, g * t * g⁻¹ ≠ z) (D : InnerData L z) :
    ∃ m ∈ normalizer ((zpowers t ⊔ closure (Set.range fun j => wordEval D.g₁ D.a (D.eW j)) :
      Subgroup G) : Set G), m * t * m⁻¹ = z * t := by
  have H : InnerSetting L t z := ⟨htL, ht2, hin, hLC, hzL, hzt⟩
  obtain ⟨n₂, i, hn₂, hg, ha⟩ := exists_normalized H D (show Fusing z t n from ⟨hnz, hnt⟩)
  by_cases hi : i.val < 2
  · rcases ha with ha | ha
    · exact exists_normalizer_of_pres_zero H D hn₂ hg hi ha
    · exact (false_of_pres_one H D hn₂ hi ha).elim
  · have hi' : 2 ≤ i.val := by omega
    rcases ha with ha | ha
    · exact (false_of_stab_zero H D hn₂ hg hi' ha).elim
    · exact (false_of_swap_one H D hn₂ hg hi' ha).elim

section Assembly

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem conj_mem_normalizer_map {G : Type*} [Group G] {X : Subgroup G} {m : G}
    (hm : m ∈ normalizer (X : Set G)) (c : G) :
    c * m * c⁻¹ ∈ normalizer ((X.map (MulAut.conj c : G →* G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hm ⊢
  intro h
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨m * x * m⁻¹, (hm x).1 hx, ?_⟩
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
    group
  · rintro ⟨x, hx, hxh⟩
    refine ⟨m⁻¹ * x * m, ?_, ?_⟩
    · have := (hm (m⁻¹ * x * m)).2
      rw [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at this
      exact this hx
    · simp only [MonoidHom.coe_ofClass, MulAut.conj_apply] at hxh ⊢
      calc c * (m⁻¹ * x * m) * c⁻¹ = (c * m * c⁻¹)⁻¹ * (c * x * c⁻¹) * (c * m * c⁻¹) := by group
        _ = h := by rw [hxh]; group

theorem hsInnerFusion_of_innerData
    (hdata : ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G) (z : G), IsSporadic L .HS →
      IsPGroup 2 S → ¬ 2 ∣ (S ⊓ L).relIndex L → z ∈ S ⊓ L → orderOf z = 2 →
      centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z → Nonempty (InnerData L z))
    (hexist : ∀ (G : Type) [Group G] (L S : Subgroup G) (z : G), IsSporadic L .HS →
      IsPGroup 2 S → ¬ 2 ∣ (S ⊓ L).relIndex L → z ∈ S ⊓ L → orderOf z = 2 →
      centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z →
      ∃ E : Subgroup G, E ≤ L ∧ z ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
        (∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
          φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)) ∧
        ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e)
    (huniq : ∀ (G : Type) [Group G] (L S : Subgroup G) (z : G), IsSporadic L .HS →
      IsPGroup 2 S → ¬ 2 ∣ (S ⊓ L).relIndex L → z ∈ S ⊓ L → orderOf z = 2 →
      centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z →
      ∀ {F₁ F₂ : Subgroup G}, F₁ ≤ L → F₂ ≤ L → IsElemAbelian 2 F₁ → IsElemAbelian 2 F₂ →
        Nat.card F₁ = 16 → Nat.card F₂ = 16 → z ∈ F₁ → z ∈ F₂ →
        (∀ e ∈ F₁, e ≠ 1 → ∃ a ∈ L, a * z * a⁻¹ = e) →
        (∀ e ∈ F₂, e ≠ 1 → ∃ a ∈ L, a * z * a⁻¹ = e) →
        ∃ c ∈ L ⊓ centralizer ({z} : Set G), F₁.map (MulAut.conj c : G →* G) = F₂) :
    HSInnerFusion := by
  intro G _ _ L hset t htL ht2 hin
  obtain ⟨-, hL, -, hSyl, -⟩ := hset
  obtain ⟨S, z, n, hf⟩ := (sylowFusion_iff L t).1 (hSyl t htL ht2)
  have hnz := fusionData_conj_z hf hL htL ht2 hin
  have hzt := fusionData_conj_ne_z hf hL htL ht2 hin
  have hLC := inf_centralizer_eq_bot_hs hL
  have hSL := fusionData_relIndex_odd hf hL htL ht2 hin
  have hzSL : z ∈ S ⊓ L := ⟨hf.zS, hf.zL⟩
  obtain ⟨D⟩ := hdata G L S z hL hf.pgroup hSL hzSL hf.z2 hf.zc
  obtain ⟨m, hm, hmt⟩ := exists_fusing_of_innerData htL ht2 hin hLC hf.zL hnz hf.nt hzt D
  obtain ⟨E₀, hE₀L, hzE₀, hab₀, hcard₀, hφ, htrans₀⟩ :=
    hexist G L S z hL hf.pgroup hSL hzSL hf.z2 hf.zc
  set E_D : Subgroup G := closure (Set.range fun j => wordEval D.g₁ D.a (D.eW j)) with hED
  have hEDL : E_D ≤ L := by
    rw [hED, closure_le]
    rintro _ ⟨j, rfl⟩
    exact wordEval_mem D.g₁_mem.1 D.a_mem.1 _
  obtain ⟨c, hc, hcE⟩ := huniq G L S z hL hf.pgroup hSL hzSL hf.z2 hf.zc hEDL hE₀L
    D.E_elemAbelian hab₀ D.E_card hcard₀ D.z_mem_E hzE₀ D.E_conj
    (fun e he he1 => let ⟨a, ha, h⟩ := htrans₀ e he he1; ⟨a, ha.2, h⟩)
  refine ⟨E₀, hE₀L, hab₀, hcard₀, hφ, ?_⟩
  have hcct : c * t = t * c := mem_centralizer_iff.1 htL c hc.1
  have hccz : c * z = z * c := mem_centralizer_singleton_iff.1 hc.2
  have hct : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 htL l hl
  have hm' : c * m * c⁻¹ ∈ normalizer ((zpowers t ⊔ E₀ : Subgroup G) : Set G) := by
    have h1 := conj_mem_normalizer_map hm c
    have h2 : (zpowers t ⊔ E_D : Subgroup G).map (MulAut.conj c : G →* G) = zpowers t ⊔ E₀ := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hcE]
      have : (MulAut.conj c : G →* G) t = t := by
        show c * t * c⁻¹ = t
        rw [hcct]
        group
      rw [this]
    rwa [h2] at h1
  have hmt' : (c * m * c⁻¹) * t * (c * m * c⁻¹)⁻¹ = z * t := by
    have hcti : c⁻¹ * t * c = t := by
      calc c⁻¹ * t * c = c⁻¹ * (t * c) * 1 := by group
        _ = c⁻¹ * (c * t) := by rw [hcct]; group
        _ = t := by group
    calc (c * m * c⁻¹) * t * (c * m * c⁻¹)⁻¹ = c * (m * (c⁻¹ * t * c) * m⁻¹) * c⁻¹ := by group
      _ = c * (z * t) * c⁻¹ := by rw [hcti, hmt]
      _ = (c * z) * t * c⁻¹ := by rw [mul_assoc c z t]
      _ = z * (c * t) * c⁻¹ := by rw [hccz]; group
      _ = z * t := by rw [hcct]; group
  exact forall_conj_mul_of_conj_mul hct hE₀L htrans₀ hm' hmt'

end Assembly

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
