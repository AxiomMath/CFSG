module

public import CFSG.LocalAnalysis.OddStandard.ONan76Fus
public import CFSG.LocalAnalysis.OddStandard.ONan76Split
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.ONan76

open Subgroup CFSG.ABGLocalTools

section Coord

variable {n : ℕ}

theorem actS'_apply (p : Vec n) : actS' p = (p.1 + p.2.1, p.2.2 - p.1, p.1) := rfl

theorem actS'_iter_two (p : Vec n) : actS'^[2] p = actS' (actS' p) := rfl

theorem actS'_iter_three (p : Vec n) : actS'^[3] p = actS' (actS' (actS' p)) := rfl

theorem actS'_iter_one (p : Vec n) : actS'^[1] p = actS' p := rfl

end Coord

namespace AlperinFrame

variable {G : Type*} [Group G] {n : ℕ} {v₁ v₂ v₃ s t : G} (hF : AlperinFrame n v₁ v₂ v₃ s t)

include hF

theorem exists_nf_s_of_comm (hn : 2 ≤ n) {a : ZMod (2 ^ n)}
    (ha : (2 : ZMod (2 ^ n)) ^ (n - 1) * a ≠ 0) {x : G} (hx : x ∈ hF.P)
    (hxb : x * vec v₁ v₂ v₃ ((a, 0, a) : Vec n) = vec v₁ v₂ v₃ ((a, 0, a) : Vec n) * x) :
    ∃ p : Vec n, ∃ i < 4, x = vec v₁ v₂ v₃ p * s ^ i := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨p, i, hi, e, he, rfl⟩ := hF.exists_nf hn1 hx
  interval_cases e
  · exact ⟨p, i, hi, by rw [pow_zero, mul_one]⟩
  · have h2 := fix_s_t hi ((hF.comm_nf_vec_iff hn1 p _ i 1).1 hxb)
    exfalso
    apply ha
    rw [show (2 : ZMod (2 ^ n)) ^ (n - 1) = 2 ^ (n - 2) * 2 by
      rw [← pow_succ]; congr 1; omega, mul_assoc, two_mul, h2, mul_zero]

theorem comm_mem_V (hn : 1 ≤ n) (p₁ p₂ : Vec n) (i₁ i₂ : ℕ) :
    (vec v₁ v₂ v₃ p₁ * s ^ i₁)⁻¹ * (vec v₁ v₂ v₃ p₂ * s ^ i₂)⁻¹ * (vec v₁ v₂ v₃ p₁ * s ^ i₁) *
      (vec v₁ v₂ v₃ p₂ * s ^ i₂) ∈ hF.V := by
  set n₁ := vec v₁ v₂ v₃ p₁
  set n₂ := vec v₁ v₂ v₃ p₂
  set σ₁ := s ^ i₁
  set σ₂ := s ^ i₂
  have hσ : σ₁ * σ₂ = σ₂ * σ₁ := by rw [← pow_add, ← pow_add, add_comm]
  have hσP : ∀ k : ℕ, s ^ k ∈ hF.P := fun k => pow_mem hF.s_mem_P k
  have hc : ∀ y v : G, y ∈ hF.P → v ∈ hF.V → y⁻¹ * v * y ∈ hF.V := fun y v hy hv =>
    hF.conj_mem_V hn hy hv
  have e : (n₁ * σ₁)⁻¹ * (n₂ * σ₂)⁻¹ * (n₁ * σ₁) * (n₂ * σ₂) =
      (σ₁⁻¹ * n₁⁻¹ * σ₁) * ((σ₂ * σ₁)⁻¹ * (n₂⁻¹ * n₁) * (σ₂ * σ₁)) *
        ((σ₁⁻¹ * σ₂ * σ₁)⁻¹ * n₂ * (σ₁⁻¹ * σ₂ * σ₁)) := by
    have : σ₁⁻¹ * σ₂ * σ₁ = σ₂ := by rw [mul_assoc, ← hσ, inv_mul_cancel_left]
    rw [this]
    have h21 : σ₂ * σ₁ * σ₂⁻¹ = σ₁ := by rw [← hσ, mul_inv_cancel_right]
    calc (n₁ * σ₁)⁻¹ * (n₂ * σ₂)⁻¹ * (n₁ * σ₁) * (n₂ * σ₂)
        = σ₁⁻¹ * n₁⁻¹ * σ₂⁻¹ * n₂⁻¹ * n₁ * σ₁ * n₂ * σ₂ := by group
      _ = σ₁⁻¹ * n₁⁻¹ * σ₂⁻¹ * n₂⁻¹ * n₁ * (σ₂ * σ₁ * σ₂⁻¹) * n₂ * σ₂ := by rw [h21]
      _ = _ := by group
  rw [e]
  refine mul_mem (mul_mem (hc _ _ (hσP i₁) (inv_mem (hF.vec_mem_V p₁)))
    (hc _ _ (mul_mem (hσP i₂) (hσP i₁)) (mul_mem (inv_mem (hF.vec_mem_V p₂))
      (hF.vec_mem_V p₁)))) (hc _ _ ?_ (hF.vec_mem_V p₂))
  exact mul_mem (mul_mem (inv_mem (hσP i₁)) (hσP i₂)) (hσP i₁)

theorem sq_vec_s2 {r σ : Vec n} (hσ : s ^ 4 = vec v₁ v₂ v₃ σ) :
    vec v₁ v₂ v₃ r * s ^ 2 * (vec v₁ v₂ v₃ r * s ^ 2) =
      vec v₁ v₂ v₃ (r + actS'^[2] r + σ) := by
  rw [hF.vec_s_mul_vec_s, show 2 + 2 = 4 from rfl, hσ, ← hF.vec_add]

theorem not_mem_W_of_nonsplit (hn : 2 ≤ n) (hs4 : s ^ 4 = v₁ * v₃) {r p : Vec n} {i : ℕ}
    (hi : i = 1 ∨ i = 3)
    (hj2 : vec v₁ v₂ v₃ r * s ^ 2 * (vec v₁ v₂ v₃ r * s ^ 2) = 1) :
    vec v₁ v₂ v₃ p * s ^ i * (vec v₁ v₂ v₃ r * s ^ 2) * (vec v₁ v₂ v₃ p * s ^ i)⁻¹ *
      (vec v₁ v₂ v₃ r * s ^ 2) ∉ hF.W (by omega) := by
  have hn1 : 1 ≤ n := by omega
  have hσ : s ^ 4 = vec v₁ v₂ v₃ ((1, 0, 1) : Vec n) := by rw [hs4, hF.vec_one_zero_one hn1]
  have hrel : r.1 + r.2.1 + r.2.2 = -1 := by
    rw [hF.sq_vec_s2 hσ, hF.vec_eq_one_iff hn1] at hj2
    have := congrArg Prod.fst hj2
    simp only [actS'_iter_two, actS'_apply, Prod.fst_add, Prod.fst_zero] at this
    linear_combination this
  intro hW
  rw [hF.conj_vec_s, hF.vec_s_mul_vec_s, show 2 + 2 = 4 from rfl, hσ, ← hF.vec_add,
    hF.vec_mem_W_iff hn1] at hW
  have h2 := congrArg (fun x : Vec n => x.2.1) hW
  simp only [Prod.snd_add, Prod.snd_zero, Prod.fst_add, Prod.fst_zero] at h2
  rcases hi with rfl | rfl
  · simp only [actS'_iter_one, actS'_iter_two, actS'_apply, Prod.snd_neg, Prod.fst_neg,
      Prod.snd_add, Prod.fst_add] at h2
    apply odd_add_self_ne_zero hn (p.2.1 - r.1 - r.2.1 - 1)
    linear_combination h2 + (-2) * hrel
  · simp only [actS'_iter_three, actS'_iter_two, actS'_apply, Prod.snd_neg, Prod.fst_neg,
      Prod.snd_add, Prod.fst_add] at h2
    apply odd_add_self_ne_zero hn (p.2.1 + r.1)
    linear_combination h2 + 2 * hrel

theorem y₀_comm (hn : 1 ≤ n) (hs4 : s ^ 4 = 1) {r : Vec n}
    (hj2 : vec v₁ v₂ v₃ r * s ^ 2 * (vec v₁ v₂ v₃ r * s ^ 2) = 1) :
    vec v₁ v₂ v₃ ((0, -r.2.2, -r.1) : Vec n) * s ^ 1 * (vec v₁ v₂ v₃ r * s ^ 2) *
      (vec v₁ v₂ v₃ ((0, -r.2.2, -r.1) : Vec n) * s ^ 1)⁻¹ = vec v₁ v₂ v₃ r * s ^ 2 := by
  have hσ : s ^ 4 = vec v₁ v₂ v₃ (0 : Vec n) := by rw [hs4, hF.vec_zero]
  have hrel : r.1 + r.2.1 + r.2.2 = 0 := by
    rw [hF.sq_vec_s2 hσ, hF.vec_eq_one_iff hn] at hj2
    have := congrArg Prod.fst hj2
    simp only [actS'_iter_two, actS'_apply, Prod.fst_add, Prod.fst_zero, add_zero] at this
    linear_combination this
  rw [hF.conj_vec_s]
  congr 2
  obtain ⟨a, b, c⟩ := r
  simp only at hrel
  simp only [actS'_iter_one, actS'_iter_two, actS'_apply, Prod.mk_add_mk, Prod.neg_mk,
    Prod.mk.injEq]
  and_intros
  · linear_combination hrel
  · linear_combination (-1) * hrel
  · ring

theorem y₁_conj (hn : 1 ≤ n) (r : Vec n) :
    vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) * (vec v₁ v₂ v₃ r * s ^ 2) *
      (vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n))⁻¹ =
      vec v₁ v₂ v₃ r * s ^ 2 * vec v₁ v₂ v₃ ((2 ^ (n - 1), 0, 2 ^ (n - 1)) : Vec n) := by
  have hεε := two_pow_pred_add_self hn (n := n)
  have h := hF.conj_nf r ((0, 2 ^ (n - 1), 0) : Vec n) 2 0
  rw [pow_zero, mul_one] at h
  calc vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) * (vec v₁ v₂ v₃ r * s ^ 2) *
        (vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n))⁻¹
      = vec v₁ v₂ v₃ r * s ^ 2 * ((vec v₁ v₂ v₃ r * s ^ 2)⁻¹ *
          vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) * (vec v₁ v₂ v₃ r * s ^ 2)) *
          (vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n))⁻¹ := by group
    _ = vec v₁ v₂ v₃ r * s ^ 2 * vec v₁ v₂ v₃ (act 2 0 ((0, 2 ^ (n - 1), 0) : Vec n) -
          (0, 2 ^ (n - 1), 0)) := by rw [h, hF.vec_sub, mul_assoc]
    _ = _ := by
        congr 2
        simp only [act_20, actS, Prod.mk_sub_mk, Prod.mk.injEq]
        and_intros <;> grind

theorem comm_y₁_y₀ (hn : 1 ≤ n) (p₀ : Vec n) :
    (vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n))⁻¹ * (vec v₁ v₂ v₃ p₀ * s ^ 1)⁻¹ *
      vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) * (vec v₁ v₂ v₃ p₀ * s ^ 1) =
      vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 2 ^ (n - 1)) : Vec n) := by
  have hεε := two_pow_pred_add_self hn (n := n)
  have h := hF.conj_nf p₀ ((0, 2 ^ (n - 1), 0) : Vec n) 1 0
  rw [pow_zero, mul_one] at h
  rw [mul_assoc _ (vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n)), mul_assoc, ← mul_assoc _ _
    (vec v₁ v₂ v₃ p₀ * s ^ 1), h, ← hF.vec_neg, ← hF.vec_add]
  congr 1
  simp only [act_10, actS, Prod.neg_mk, Prod.mk_add_mk, Prod.mk.injEq]
  and_intros <;> grind

theorem false_of_extremal [Finite G] (hn : 3 ≤ n) {b j k : G} (hb : b ∈ hF.V)
    (hbo : b ^ 2 ^ (n - 1) ≠ 1)
    (hext : IsSylowOf 2 (hF.P ⊓ centralizer ({b} : Set G)) (centralizer ({b} : Set G)))
    (hjS : j ∈ hF.P ⊓ centralizer ({b} : Set G)) (hjV : j ∉ hF.V) (hj2 : j * j = 1)
    (hk : k ∈ centralizer ({b} : Set G)) (hkj : k * j * k⁻¹ ∈ hF.V) : False := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hjP : j ∈ hF.P := (mem_inf.1 hjS).1
  have hjb : j * b = b * j := mem_centralizer_singleton_iff.1 (mem_inf.1 hjS).2
  obtain ⟨u₁, hu₁, u₂, hu₂W, hju₁, hju₂, hu₁o, hu₂1, hu₁₂, hH, hcomm⟩ :=
    hF.inv_data hn2 hjP hjV hj2
  have hεW : vec v₁ v₂ v₃ ((2 ^ (n - 1), 0, 0) : Vec n) ∈ hF.W hn1 :=
    (hF.vec_mem_W_iff hn1).2 (by
      simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, and_true]
      exact two_pow_pred_add_self hn1)
  have hεW' : vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) ∈ hF.W hn1 :=
    (hF.vec_mem_W_iff hn1).2 (by
      simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, true_and, and_true]
      exact two_pow_pred_add_self hn1)
  have hX : ExtSetting (centralizer ({b} : Set G)) (hF.P ⊓ centralizer ({b} : Set G)) hF.V
      (hF.W hn1) j :=
    { syl := hext
      VS := fun v hv => mem_inf.2 ⟨hF.V_le_P hv,
        mem_centralizer_singleton_iff.2 (hF.V_comm hn1 hv hb)⟩
      V_comm := fun x hx y hy => hF.V_comm hn1 hx hy
      S_V := fun x hx v hv => by
        have := hF.conj_mem_V hn1 (inv_mem (mem_inf.1 hx).1) hv
        rwa [inv_inv] at this
      mem_W := fun w => hF.mem_W_iff hn1
      card_W := hF.card_W hn1
      wc := fun g _ h => hF.weakly_closed hn fun v hv => (mem_inf.1 (h v hv)).1
      jS := hjS
      jV := hjV
      j2 := hj2
      uic := fun x hx hxV hx2 => by
        have := hF.mul_inv_mem_V_of_pow hn hb hbo (mem_inf.1 hx).1 hjP hxV hjV hx2
          (by rw [hj2]; exact one_mem _) (mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2) hjb
        rwa [inv_eq_of_mul_eq_one_right hj2] at this
      cSW := fun x hx hW => hF.mem_V_of_comm hn2 (mem_inf.1 hx).1 (hW _ hεW) (hW _ hεW')
      card_H := by
        refine card_eq_four (a := u₁ ^ 2 ^ (n - 1)) (b := u₂) ?_ ?_ hu₁o hu₂1 hu₁₂.symm
          (hF.mul_self_pow_pred hn1 hu₁) fun x hx => ?_
        · refine mem_inf.2 ⟨(hF.mem_W_iff hn1).2 ⟨pow_mem hu₁ _, hF.mul_self_pow_pred hn1 hu₁⟩,
            mem_centralizer_singleton_iff.2 ?_⟩
          exact ((Commute.pow_right (show Commute j u₁ from hju₁) _).eq).symm
        · exact mem_inf.2 ⟨hu₂W, mem_centralizer_singleton_iff.2 hju₂.symm⟩
        · exact hH x (mem_inf.1 hx).1 (mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2).symm
      comm := fun h hh hhj => hcomm h hh hhj.symm }
  refine hX.false_of_conj ?_ hk hkj
  by_cases hall : ∀ q ∈ hF.P ⊓ centralizer ({b} : Set G), q ∈ hF.V ∨ q * j ∈ hF.V
  · exact Or.inl fun _ _ _ _ q hq _ => hall q hq
  push Not at hall
  obtain ⟨q, hqS, hqV, hqj⟩ := hall
  have hqP := (mem_inf.1 hqS).1
  have hqb : q * b = b * q := mem_centralizer_singleton_iff.1 (mem_inf.1 hqS).2
  have hq2 : q * q ∉ hF.V := fun h => hqj (hX.uic q hqS hqV h)
  obtain ⟨p, i, hi, e, he, rfl⟩ := hF.exists_nf hn1 hqP
  have hτ := (hF.nf_sq_mem_V_iff hn2 p hi he).not.1 (by rwa [pow_two])
  have hi13 : i = 1 ∨ i = 3 := by omega
  have he0 : e = 0 := by omega
  subst he0
  obtain ⟨β, rfl⟩ := hF.exists_vec_of_mem_V hn1 hb
  obtain ⟨hβ2, hβ3⟩ := fix_order_four hi13 ((hF.comm_nf_vec_iff hn1 p β i 0).1 hqb)
  obtain ⟨a, b', c⟩ := β
  simp only at hβ2 hβ3
  have hac : a = c := hβ3.symm
  subst hβ2 hac
  have hεε := two_pow_pred_add_self hn1 (n := n)
  have hε0 := two_pow_pred_ne_zero hn1 (n := n)
  have hεa : (2 : ZMod (2 ^ n)) ^ (n - 1) * a ≠ 0 := by
    intro h
    apply hbo
    rw [hF.vec_pow_two_pow_pred, nsmul_two_pow_pred]
    simp only [h, mul_zero]
    exact hF.vec_zero
  have hεa' : (2 : ZMod (2 ^ n)) ^ (n - 1) * a = 2 ^ (n - 1) := by
    rcases (two_mul_eq_zero_iff hn1 _).1 (show 2 * (2 ^ (n - 1) * a) = 0 by
      rw [← mul_assoc, two_mul_two_pow_pred hn1, zero_mul]) with h | h
    · exact absurd h hεa
    · exact h
  set z := vec v₁ v₂ v₃ (((2 : ZMod (2 ^ n)) ^ (n - 1), 0, (2 : ZMod (2 ^ n)) ^ (n - 1)) :
    Vec n) with hz
  have hzb : vec v₁ v₂ v₃ ((a, 0, a) : Vec n) ^ 2 ^ (n - 1) = z := by
    rw [hF.vec_pow_two_pow_pred, nsmul_two_pow_pred]
    simp only [mul_zero, hεa']
    exact hz.symm
  have hSs : ∀ x ∈ hF.P ⊓ centralizer ({vec v₁ v₂ v₃ ((a, 0, a) : Vec n)} : Set G),
      ∃ p : Vec n, ∃ i < 4, x = vec v₁ v₂ v₃ p * s ^ i := fun x hx =>
    hF.exists_nf_s_of_comm hn2 hεa (mem_inf.1 hx).1
      (mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2)
  have hinv : ∀ x ∈ hF.P ⊓ centralizer ({vec v₁ v₂ v₃ ((a, 0, a) : Vec n)} : Set G),
      x ∉ hF.V → x * x = 1 → ∃ r : Vec n, x = vec v₁ v₂ v₃ r * s ^ 2 := by
    intro x hx hxV hx2
    obtain ⟨r, i', hi', rfl⟩ := hSs x hx
    have h1 := (hF.nf_sq_mem_V_iff hn2 r hi' (e := 0) (by norm_num)).1
      (by rw [pow_zero, mul_one, pow_two, hx2]; exact one_mem _)
    have h2 : i' ≠ 0 := by
      rintro rfl
      exact hxV (by rw [pow_zero, mul_one]; exact hF.vec_mem_V r)
    have : i' = 2 := by omega
    exact ⟨r, by rw [this]⟩
  have hcj : ∀ r h : Vec n, vec v₁ v₂ v₃ h * (vec v₁ v₂ v₃ r * s ^ 2) =
      vec v₁ v₂ v₃ r * s ^ 2 * vec v₁ v₂ v₃ h ↔ act 2 0 h = h := by
    intro r h
    have := hF.comm_nf_vec_iff hn1 r h 2 0
    rw [pow_zero, mul_one] at this
    exact ⟨fun h' => this.1 h'.symm, fun h' => (this.2 h').symm⟩
  obtain ⟨rj, rfl⟩ := hinv j hjS hjV hj2
  rcases hF.s_four with hs4 | hs4
  ·
    have hzW : z ∈ hF.W hn1 := (hF.vec_mem_W_iff hn1).2 (by
      simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, true_and]
      exact ⟨hεε, hεε⟩)
    have hz1 : z ≠ 1 := fun h => hε0 (congrArg Prod.fst ((hF.vec_eq_one_iff hn1).1 h))
    have hfixz : act 2 0 (((2 : ZMod (2 ^ n)) ^ (n - 1), 0, (2 : ZMod (2 ^ n)) ^ (n - 1)) :
        Vec n) = ((2 : ZMod (2 ^ n)) ^ (n - 1), 0, (2 : ZMod (2 ^ n)) ^ (n - 1)) := by
      simp only [act_20, actS, Prod.mk.injEq]
      and_intros <;> grind
    have hzj : ∀ r : Vec n, z * (vec v₁ v₂ v₃ r * s ^ 2) = vec v₁ v₂ v₃ r * s ^ 2 * z :=
      fun r => (hcj r _).2 hfixz
    have hHc : ∀ f ∈ hF.W hn1 ⊓ centralizer ({vec v₁ v₂ v₃ rj * s ^ 2} : Set G),
        ∃ h : Vec n, f = vec v₁ v₂ v₃ h ∧ h + h = 0 ∧ act 2 0 h = h := by
      intro f hf
      obtain ⟨hfW, hfc⟩ := mem_inf.1 hf
      obtain ⟨h, rfl⟩ := hF.exists_vec_of_mem_V hn1 ((hF.mem_W_iff hn1).1 hfW).1
      exact ⟨h, rfl, (hF.vec_mem_W_iff hn1).1 hfW,
        (hcj rj h).1 (mem_centralizer_singleton_iff.1 hfc)⟩
    refine Or.inr ⟨z, mem_inf.2 ⟨hzW, mem_centralizer_singleton_iff.2 (hzj rj)⟩, hz1, ?_, ?_, ?_⟩
    · intro x hx
      rw [← hzb]
      exact (Commute.pow_right (show Commute x (vec v₁ v₂ v₃ ((a, 0, a) : Vec n)) from
        mem_centralizer_singleton_iff.1 hx) _).eq
    · intro x hx y hy
      obtain ⟨p₁, i₁, -, rfl⟩ := hSs x hx
      obtain ⟨p₂, i₂, -, rfl⟩ := hSs y hy
      exact hF.comm_mem_V hn1 p₁ p₂ i₁ i₂
    · intro j₃ hj₃S hj₃V hj₃2
      obtain ⟨r, rfl⟩ := hinv j₃ hj₃S hj₃V hj₃2
      set p₀ : Vec n := (0, -r.2.2, -r.1) with hp₀
      set y₁ := vec v₁ v₂ v₃ ((0, (2 : ZMod (2 ^ n)) ^ (n - 1), 0) : Vec n) with hy₁
      have hy₀S : vec v₁ v₂ v₃ p₀ * s ^ 1 ∈
          hF.P ⊓ centralizer ({vec v₁ v₂ v₃ ((a, 0, a) : Vec n)} : Set G) := by
        refine mem_inf.2 ⟨mul_mem (hF.V_le_P (hF.vec_mem_V p₀)) (pow_mem hF.s_mem_P 1),
          mem_centralizer_singleton_iff.2 ?_⟩
        have := (hF.comm_nf_vec_iff hn1 p₀ ((a, 0, a) : Vec n) 1 0).2 (by
          simp only [act_10, actS, Prod.mk.injEq]
          and_intros <;> grind)
        rwa [pow_zero, mul_one] at this
      have hy₁S : y₁ ∈ hF.P ⊓ centralizer ({vec v₁ v₂ v₃ ((a, 0, a) : Vec n)} : Set G) :=
        hX.VS (hF.vec_mem_V _)
      have hy₀c := hF.y₀_comm hn1 hs4 hj₃2
      have hH0 : ∀ f ∈ hF.W hn1 ⊓ centralizer ({vec v₁ v₂ v₃ rj * s ^ 2} : Set G),
          vec v₁ v₂ v₃ p₀ * s ^ 1 * f * (vec v₁ v₂ v₃ p₀ * s ^ 1)⁻¹ = f ∨
          vec v₁ v₂ v₃ p₀ * s ^ 1 * f * (vec v₁ v₂ v₃ p₀ * s ^ 1)⁻¹ = f * z := by
        intro f hf
        obtain ⟨h, rfl, hh2, hhf⟩ := hHc f hf
        rw [hF.conj_vec_s_vec, actS'_iter_one]
        rcases actS'_fix_s2 hn1 hh2 hhf with h' | h'
        · exact Or.inl (by rw [h'])
        · exact Or.inr (by rw [h', hF.vec_add])
      have hsplit : ∀ f, f * (vec v₁ v₂ v₃ r * s ^ 2) ∈
          hF.W hn1 ⊓ centralizer ({vec v₁ v₂ v₃ rj * s ^ 2} : Set G) →
          ∃ h', h' ∈ hF.W hn1 ⊓ centralizer ({vec v₁ v₂ v₃ rj * s ^ 2} : Set G) ∧
            f = h' * (vec v₁ v₂ v₃ r * s ^ 2) := fun f hf =>
        ⟨_, hf, by rw [mul_assoc, hj₃2, mul_one]⟩
      refine ⟨vec v₁ v₂ v₃ p₀ * s ^ 1, hy₀S, y₁, hy₁S, fun f hf => ?_, fun f hf => ?_, ?_, ?_, ?_⟩
      · rcases hf with hf | hf
        · exact hH0 f hf
        · obtain ⟨h', hh', rfl⟩ := hsplit f hf
          rw [show vec v₁ v₂ v₃ p₀ * s ^ 1 * (h' * (vec v₁ v₂ v₃ r * s ^ 2)) *
              (vec v₁ v₂ v₃ p₀ * s ^ 1)⁻¹ =
              (vec v₁ v₂ v₃ p₀ * s ^ 1 * h' * (vec v₁ v₂ v₃ p₀ * s ^ 1)⁻¹) *
                (vec v₁ v₂ v₃ p₀ * s ^ 1 * (vec v₁ v₂ v₃ r * s ^ 2) *
                  (vec v₁ v₂ v₃ p₀ * s ^ 1)⁻¹) by group, hy₀c]
          rcases hH0 h' hh' with h'' | h''
          · exact Or.inl (by rw [h''])
          · exact Or.inr (by rw [h'', mul_assoc, hzj r, ← mul_assoc])
      · rcases hf with hf | hf
        · obtain ⟨h, rfl, -, -⟩ := hHc f hf
          exact Or.inl (by rw [hy₁, hF.vec_comm, mul_inv_cancel_right])
        · refine Or.inr ?_
          obtain ⟨h', hh', rfl⟩ := hsplit f hf
          obtain ⟨h, rfl, -, -⟩ := hHc h' hh'
          rw [show y₁ * (vec v₁ v₂ v₃ h * (vec v₁ v₂ v₃ r * s ^ 2)) * y₁⁻¹ =
            y₁ * vec v₁ v₂ v₃ h * y₁⁻¹ * (y₁ * (vec v₁ v₂ v₃ r * s ^ 2) * y₁⁻¹) by group,
            hy₁, hF.vec_comm, mul_inv_cancel_right, hF.y₁_conj hn1 r, ← mul_assoc]
      · rw [hy₁, hF.comm_y₁_y₀ hn1 p₀]
        refine mem_inf.2 ⟨(hF.vec_mem_W_iff hn1).2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
        · simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, true_and]
          exact ⟨hεε, hεε⟩
        · refine (hcj rj _).2 ?_
          simp only [act_20, actS, Prod.mk.injEq]
          and_intros <;> grind
      · rw [hy₁, hF.comm_y₁_y₀ hn1 p₀]
        intro h
        exact hε0 (congrArg (fun x : Vec n => x.2.1) ((hF.vec_eq_one_iff hn1).1 h))
      · rw [hy₁, hF.comm_y₁_y₀ hn1 p₀, hz]
        intro h
        exact hε0 (congrArg Prod.fst ((hF.vec_inj hn1).1 h)).symm
  ·
    refine Or.inl fun j₃ hj₃S hj₃V hj₃2 q' hq'S hW => ?_
    obtain ⟨r, rfl⟩ := hinv j₃ hj₃S hj₃V hj₃2
    obtain ⟨p', i', hi', rfl⟩ := hSs q' hq'S
    interval_cases i'
    · left
      rw [pow_zero, mul_one]
      exact hF.vec_mem_V p'
    · exact absurd hW (hF.not_mem_W_of_nonsplit hn2 hs4 (Or.inl rfl) hj₃2)
    · right
      rw [hF.vec_s_mul_vec_s, show 2 + 2 = 4 from rfl]
      exact mul_mem (hF.vec_mem_V _) hF.s_four_mem_V
    · exact absurd hW (hF.not_mem_W_of_nonsplit hn2 hs4 (Or.inr rfl) hj₃2)

end AlperinFrame

end CFSG.OddStandard.ONan76
