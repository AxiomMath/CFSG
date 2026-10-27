module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Q
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Cent

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Cfg

variable {d : Datum A} (K : Cfg d 0)

include K

theorem Q_le_W (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) : d.Q ≤ K.c.W := fun u hu =>
  (Subgroup.zpowers_le.2 (K.c.t_mem_W K.h K.hP K.hQ K.hα)) (hQt u hu)

theorem qwSub_eq_W (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) : qwSub K.c = K.c.W :=
  sup_eq_right.2 (K.Q_le_W hQt)

theorem W_le_centralizer_V : K.c.W ≤ centralizer (K.c.V : Set G) :=
  K.qwSub_le_centralizer_V.trans' le_sup_right

end Cfg

namespace Cfg

variable {d : Datum A} (K : Cfg d 0)

include K

theorem X_le_normalizer_V : d.X ≤ normalizer (K.c.V : Set G) := fun _ hx =>
  mem_normalizer_iff.2 fun v => (K.c.X_normalizes K.hα K.h K.hP K.hQ K.hS2 K.hc hx).2 v

theorem W_normalized {h : G} (hh : h ∈ normalizer (K.c.V : Set G)) (w : G) :
    w ∈ K.c.W ↔ h * w * h⁻¹ ∈ K.c.W := by
  obtain ⟨c, hcC, -, hP⟩ := K.exists_mul_mem_normalizer_P hh
  set h₀ := c⁻¹ * h with hh₀
  have hg : ∀ w ∈ K.c.W, h₀ * w * h₀⁻¹ ∈ d.X := fun w hw =>
    ((mem_normalizer_iff.1 hP w).1 ⟨d.S_le_X hw.1, K.W_le_centralizer_V hw⟩).1
  have h0 := (K.c.normalizes_of_conj_le_X K.hα K.h K.hP K.hQ K.hS2 K.hc hg).1 w
  have hcW : ∀ x, x ∈ K.c.W ↔ c * x * c⁻¹ ∈ K.c.W := fun x =>
    ⟨fun hx => K.conj_mem_W_of_mem_centralizer_V hcC hx, fun hx => by
      have := K.conj_mem_W_of_mem_centralizer_V (inv_mem hcC) hx
      simpa [mul_assoc] using this⟩
  have e : h * w * h⁻¹ = c * (h₀ * w * h₀⁻¹) * c⁻¹ := by rw [hh₀]; group
  rw [e, ← hcW, h0]

theorem P_normalized {h : G} (hh : h ∈ normalizer (K.c.V : Set G)) {c : G}
    (hc : c ∈ centralizer (K.c.V : Set G)) : h * c * h⁻¹ ∈ centralizer (K.c.V : Set G) :=
  conj_mem_centralizer_of_normalizer (fun v => mem_normalizer_iff.1 hh v) hc

theorem W_relIndex_two (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) :
    K.c.W.relIndex (d.X ⊓ centralizer (K.c.V : Set G)) = 2 := by
  have := K.qw_relIndex_two
  rwa [K.qwSub_eq_W hQt] at this

theorem card_P (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) :
    Nat.card (d.X ⊓ centralizer (K.c.V : Set G) : Subgroup G) = 2 * Nat.card K.c.W := by
  have h := Subgroup.relIndex_mul_card K.c.W (d.X ⊓ centralizer (K.c.V : Set G))
  rw [inf_eq_left.2 (le_inf (K.W_le_S.trans d.S_le_X) K.W_le_centralizer_V),
    K.W_relIndex_two hQt] at h
  omega

theorem exists_order_seven (hqπ : IsConj d.q K.c.pi) :
    ∃ n : G, ∃ hn : n ∈ normalizer (K.c.V : Set G),
      n ∈ normalizer ((d.X ⊓ centralizer (K.c.V : Set G) : Subgroup G) : Set G) ∧
      (∃ k : ℕ, orderOf n = 7 ^ k) ∧ orderOf (K.c.V.normalizerMonoidHom ⟨n, hn⟩) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set ρ := K.c.V.normalizerMonoidHom with hρ
  have hsurj := K.c.surjective_normalizerMonoidHom_of_isConj K.hα K.h K.hP K.hQ K.hS2 K.hc
    K.g_norm K.g_act hqπ
  have hV2 : ∀ v : ↥K.c.V, v * v = 1 := fun v => Subtype.ext (K.sf.V_sq v v.2)
  have hA : Nat.card (MulAut ↥K.c.V) = 168 := card_mulAut_elemAb8 K.sf.card_V hV2
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := MulAut ↥K.c.V) 7 (by rw [hA]; norm_num)
  obtain ⟨n₁, hn₁⟩ := hsurj σ
  obtain ⟨c, hcC, hn₂N, hn₂P⟩ := K.exists_mul_mem_normalizer_P n₁.2
  set n₂ : ↥(normalizer (K.c.V : Set G)) := ⟨c⁻¹ * n₁, hn₂N⟩ with hn₂
  have hcN : c ∈ normalizer (K.c.V : Set G) := (centralizer_le_normalizer _) hcC
  have hρc : ρ ⟨c, hcN⟩ = 1 := by
    have : (⟨c, hcN⟩ : ↥(normalizer (K.c.V : Set G))) ∈ ρ.ker := by
      rw [hρ, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf]
      exact hcC
    exact this
  have hρn₂ : ρ n₂ = σ := by
    have e : n₂ = (⟨c, hcN⟩ : ↥(normalizer (K.c.V : Set G)))⁻¹ * n₁ := Subtype.ext rfl
    rw [e, map_mul, map_inv, hρc, inv_one, one_mul, hn₁]
  obtain ⟨e, m, hm7, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n₂).ne' 7 (by norm_num)
  have hmpos : m ≠ 0 := fun h0 => by rw [h0, mul_zero] at hm; exact (orderOf_pos n₂).ne' hm
  refine ⟨((n₂ ^ m : ↥(normalizer (K.c.V : Set G))) : G), (n₂ ^ m).2, ?_, ⟨e, ?_⟩, ?_⟩
  · simpa using pow_mem hn₂P m
  · rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hmpos ⟨7 ^ e, by rw [hm, mul_comm]⟩, hm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hmpos)]
  · have e1 : (⟨((n₂ ^ m : ↥(normalizer (K.c.V : Set G))) : G), (n₂ ^ m).2⟩ :
        ↥(normalizer (K.c.V : Set G))) = n₂ ^ m := rfl
    rw [e1, map_pow, hρn₂]
    have hcop : (orderOf σ).Coprime m := by
      rw [hσ]
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hm7
    rw [hcop.orderOf_pow, hσ]

theorem no_fixed_of_order_seven {n : G} (hn : n ∈ normalizer (K.c.V : Set G))
    (hord : orderOf (K.c.V.normalizerMonoidHom ⟨n, hn⟩) = 7)
    {v : G} (hv : v ∈ K.c.V) (hv1 : v ≠ 1) (hnv : n * v * n⁻¹ = v) : False := by
  set ρ := K.c.V.normalizerMonoidHom with hρ
  have hv1' : (⟨v, hv⟩ : ↥K.c.V) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hfix : ρ ⟨n, hn⟩ ⟨v, hv⟩ = ⟨v, hv⟩ := by
    apply Subtype.ext
    rw [hρ, Sec2Aux.normalizerMonoidHom_coe]
    exact hnv
  exact no_fixed_of_orderOf_seven K.sf.card_V hord hv1' hfix

theorem exists_pow_conj_of_order_seven {n : G} (hn : n ∈ normalizer (K.c.V : Set G))
    (hord : orderOf (K.c.V.normalizerMonoidHom ⟨n, hn⟩) = 7) {v w : G} (hv : v ∈ K.c.V)
    (hw : w ∈ K.c.V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ j : ℕ, n ^ j * v * (n ^ j)⁻¹ = w := by
  set ρ := K.c.V.normalizerMonoidHom with hρ
  set c : MulAut ↥K.c.V := ρ ⟨n, hn⟩ with hc
  obtain ⟨v₀, hv₀⟩ := GL32Aux.exists_cover_of_orderOf_seven K.sf.card_V hord
  obtain ⟨a, ha⟩ := hv₀ ⟨v, hv⟩ (fun h => hv1 (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ := hv₀ ⟨w, hw⟩ (fun h => hw1 (congrArg Subtype.val h))
  have hc7 : c ^ 7 = 1 := by rw [← hord]; exact pow_orderOf_eq_one c
  refine ⟨6 * a + b, ?_⟩
  have h1 : (c ^ (6 * a + b)) ⟨v, hv⟩ = ⟨w, hw⟩ := by
    rw [← hb, ← ha, ← MulAut.mul_apply, ← pow_add, show 6 * a + b + a = 7 * a + b by ring, pow_add,
      pow_mul, hc7, one_pow, one_mul]
  have h2 : (c ^ (6 * a + b)) ⟨v, hv⟩ = ρ (⟨n, hn⟩ ^ (6 * a + b)) ⟨v, hv⟩ := by
    rw [hc, map_pow]
  rw [h2] at h1
  have h3 := congrArg Subtype.val h1
  rw [hρ, Sec2Aux.normalizerMonoidHom_coe] at h3
  simpa using h3

theorem exists_fixed_involution (hqπ : IsConj d.q K.c.pi)
    (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) :
    ∃ n : G, ∃ hn : n ∈ normalizer (K.c.V : Set G), (∃ k : ℕ, orderOf n = 7 ^ k) ∧
      orderOf (K.c.V.normalizerMonoidHom ⟨n, hn⟩) = 7 ∧
      ∃ z : G, z ∈ d.X ⊓ centralizer (K.c.V : Set G) ∧ z ∉ K.c.W ∧ z * z = 1 ∧
        n * z * n⁻¹ = z := by
  obtain ⟨n, hnN, hnP, ⟨k, hk⟩, hord⟩ := K.exists_order_seven hqπ
  have hPn : ∀ x : G, x ∈ d.X ⊓ centralizer (K.c.V : Set G) →
      n * x * n⁻¹ ∈ d.X ⊓ centralizer (K.c.V : Set G) := fun x hx =>
    (mem_normalizer_iff.1 hnP x).1 hx
  have hWn : ∀ x : G, x ∈ K.c.W → n * x * n⁻¹ ∈ K.c.W := fun x hx => (K.W_normalized hnN x).1 hx
  have hWP : K.c.W ≤ d.X ⊓ centralizer (K.c.V : Set G) :=
    le_inf (K.W_le_S.trans d.S_le_X) K.W_le_centralizer_V
  obtain ⟨z, hzP, hzW, hzn⟩ := exists_fixed_mem_sdiff_of_orderOf_seven_pow hk hWP hPn hWn
    (K.card_P hQt) K.sf.card_W
  refine ⟨n, hnN, ⟨k, hk⟩, hord, z, hzP, hzW, ?_, hzn⟩
  rcases K.centralizer_V_cases hzP with hB | ⟨y, hy, b, hb, hzb⟩
  · exact absurd ((K.qwSub_eq_W hQt) ▸ hB) hzW
  · obtain ⟨hyX, -, hact⟩ := K.c.rep_mem Kind.graph y hy
    have hbW : b ∈ K.c.W := (K.qwSub_eq_W hQt) ▸ hb
    have hy2W : y * y ∈ K.c.W :=
      K.Q_le_W hQt (K.c.sq_mem_Q K.hα K.h K.hP K.hQ Kind.graph hyX hact)
    have hyW : ∀ w, w ∈ K.c.W → y * w * y⁻¹ ∈ K.c.W := fun w hw =>
      ((K.c.X_normalizes K.hα K.h K.hP K.hQ K.hS2 K.hc hyX).1 w).1 hw
    have hzz : z * z ∈ K.c.W := by
      rw [hzb]
      have e : b * y * (b * y) = b * (y * b * y⁻¹) * (y * y) := by group
      rw [e]
      exact mul_mem (mul_mem hbW (hyW b hbW)) hy2W
    by_contra hne
    have hzzX : z * z ∈ d.X := d.S_le_X hzz.1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 d.X_sylow.isPGroup) ⟨z * z, hzzX⟩
    rw [Subgroup.orderOf_mk] at hj
    obtain ⟨k, hk⟩ := exists_pow_orderOf_two hne ⟨j, hj⟩
    have hvW : (z * z) ^ k ∈ K.c.W := pow_mem hzz k
    have hv2 : (z * z) ^ k * (z * z) ^ k = 1 := by
      have := pow_orderOf_eq_one ((z * z) ^ k)
      rw [hk] at this
      simpa [pow_two] using this
    have hvV : (z * z) ^ k ∈ K.c.V := K.sf.W_invol _ hvW hv2
    have hv1 : (z * z) ^ k ≠ 1 := fun h => by
      rw [h, orderOf_one] at hk
      omega
    have hnzz : n * (z * z) * n⁻¹ = z * z := by
      calc n * (z * z) * n⁻¹ = (n * z * n⁻¹) * (n * z * n⁻¹) := by group
        _ = z * z := by rw [hzn]
    have hnv : n * (z * z) ^ k * n⁻¹ = (z * z) ^ k := by
      rw [← conj_pow, hnzz]
    exact K.no_fixed_of_order_seven hnN hord hvV hv1 hnv

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
