module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitBasic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainStart

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn

variable {G : Type} [Group G]

section Cm

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G}

theorem conj_cmX (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) {w : G} :
    t * cm t w * t⁻¹ = (cm t w)⁻¹ := by
  have ht := hS.shape.inv_eq
  have h2 : t * t = 1 := hS.shape.mul_self
  have e : (cm t w)⁻¹ = t * w * t⁻¹ * w⁻¹ := by simp only [cm]; group
  rw [e, ht]
  calc t * cm t w * t = t * w * t * w⁻¹ * (t * t) := by simp only [cm, ht]; group
    _ = t * w * t * w⁻¹ := by rw [h2, mul_one]

theorem cm_conjX (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) {x w : G} (hx : x ∈ P ⊔ zpowers x₀) :
    cm t (x * w * x⁻¹) = x * cm t w * x⁻¹ := by
  have h1 : t = x * t * x⁻¹ := by rw [hS.commute_of_mem_K hx, mul_inv_cancel_right]
  simp only [cm]
  conv_lhs => rw [h1]
  group

end Cm

namespace Premises

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {W : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hW : Premises t Q W)
include hS hW

theorem mem_Q_of_commuteX {w : G} (hw : w ∈ W) (h : w * t = t * w) : w ∈ Q := by
  have hc : w ∈ centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 h, mem_centralizer_iff.2 fun q hq =>
      hW.comm q (hW.Q_le hq) w hw⟩
  rw [hS.shape.centralizer_eq] at hc
  obtain ⟨q, hq, rfl | rfl⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 hc
  · exact hq
  · exact absurd (by simpa using mul_mem (inv_mem (hW.Q_le hq)) hw) hW.t_not_mem

theorem cm_eq_one_iffX {w : G} (hw : w ∈ W) : cm t w = 1 ↔ w ∈ Q := by
  constructor
  · intro h
    refine hW.mem_Q_of_commuteX hS hw ?_
    have : w * t * w⁻¹ = t := by rw [← mul_inv_eq_one]; exact h
    calc w * t = w * t * w⁻¹ * w := by group
      _ = t * w := by rw [this]
  · intro hq
    have := hS.shape.commute_of_mem (hS.rad.Q_le_L hq)
    simp only [cm]
    rw [this]
    group

theorem P_conj_memX {x w : G} (hx : x ∈ P) (hw : w ∈ W) : x * w * x⁻¹ ∈ W :=
  hW.norm x (hS.P_le_normalizer_E hx) w hw

theorem K_conj_memX {x w : G} (hx : x ∈ P ⊔ zpowers x₀) (hw : w ∈ W) : x * w * x⁻¹ ∈ W :=
  hW.norm x (hS.K_le_normalizer_E hx) w hw

theorem card_rangeX [Finite G] : Nat.card (cmHom hW).range = 64 := by
  have hker : (cmHom hW).ker = Q.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hW.cm_eq_one_iffX hS w.2
  have h := card_mul_index (cmHom hW).ker
  rw [index_ker, hker, hW.card_eq,
    Nat.card_congr (subgroupOfEquivOfLe hW.Q_le).toEquiv, hS.rad.card_Q] at h
  omega

theorem range_eqX [Finite G] : (cmHom hW).range = Q := by
  set R := (cmHom hW).range
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    hW.comm x (hW.range_le hx) y (hW.range_le hy)
  have hle : om R 2 ≤ Q := by
    intro x hx
    obtain ⟨hxR, hx2⟩ := (mem_om hRc).1 hx
    obtain ⟨w, rfl⟩ := hxR
    refine hW.mem_Q_of_commuteX hS (hW.cm_mem w.2) ?_
    have h1 := conj_cmX hS (w := (w : G))
    have h2 : (cm t w)⁻¹ = cm t w := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
    rw [h2] at h1
    change cm t w * t = t * cm t w
    calc cm t w * t = t * cm t w * t⁻¹ * t := by rw [h1]
      _ = t * cm t w := by group
  have hP : ∀ x ∈ P, ∀ s ∈ om R 2, x * s * x⁻¹ ∈ om R 2 := by
    intro x hx s hs
    obtain ⟨hsR, hs2⟩ := (mem_om hRc).1 hs
    obtain ⟨w, rfl⟩ := hsR
    refine mem_om_of (MonoidHom.mem_range.2 ⟨⟨x * w * x⁻¹, hW.P_conj_memX hS hx w.2⟩,
      cm_conjX hS (mem_sup_left hx)⟩) ?_
    rw [conj_pow, hs2, mul_one, mul_inv_cancel]
  have hne : om R 2 ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2
      (by rw [hW.card_rangeX hS]; norm_num)
    intro hbot
    have hxm : (x : G) ∈ om R 2 := mem_om_of x.2 (by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [hbot, mem_bot] at hxm
    have : x = 1 := Subtype.ext hxm
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hQ := eq_of_le_of_ne_bot hS.rad hle hP hne
  refine (eq_of_le_of_card_ge (hQ ▸ om_le R 2) ?_).symm
  rw [hW.card_rangeX hS, hS.rad.card_Q]

theorem cm_mem_QX [Finite G] {w : G} (hw : w ∈ W) : cm t w ∈ Q := by
  rw [← hW.range_eqX hS]
  exact ⟨⟨w, hw⟩, rfl⟩

theorem exists_cm_eqX [Finite G] {q : G} (hq : q ∈ Q) :
    ∃ w ∈ W, cm t w = q := by
  rw [← hW.range_eqX hS] at hq
  obtain ⟨w, rfl⟩ := hq
  exact ⟨w, w.2, rfl⟩

theorem mul_self_mem_QX [Finite G] {w : G} (hw : w ∈ W) :
    w * w ∈ Q := by
  rw [← hW.cm_eq_one_iffX hS (mul_mem hw hw), hW.cm_mul hw hw]
  exact hS.rad.Q_mul_self (hW.cm_mem_QX hS hw)

theorem mul_self_eq_of_cm_eqX [Finite G] {w w' : G} (hw : w ∈ W) (hw' : w' ∈ W)
    (h : cm t w = cm t w') : w * w = w' * w' := by
  have hq : w⁻¹ * w' ∈ Q := by
    rw [← hW.cm_eq_one_iffX hS (mul_mem (inv_mem hw) hw'), hW.cm_mul (inv_mem hw) hw',
      hW.cm_inv hw, h, inv_mul_cancel]
  obtain ⟨q, hq', rfl⟩ : ∃ q ∈ Q, w' = w * q := ⟨w⁻¹ * w', hq, by group⟩
  have hqw : q * w = w * q := hW.comm q (hW.Q_le hq') w hw
  calc w * w = w * w * (q * q) := by rw [hS.rad.Q_mul_self hq', mul_one]
    _ = w * (q * w) * q := by rw [hqw]; group
    _ = w * q * (w * q) := by group

theorem le_normalizer_EX [Finite G] :
    W ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
  intro w hw
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hx
  · rw [hW.comm w hw _ (hW.Q_le (hS.rad.ψ_mem v)), mul_inv_cancel_right]
    exact mem_sup_left (hS.rad.ψ_mem v)
  · have e : w * (t * ψ v) * w⁻¹ = cm t w * t * ψ v := by
      have := hW.comm w hw _ (hW.Q_le (hS.rad.ψ_mem v))
      simp only [cm]
      calc w * (t * ψ v) * w⁻¹ = w * t * (ψ v * w⁻¹) := by group
        _ = w * t * (w⁻¹ * ψ v) := by
          rw [show ψ v * w⁻¹ = w⁻¹ * ψ v by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← this, inv_mul_cancel_left]]
        _ = w * t * w⁻¹ * t⁻¹ * t * ψ v := by group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left (hW.cm_mem_QX hS hw)) t_mem_sup)
      (mem_sup_left (hS.rad.ψ_mem v))

theorem normalizer_E_eqX [Finite G] :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) = W ⊔ (P ⊔ zpowers x₀ ⊔ zpowers t) := by
  set X : Subgroup G := P ⊔ zpowers x₀ ⊔ zpowers t
  have hXle : X ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    sup_le hS.K_le_normalizer_E (zpowers_le.2 (le_normalizer t_mem_sup))
  have hle : W ⊔ X ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    sup_le (hW.le_normalizer_EX hS) hXle
  have hXW : X ≤ normalizer (W : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun w hw => hW.norm x (hXle hx) w hw
  have hinf : X ⊓ W = Q := by
    refine le_antisymm (fun x hx => hW.mem_Q_of_commuteX hS hx.2
      (mem_centralizer_singleton_iff.1 (hS.KT_le_centralizer hx.1))) (le_inf ?_ hW.Q_le)
    exact (hS.rad.Q_le_U.trans hS.rad.U_le_P).trans (le_sup_left.trans le_sup_left)
  have h1 := card_sup_mul_card_inf hXW
  rw [hinf, hS.rad.card_Q, hS.card_KT, hW.card_eq, sup_comm] at h1
  have h2 := hS.card_normalizer_E
  have h3 : Nat.card (Zset t Q ψ) ≤ 64 := by
    calc Nat.card (Zset t Q ψ) ≤ Nat.card V6 := Finite.card_subtype_le _
      _ = 64 := by rw [Nat.card_eq_fintype_card]; simp
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [h2]
  have : Nat.card (W ⊔ X : Subgroup G) = 64 * (2 * Nat.card (P ⊔ zpowers x₀ : Subgroup G)) := by
    have := h1
    omega
  rw [this]
  exact Nat.mul_le_mul_right _ h3

theorem sq_eq_one_or_invX [Finite G] (hE : EndF2 ε) :
    (∀ w ∈ W, w * w = 1) ∨ (∀ w ∈ W, t * w * t⁻¹ = w⁻¹) := by
  have hex : ∀ v : V6, ∃ w ∈ W, cm t w = ψ v := fun v => hW.exists_cm_eqX hS (hS.rad.ψ_mem v)
  choose wv hwv hcm using hex
  set f : V6 → V6 := fun v => coord ψ (wv v * wv v) with hfdef
  have hf : ∀ v, ψ (f v) = wv v * wv v := fun v =>
    hS.rad.ψ_coord (hW.mul_self_mem_QX hS (hwv v))
  have hadd : ∀ v v', f (v + v') = f v + f v' := by
    intro v v'
    apply hS.rad.ψ_inj
    rw [hf, hS.rad.ψ_add, hf, hf]
    have h1 : cm t (wv (v + v')) = cm t (wv v * wv v') := by
      rw [hcm, hW.cm_mul (hwv v) (hwv v'), hcm, hcm, hS.rad.ψ_add]
    rw [hW.mul_self_eq_of_cm_eqX hS (hwv _) (mul_mem (hwv v) (hwv v')) h1]
    have hc := hW.comm _ (hwv v) _ (hwv v')
    calc wv v * wv v' * (wv v * wv v') = wv v * (wv v' * wv v) * wv v' := by group
      _ = wv v * (wv v * wv v') * wv v' := by rw [hc]
      _ = wv v * wv v * (wv v' * wv v') := by group
  have hequiv : ∀ i : Fin 6, ∀ v, f (genMat ε i *ᵥ v) = genMat ε i *ᵥ f v := by
    intro i v
    apply hS.rad.ψ_inj
    rw [hf, ← hS.rad.p_act, hf]
    have hp := hS.rad.p_mem i
    have h1 : cm t (wv (genMat ε i *ᵥ v)) = cm t (p i * wv v * (p i)⁻¹) := by
      rw [hcm, cm_conjX hS (mem_sup_left hp), hcm, hS.rad.p_act]
    rw [hW.mul_self_eq_of_cm_eqX hS (hwv _) (hW.P_conj_memX hS hp (hwv v)) h1]
    group
  have hv : ∀ w ∈ W, cm t w = cm t (wv (coord ψ (cm t w))) := fun w hw => by
    rw [hcm, hS.rad.ψ_coord (hW.cm_mem_QX hS hw)]
  rcases hE f hadd hequiv with h0 | hid
  · left
    intro w hw
    rw [hW.mul_self_eq_of_cm_eqX hS hw (hwv _) (hv w hw), ← hf, h0, hS.rad.ψ_zero]
  · right
    intro w hw
    have hsq : w * w = cm t w := by
      rw [hW.mul_self_eq_of_cm_eqX hS hw (hwv _) (hv w hw), ← hf, hid, ← hcm, ← hv w hw]
    have h3 : w * w = w * (t * w⁻¹ * t⁻¹) := by rw [hsq]; simp only [cm]; group
    have h2 : w = t * w⁻¹ * t⁻¹ := mul_left_cancel h3
    calc t * w * t⁻¹ = (t * w⁻¹ * t⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [← h2]

theorem level_twoX [Finite G]
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) : Level Q 2 W := by
  refine ⟨hW.comm, by rw [hW.card_eq]; norm_num, hW.Q_le, fun w hw h => ?_, fun w hw => ?_⟩
  · rw [← hW.cm_eq_one_iffX hS hw, cm_eq_sq hinv hw, h]
  · have h := hS.rad.Q_mul_self (hW.cm_mem_QX hS hw)
    rw [cm_eq_sq hinv hw] at h
    rw [show 2 ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
    exact h

end Premises

end CFSG.EvenSmallLie.OmegaEight.Chain
