module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainBasic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Setup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Orbit

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => h x hx
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    exact this ▸ hy

@[expose] def EndF2 (ε : Eps) : Prop :=
  ∀ f : V6 → V6, (∀ v w, f (v + w) = f v + f w) →
    (∀ i : Fin 6, ∀ v, f (genMat ε i *ᵥ v) = genMat ε i *ᵥ f v) → (∀ v, f v = 0) ∨ (∀ v, f v = v)

theorem span_plus : ∀ b : Bool, ∀ j < 6, ∃ y < 64, (y = 0 ∨ qfB .plus y = b) ∧
    (2 ^ j ^^^ y = 0 ∨ qfB .plus (2 ^ j ^^^ y) = b) := by decide

theorem span_minus : ∀ b : Bool, ∀ j < 6, ∃ y < 64, (y = 0 ∨ qfB .minus y = b) ∧
    (2 ^ j ^^^ y = 0 ∨ qfB .minus (2 ^ j ^^^ y) = b) := by decide

theorem span (ε : Eps) : ∀ b : Bool, ∀ j < 6, ∃ y < 64, (y = 0 ∨ qfB ε y = b) ∧
    (2 ^ j ^^^ y = 0 ∨ qfB ε (2 ^ j ^^^ y) = b) := by
  cases ε
  · exact span_plus
  · exact span_minus

section Irred

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G}

@[expose] def vecSub (hR : RadicalData ε L U Q P a ψ p) (S : Subgroup G) : AddSubgroup V6 where
  carrier := {v | ψ v ∈ S}
  zero_mem' := by
    change ψ 0 ∈ S
    rw [hR.ψ_zero]
    exact one_mem S
  add_mem' {v w} hv hw := by
    change ψ (v + w) ∈ S
    rw [hR.ψ_add]
    exact mul_mem hv hw
  neg_mem' {v} hv := by
    change ψ (-v) ∈ S
    have : -v = v := by
      ext i
      simp only [Pi.neg_apply]
      generalize v i = c
      fin_cases c <;> rfl
    rwa [this]

theorem eq_of_le_of_ne_bot (hR : RadicalData ε L U Q P a ψ p) {S : Subgroup G} (hSQ : S ≤ Q)
    (hSP : ∀ x ∈ P, ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hne : S ≠ ⊥) : S = Q := by
  obtain ⟨⟨s, hs⟩, hs1⟩ := (ne_bot_iff_exists_ne_one.1 hne)
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨v₀, rfl⟩ := hR.mem_ψ s (hSQ hs)
  have hv₀ : v₀ ≠ 0 := fun h => hs1' (by rw [h, hR.ψ_zero])
  have htype : ∀ z < 64, (z = 0 ∨ qfB ε z = qfB ε (vecBits v₀)) → ψ (toVec 6 z) ∈ S := by
    intro z hz h
    rcases h with rfl | h
    · rw [show toVec 6 0 = 0 by rw [← vecBits_zero, toVec_vecBits], hR.ψ_zero]
      exact one_mem S
    by_cases hz0 : z = 0
    · subst hz0
      rw [show toVec 6 0 = 0 by rw [← vecBits_zero, toVec_vecBits], hR.ψ_zero]
      exact one_mem S
    have hw : toVec 6 z ≠ 0 := by
      intro h0
      apply hz0
      rw [← vecBits_toVec hz, h0, vecBits_zero]
    have hq : qfV ε v₀ = qfV ε (toVec 6 z) := by
      rw [qfV, qfV_toVec ε hz, h]
    obtain ⟨x, hx, hxw⟩ := hR.exists_lin_eq hv₀ hw hq
    rw [← hxw, hR.ψ_lin (hR.P_le_normalizer hx)]
    exact hSP x hx _ hs
  have hb : ∀ j : Fin 6, Pi.single j 1 ∈ vecSub hR S := by
    intro j
    obtain ⟨y, hy, h1, h2⟩ := span ε (qfB ε (vecBits v₀)) j j.isLt
    have hxy : 2 ^ (j : ℕ) ^^^ y < 64 := by
      have h2j : 2 ^ (j : ℕ) < 64 := by
        have := j.isLt
        calc 2 ^ (j : ℕ) < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) this
          _ = 64 := by norm_num
      exact Nat.xor_lt_two_pow (n := 6) (by simpa using h2j) (by simpa using hy)
    have e : (Pi.single j 1 : V6) = toVec 6 y + toVec 6 (2 ^ (j : ℕ) ^^^ y) := by
      rw [← toVec_xor, ← Nat.xor_assoc, Nat.xor_comm y, Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero, toVec_two_pow']
    change ψ (Pi.single j 1) ∈ S
    rw [e, hR.ψ_add]
    exact mul_mem (htype y hy h1) (htype _ hxy h2)
  refine le_antisymm hSQ (fun x hx => ?_)
  obtain ⟨v, rfl⟩ := hR.mem_ψ x hx
  change v ∈ vecSub hR S
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  generalize v j = c
  fin_cases c
  · show (Pi.single j (0 : ZMod 2) : V6) ∈ vecSub hR S
    rw [Pi.single_zero]
    exact (vecSub hR S).zero_mem
  · exact hb j

end Irred

@[expose] def cm (t w : G) : G := w * t * w⁻¹ * t⁻¹

section Cm

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}

theorem conj_cm (hS : Setup ε t L U Q P a ψ p) {w : G} : t * cm t w * t⁻¹ = (cm t w)⁻¹ := by
  have ht := hS.shape.inv_eq
  have h2 : t * t = 1 := hS.shape.mul_self
  have e : (cm t w)⁻¹ = t * w * t⁻¹ * w⁻¹ := by simp only [cm]; group
  rw [e, ht]
  calc t * cm t w * t = t * w * t * w⁻¹ * (t * t) := by simp only [cm, ht]; group
    _ = t * w * t * w⁻¹ := by rw [h2, mul_one]

theorem cm_conj (hS : Setup ε t L U Q P a ψ p) {x w : G} (hx : x ∈ P) :
    cm t (x * w * x⁻¹) = x * cm t w * x⁻¹ := by
  have h1 : t = x * t * x⁻¹ := by rw [hS.commute_of_mem_P hx, mul_inv_cancel_right]
  simp only [cm]
  conv_lhs => rw [h1]
  group

theorem cm_eq_sq {W : Subgroup G} (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) {w : G} (hw : w ∈ W) :
    cm t w = w * w := by
  have h := hinv w⁻¹ (inv_mem hw)
  rw [inv_inv] at h
  calc cm t w = w * (t * w⁻¹ * t⁻¹) := by simp only [cm]; group
    _ = w * w := by rw [h]

end Cm

structure Premises (t : G) (Q W : Subgroup G) : Prop where
  Q_le : Q ≤ W
  t_not_mem : t ∉ W
  card_eq : Nat.card W = 4096
  comm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  norm : ∀ n ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), ∀ w ∈ W, n * w * n⁻¹ ∈ W

namespace Premises

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  {W : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hW : Premises t Q W)
include hS hW

omit hS in
theorem t_conj_mem {w : G} (hw : w ∈ W) : t * w * t⁻¹ ∈ W :=
  hW.norm t (le_normalizer t_mem_sup) w hw

omit hS in
theorem cm_mem {w : G} (hw : w ∈ W) : cm t w ∈ W := by
  have := mul_mem hw (hW.t_conj_mem (inv_mem hw))
  simpa [cm, mul_assoc] using this

theorem mem_Q_of_commute {w : G} (hw : w ∈ W) (h : w * t = t * w) : w ∈ Q := by
  have hc : w ∈ centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 h, mem_centralizer_iff.2 fun q hq =>
      hW.comm q (hW.Q_le hq) w hw⟩
  rw [hS.shape.centralizer_eq] at hc
  obtain ⟨q, hq, rfl | rfl⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 hc
  · exact hq
  · exact absurd (by simpa using mul_mem (inv_mem (hW.Q_le hq)) hw) hW.t_not_mem

omit hS in
theorem cm_mul {x y : G} (hx : x ∈ W) (hy : y ∈ W) : cm t (x * y) = cm t x * cm t y := by
  have h1 := hW.comm _ (hW.cm_mem hy) _ (hW.t_conj_mem (inv_mem hx))
  simp only [cm] at *
  calc x * y * t * (x * y)⁻¹ * t⁻¹ = x * (y * t * y⁻¹ * t⁻¹) * (t * x⁻¹ * t⁻¹) := by group
    _ = x * (t * x⁻¹ * t⁻¹) * (y * t * y⁻¹ * t⁻¹) := by rw [mul_assoc x, h1, ← mul_assoc]
    _ = x * t * x⁻¹ * t⁻¹ * (y * t * y⁻¹ * t⁻¹) := by group

theorem cm_eq_one_iff {w : G} (hw : w ∈ W) : cm t w = 1 ↔ w ∈ Q := by
  constructor
  · intro h
    refine hW.mem_Q_of_commute hS hw ?_
    have : w * t * w⁻¹ = t := by rw [← mul_inv_eq_one]; exact h
    calc w * t = w * t * w⁻¹ * w := by group
      _ = t * w := by rw [this]
  · intro hq
    have := hS.shape.commute_of_mem (hS.rad.Q_le_L hq)
    simp only [cm]
    rw [this]
    group

theorem P_conj_mem {x w : G} (hx : x ∈ P) (hw : w ∈ W) : x * w * x⁻¹ ∈ W :=
  hW.norm x (hS.P_le_normalizer_E hx) w hw


end Premises

@[expose] def cmHom {t : G} {Q W : Subgroup G} (hW : Premises t Q W) : W →* G where
  toFun w := cm t w
  map_one' := by simp [cm]
  map_mul' x y := hW.cm_mul x.2 y.2

namespace Premises

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  {W : Subgroup G} (hS : Setup ε t L U Q P a ψ p) (hW : Premises t Q W)
include hS hW

omit hS in
theorem range_le : (cmHom hW).range ≤ W := by
  rintro _ ⟨w, rfl⟩
  exact hW.cm_mem w.2

theorem card_range [Finite G] : Nat.card (cmHom hW).range = 64 := by
  have hker : (cmHom hW).ker = Q.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hW.cm_eq_one_iff hS w.2
  have h := card_mul_index (cmHom hW).ker
  rw [index_ker, hker, hW.card_eq,
    Nat.card_congr (subgroupOfEquivOfLe hW.Q_le).toEquiv, hS.rad.card_Q] at h
  omega

theorem range_eq [Finite G] : (cmHom hW).range = Q := by
  set R := (cmHom hW).range
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    hW.comm x (hW.range_le hx) y (hW.range_le hy)
  have hle : om R 2 ≤ Q := by
    intro x hx
    obtain ⟨hxR, hx2⟩ := (mem_om hRc).1 hx
    obtain ⟨w, rfl⟩ := hxR
    refine hW.mem_Q_of_commute hS (hW.cm_mem w.2) ?_
    have h1 := conj_cm hS (w := (w : G))
    have h2 : (cm t w)⁻¹ = cm t w := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
    rw [h2] at h1
    change cm t w * t = t * cm t w
    calc cm t w * t = t * cm t w * t⁻¹ * t := by rw [h1]
      _ = t * cm t w := by group
  have hP : ∀ x ∈ P, ∀ s ∈ om R 2, x * s * x⁻¹ ∈ om R 2 := by
    intro x hx s hs
    obtain ⟨hsR, hs2⟩ := (mem_om hRc).1 hs
    obtain ⟨w, rfl⟩ := hsR
    refine mem_om_of (MonoidHom.mem_range.2 ⟨⟨x * w * x⁻¹, hW.P_conj_mem hS hx w.2⟩,
      cm_conj hS hx⟩) ?_
    rw [conj_pow, hs2, mul_one, mul_inv_cancel]
  have hne : om R 2 ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2
      (by rw [hW.card_range hS]; norm_num)
    intro hbot
    have hxm : (x : G) ∈ om R 2 := mem_om_of x.2 (by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [hbot, mem_bot] at hxm
    have : x = 1 := Subtype.ext hxm
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hQ := eq_of_le_of_ne_bot hS.rad hle hP hne
  refine (eq_of_le_of_card_ge (hQ ▸ om_le R 2) ?_).symm
  rw [hW.card_range hS, hS.rad.card_Q]

theorem cm_mem_Q [Finite G] {w : G} (hw : w ∈ W) : cm t w ∈ Q := by
  rw [← hW.range_eq hS]
  exact ⟨⟨w, hw⟩, rfl⟩

theorem exists_cm_eq [Finite G] {q : G} (hq : q ∈ Q) :
    ∃ w ∈ W, cm t w = q := by
  rw [← hW.range_eq hS] at hq
  obtain ⟨w, rfl⟩ := hq
  exact ⟨w, w.2, rfl⟩

omit hS in
theorem cm_inv {w : G} (hw : w ∈ W) : cm t w⁻¹ = (cm t w)⁻¹ := by
  have h := hW.cm_mul hw (inv_mem hw)
  rw [mul_inv_cancel, show cm t 1 = 1 by simp [cm]] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem mul_self_mem_Q [Finite G] {w : G} (hw : w ∈ W) :
    w * w ∈ Q := by
  rw [← hW.cm_eq_one_iff hS (mul_mem hw hw), hW.cm_mul hw hw]
  exact hS.rad.Q_mul_self (hW.cm_mem_Q hS hw)

theorem mul_self_eq_of_cm_eq [Finite G] {w w' : G} (hw : w ∈ W) (hw' : w' ∈ W)
    (h : cm t w = cm t w') : w * w = w' * w' := by
  have hq : w⁻¹ * w' ∈ Q := by
    rw [← hW.cm_eq_one_iff hS (mul_mem (inv_mem hw) hw'), hW.cm_mul (inv_mem hw) hw',
      hW.cm_inv hw, h, inv_mul_cancel]
  obtain ⟨q, hq', rfl⟩ : ∃ q ∈ Q, w' = w * q := ⟨w⁻¹ * w', hq, by group⟩
  have hqw : q * w = w * q := hW.comm q (hW.Q_le hq') w hw
  calc w * w = w * w * (q * q) := by rw [hS.rad.Q_mul_self hq', mul_one]
    _ = w * (q * w) * q := by rw [hqw]; group
    _ = w * q * (w * q) := by group

theorem le_normalizer_E [Finite G] :
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
    exact mul_mem (mul_mem (mem_sup_left (hW.cm_mem_Q hS hw)) t_mem_sup)
      (mem_sup_left (hS.rad.ψ_mem v))

theorem normalizer_E_eq [Finite G] :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) = W ⊔ (P ⊔ zpowers t) := by
  set X : Subgroup G := P ⊔ zpowers t
  have hXle : X ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    sup_le hS.P_le_normalizer_E (zpowers_le.2 (le_normalizer t_mem_sup))
  have hle : W ⊔ X ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    sup_le (hW.le_normalizer_E hS) hXle
  have hXW : X ≤ normalizer (W : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun w hw => hW.norm x (hXle hx) w hw
  have hinf : X ⊓ W = Q := by
    refine le_antisymm (fun x hx => hW.mem_Q_of_commute hS hx.2 ?_) (le_inf ?_ hW.Q_le)
    · have hxC : x ∈ centralizer ({t} : Set G) := by
        refine (sup_le (hS.rad.P_le_L.trans hS.shape.le_centralizer) ?_) hx.1
        rw [zpowers_le]
        exact mem_centralizer_singleton_iff.2 rfl
      exact mem_centralizer_singleton_iff.1 hxC
    · exact (hS.rad.Q_le_U.trans hS.rad.U_le_P).trans le_sup_left
  have h1 := card_sup_mul_card_inf hXW
  rw [hinf, hS.rad.card_Q, hS.shape.card_sup hS.rad.P_le_L, hW.card_eq, sup_comm] at h1
  have h2 := hS.card_normalizer_E
  have h3 : Nat.card (Zset t Q ψ) ≤ 64 := by
    calc Nat.card (Zset t Q ψ) ≤ Nat.card V6 := Finite.card_subtype_le _
      _ = 64 := by rw [Nat.card_eq_fintype_card]; simp
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [h2]
  have : Nat.card (W ⊔ X : Subgroup G) = 64 * (2 * Nat.card P) := by
    have := h1
    omega
  rw [this]
  exact Nat.mul_le_mul_right _ h3

theorem sq_eq_one_or_inv [Finite G] (hE : EndF2 ε) :
    (∀ w ∈ W, w * w = 1) ∨ (∀ w ∈ W, t * w * t⁻¹ = w⁻¹) := by
  have hex : ∀ v : V6, ∃ w ∈ W, cm t w = ψ v := fun v => hW.exists_cm_eq hS (hS.rad.ψ_mem v)
  choose wv hwv hcm using hex
  set f : V6 → V6 := fun v => coord ψ (wv v * wv v) with hfdef
  have hf : ∀ v, ψ (f v) = wv v * wv v := fun v =>
    hS.rad.ψ_coord (hW.mul_self_mem_Q hS (hwv v))
  have hadd : ∀ v v', f (v + v') = f v + f v' := by
    intro v v'
    apply hS.rad.ψ_inj
    rw [hf, hS.rad.ψ_add, hf, hf]
    have h1 : cm t (wv (v + v')) = cm t (wv v * wv v') := by
      rw [hcm, hW.cm_mul (hwv v) (hwv v'), hcm, hcm, hS.rad.ψ_add]
    rw [hW.mul_self_eq_of_cm_eq hS (hwv _) (mul_mem (hwv v) (hwv v')) h1]
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
      rw [hcm, cm_conj hS hp, hcm, hS.rad.p_act]
    rw [hW.mul_self_eq_of_cm_eq hS (hwv _) (hW.P_conj_mem hS hp (hwv v)) h1]
    group
  have hv : ∀ w ∈ W, cm t w = cm t (wv (coord ψ (cm t w))) := fun w hw => by
    rw [hcm, hS.rad.ψ_coord (hW.cm_mem_Q hS hw)]
  rcases hE f hadd hequiv with h0 | hid
  · left
    intro w hw
    rw [hW.mul_self_eq_of_cm_eq hS hw (hwv _) (hv w hw), ← hf, h0, hS.rad.ψ_zero]
  · right
    intro w hw
    have hsq : w * w = cm t w := by
      rw [hW.mul_self_eq_of_cm_eq hS hw (hwv _) (hv w hw), ← hf, hid, ← hcm, ← hv w hw]
    have h3 : w * w = w * (t * w⁻¹ * t⁻¹) := by rw [hsq]; simp only [cm]; group
    have h2 : w = t * w⁻¹ * t⁻¹ := mul_left_cancel h3
    calc t * w * t⁻¹ = (t * w⁻¹ * t⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [← h2]

theorem level_two [Finite G]
    (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) : Level Q 2 W := by
  refine ⟨hW.comm, by rw [hW.card_eq]; norm_num, hW.Q_le, fun w hw h => ?_, fun w hw => ?_⟩
  · rw [← hW.cm_eq_one_iff hS hw, cm_eq_sq hinv hw, h]
  · have h := hS.rad.Q_mul_self (hW.cm_mem_Q hS hw)
    rw [cm_eq_sq hinv hw] at h
    rw [show 2 ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
    exact h

end Premises

end CFSG.EvenSmallLie.OmegaEight.Chain
