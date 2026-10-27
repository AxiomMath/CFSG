module

public import CFSG.GH74.GLS.C3.Layer1.P34Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin
open scoped Pointwise

variable {X : Type} [Group X] {T P Q : Subgroup X} {x z f h : X}

namespace Cfg34

variable (c : Cfg34 X T P Q x z f h)
include c

theorem Q_le_normalizer_P : Q ≤ normalizer (P : Set X) := fun q hq => by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact c.P_norm q (c.Q_le hq) a ha
  · intro ha
    have := c.P_norm q⁻¹ (T.inv_mem (c.Q_le hq)) _ ha
    simpa [mul_assoc] using this

theorem coe_R : ((P ⊔ Q : Subgroup X) : Set X) = (P : Set X) * (Q : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left P Q c.Q_le_normalizer_P

theorem f_le_normalizer_R : zpowers f ≤ normalizer ((P ⊔ Q : Subgroup X) : Set X) := by
  rw [zpowers_le, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact c.R_norm f c.f_mem y hy
  · intro hy
    have := c.R_norm f⁻¹ (T.inv_mem c.f_mem) _ hy
    simpa [mul_assoc] using this

theorem coe_Rf : (((P ⊔ Q) ⊔ zpowers f : Subgroup X) : Set X) =
    ((P ⊔ Q : Subgroup X) : Set X) * (zpowers f : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left (P ⊔ Q) (zpowers f) c.f_le_normalizer_R

theorem T0_le_M : T0 T ≤ ((P ⊔ Q) ⊔ zpowers f) ⊔ zpowers h := by
  refine (closure_le _).2 ?_
  rintro t ⟨htT, ht2⟩
  rcases c.kf_invol t htT ht2 with h1 | ⟨r, hr, rfl⟩
  · exact mem_sup_left h1
  · exact (((P ⊔ Q) ⊔ zpowers f) ⊔ zpowers h).mul_mem (mem_sup_left (mem_sup_left hr))
      (mem_sup_right (mem_zpowers h))

theorem x_le_normalizer_P : zpowers x ≤ normalizer (P : Set X) := by
  rw [zpowers_le, Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact c.P_norm x c.x_mem a ha
  · intro ha
    have := c.P_norm x⁻¹ (T.inv_mem c.x_mem) _ ha
    simpa [mul_assoc] using this

theorem coe_Px : ((P ⊔ zpowers x : Subgroup X) : Set X) = (P : Set X) * (zpowers x : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left P (zpowers x) c.x_le_normalizer_P

theorem coe_Qz : ((Q ⊔ zpowers z : Subgroup X) : Set X) = (Q : Set X) * (zpowers z : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left Q (zpowers z) (fun w hw => by
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hw
    exact (normalizer (Q : Set X)).zpow_mem (c.T_le_normalizer_Q c.z_mem_T) l)

section Fin

variable [Finite X]

theorem card_R : Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q := by
  have h1 : Nat.card ↥(((P ⊔ Q : Subgroup X)) : Set X) = Nat.card ↥(P ⊔ Q) := rfl
  rw [← h1, c.coe_R]
  exact card_mul_of_inf_bot c.PQ_inf

theorem h_mem_normalizer_Rf :
    h ∈ normalizer ((((P ⊔ Q) ⊔ zpowers f : Subgroup X)) : Set X) := by
  have hhf : h⁻¹ * f * h ∈ (P ⊔ Q) ⊔ zpowers f := by
    have hκ : h⁻¹ * f * h⁻¹⁻¹ * f⁻¹ ∈ P ⊔ Q := c.kf_abelian h⁻¹ (T.inv_mem c.h_mem) f c.f_mem
    have e : h⁻¹ * f * h = (h⁻¹ * f * h⁻¹⁻¹ * f⁻¹) * f := by group
    rw [e]
    exact ((P ⊔ Q) ⊔ zpowers f).mul_mem (mem_sup_left hκ) (mem_sup_right (mem_zpowers f))
  refine mem_normalizer_of_conj_le (fun y hy => ?_)
  have hy' : y ∈ ((((P ⊔ Q) ⊔ zpowers f : Subgroup X)) : Set X) := hy
  rw [c.coe_Rf] at hy'
  obtain ⟨r, hr, ff, hff, rfl⟩ := hy'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hff
  have hz := conj_zpow (a := h⁻¹) (b := f) (i := k)
  simp only [inv_inv] at hz
  have e : h⁻¹ * (r * f ^ k) * h = (h⁻¹ * r * h) * (h⁻¹ * f * h) ^ k := by
    rw [hz]; group
  rw [e]
  have hr' : h⁻¹ * r * h ∈ P ⊔ Q := by
    have := c.R_norm h⁻¹ (T.inv_mem c.h_mem) r hr
    simpa using this
  exact ((P ⊔ Q) ⊔ zpowers f).mul_mem (mem_sup_left hr')
    (((P ⊔ Q) ⊔ zpowers f).zpow_mem hhf k)

theorem coe_M : (((((P ⊔ Q) ⊔ zpowers f) ⊔ zpowers h : Subgroup X)) : Set X) =
    ((((P ⊔ Q) ⊔ zpowers f : Subgroup X)) : Set X) * (zpowers h : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ (zpowers h)
    (zpowers_le.2 c.h_mem_normalizer_Rf)

theorem card_M_le : Nat.card ↥(((P ⊔ Q) ⊔ zpowers f) ⊔ zpowers h) ≤ 4 * Nat.card ↥(P ⊔ Q) := by
  have h1 : Nat.card ↥(((((P ⊔ Q) ⊔ zpowers f) ⊔ zpowers h : Subgroup X)) : Set X) ≤
      Nat.card ↥((((P ⊔ Q) ⊔ zpowers f : Subgroup X)) : Set X) * Nat.card ↥(zpowers h : Set X) := by
    rw [c.coe_M]; exact Set.natCard_mul_le
  have h2 : Nat.card ↥((((P ⊔ Q) ⊔ zpowers f : Subgroup X)) : Set X) ≤
      Nat.card ↥((P ⊔ Q : Subgroup X) : Set X) * Nat.card ↥(zpowers f : Set X) := by
    rw [c.coe_Rf]; exact Set.natCard_mul_le
  have hf : Nat.card ↥(zpowers f : Set X) = 2 := by
    have := Nat.card_zpowers f
    rw [c.f_order] at this
    exact this
  have hh : Nat.card ↥(zpowers h : Set X) ≤ 2 := by
    have h3 : Nat.card ↥(zpowers h) = orderOf h := Nat.card_zpowers h
    have h4 : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact c.h_sq)
    have : Nat.card ↥(zpowers h : Set X) = orderOf h := h3
    rw [this]
    exact Nat.le_of_dvd (by norm_num) h4
  have hR : Nat.card ↥((P ⊔ Q : Subgroup X) : Set X) = Nat.card ↥(P ⊔ Q) := rfl
  calc Nat.card ↥(((P ⊔ Q) ⊔ zpowers f) ⊔ zpowers h)
      ≤ Nat.card ↥((((P ⊔ Q) ⊔ zpowers f : Subgroup X)) : Set X) * Nat.card ↥(zpowers h : Set X) := h1
    _ ≤ (Nat.card ↥((P ⊔ Q : Subgroup X) : Set X) * Nat.card ↥(zpowers f : Set X)) * 2 :=
        Nat.mul_le_mul h2 hh
    _ = 4 * Nat.card ↥(P ⊔ Q) := by rw [hf, hR]; ring

theorem card_T0_le : Nat.card ↥(T0 T) ≤ 4 * (Nat.card ↥P * Nat.card ↥Q) := by
  have h1 : Nat.card ↥(T0 T) ≤ Nat.card ↥(((P ⊔ Q) ⊔ zpowers f) ⊔ zpowers h) :=
    Subgroup.card_le_of_le c.T0_le_M
  rw [← c.card_R]
  exact h1.trans c.card_M_le

end Fin

end Cfg34

end CFSG.GH74.GLS.C3.Layer1.P34
