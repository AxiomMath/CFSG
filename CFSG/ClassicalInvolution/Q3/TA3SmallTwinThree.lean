module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinFrameB
public import CFSG.GH74.Generic.Front.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open scoped MatrixGroups commutatorElement

variable {Y : Type} [Group Y]

structure Frame3 (L : Subgroup Y) (F' : Type) [Field F'] (x t : Y) (J₂ J₄ : Subgroup Y) : Prop
    extends Frame L F' x t J₂ J₄ where
  card : Nat.card F' = 3
  central : ∀ g : Y, g * x = x * g
  sq_mem : ∀ n ∈ L, n * t = t * n → n * n = t → ∃ b ∈ J₂, n = b ∨ n = x * t * b
  cent_mem : ∀ g ∈ L, g * t = t * g → (∀ b ∈ J₂, b * b = t → g * b = b * g) →
    ∃ j ∈ J₄, g = j ∨ g = t * j

variable {L : Subgroup Y} {F' : Type} [Field F'] {x t : Y} {J₂ J₄ : Subgroup Y}
  {R : Subgroup Y} {S : Sylow 2 R}

theorem mem_cent {g : Y} : g ∈ Subgroup.centralizer ({t} : Set Y) ↔ g * t = t * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem Frame3.x_sq (hfr : Frame3 L F' x t J₂ J₄) (ht : t * t = 1) : x * x = 1 := by
  have h := pow_orderOf_eq_one (x * t)
  rw [hfr.orderOf_xt, sq] at h
  have e : x * x = x * t * (x * t) := by
    calc x * x = x * x * (t * t) := by rw [ht, mul_one]
      _ = x * (t * x) * t := by rw [hfr.central t]; group
      _ = x * t * (x * t) := by group
  rw [e, h]

theorem t_mul_self [Finite Y] (hD : TightDatum R S t) : t * t = 1 := by
  rw [← sq, ← hD.order, pow_orderOf_eq_one]

theorem Frame3.oddCore_inf_eq_one [Finite Y] [Finite F'] (hfr : Frame3 L F' x t J₂ J₄)
    (hLn : L.Normal) (hD : TightDatum R S t) {o : Y} (ho : o ∈ oddCoreImg R ⊓ L) : o = 1 := by
  have hodd : Odd (Nat.card F') := by rw [hfr.card]; decide
  have hNodd : Odd (Nat.card ↥(oddCoreImg R ⊓ L)) :=
    (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hN := hfr.toFrame.comm_of_odd hodd (by rw [hfr.card]) inf_le_right
    (fun n hn => hD.cent (oddCoreImg_le R hn.1)) hNodd (fun g hg hgt n hn =>
      ⟨datum_conj_mem_oddCoreImg hD (mem_cent.mpr hgt) hn.1, hLn.conj_mem _ hn.2 g⟩)
  have hot : o * t = t * o := mem_cent.mp (hD.cent (oddCoreImg_le R ho.1))
  obtain ⟨j, hj, hoj⟩ := hfr.cent_mem o ho.2 hot fun b hb _ => hN.1 o ho b hb
  have ht2 := t_mul_self hD
  have hjc : ∀ w ∈ J₄, w * j = j * w := by
    intro w hw
    rcases hoj with rfl | rfl
    · exact (hN.2 _ ho w hw).symm
    · have h1 := hN.2 _ ho w hw
      have h2 : w * t = t * w := mem_cent.mp (hfr.toFrame.cent₄ hw)
      have : t * (w * j) = t * (j * w) := by
        rw [← mul_assoc, ← h2, mul_assoc, ← h1, mul_assoc]
      exact mul_left_cancel this
  obtain ⟨e₄⟩ := hfr.equiv₄
  have hsq : o * o = 1 := by
    have hx2 := hfr.x_sq ht2
    rcases eq_one_or_of_central hodd e₄ hfr.mem₄ hfr.orderOf_xt hj hjc with rfl | rfl <;>
      rcases hoj with rfl | rfl
    · rw [mul_one]
    · rw [mul_one, ht2]
    · rw [← sq, ← hfr.orderOf_xt, pow_orderOf_eq_one]
    · have e : t * (x * t) = x := by
        rw [← mul_assoc, hfr.central t, mul_assoc, ht2, mul_one]
      rw [e, hx2]
  have hord : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hsq])
  have hodd' : Odd (orderOf o) := (odd_natCard_oddCoreImg R).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ ho.1)
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd'
    exact absurd hodd' (by decide)

theorem Frame3.inter_cases [Finite Y] [Finite F'] (hfr : Frame3 L F' x t J₂ J₄) (hLn : L.Normal)
    (hD : TightDatum R S t) :
    (∃ n ∈ R, n ∈ L ∧ n * n = t) ∨ ∀ r ∈ R, r ∈ L → r = 1 ∨ r = t := by
  by_cases h : ∃ n ∈ R, n ∈ L ∧ n * n = t
  · exact Or.inl h
  right
  intro r hr hrL
  obtain ⟨m, ⟨e⟩⟩ := datum_quotient_equiv hD
  have : NeZero (2 ^ m) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hcard : Nat.card (R ⧸ oddCore R) = 2 ^ (m + 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  have hk := pow_card_eq_one' (G := R ⧸ oddCore R) (x := QuotientGroup.mk ⟨r, hr⟩)
  rw [hcard, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  have hr1 : r ^ 2 ^ (m + 2) = 1 :=
    hfr.oddCore_inf_eq_one hLn hD ⟨⟨_, hk, rfl⟩, L.pow_mem hrL _⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hr1)
  rcases j with _ | _ | j
  · left
    exact orderOf_eq_one_iff.mp (by rw [hj, pow_zero])
  · right
    exact hD.eq_of_orderOf_eq_two hr (by rw [hj, pow_one])
  · exfalso
    have hdvd : 2 ^ j ∣ orderOf r := by
      rw [hj]
      exact pow_dvd_pow 2 (by omega)
    have h4 : orderOf (r ^ 2 ^ j) = 4 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hj,
        show j + 1 + 1 = j + 2 by omega, pow_add, Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
      norm_num
    have h2 : orderOf (r ^ 2 ^ j * r ^ 2 ^ j) = 2 := by
      rw [← sq, orderOf_pow_of_dvd two_ne_zero (by rw [h4]; norm_num), h4]
    exact h ⟨r ^ 2 ^ j, R.pow_mem hr _, L.pow_mem hrL _,
      hD.eq_of_orderOf_eq_two (R.mul_mem (R.pow_mem hr _) (R.pow_mem hr _)) h2⟩

theorem comm_of_inter [Finite Y] (hD : TightDatum R S t) (hLn : L.Normal) {J : Subgroup Y}
    (hJL : J ≤ L) (hJt : J ≤ Subgroup.centralizer ({t} : Set Y))
    (hJ : GH74.Generic.OddGenerated J) (hRL : ∀ r ∈ R, r ∈ L → r = 1 ∨ r = t) :
    ∀ r ∈ R, ∀ j ∈ J, r * j = j * r := by
  intro r hr
  have ht2 := t_mul_self hD
  have hgen : ∀ g ∈ J, Odd (orderOf g) → g * r = r * g := by
    intro g hg hodd
    have hgt : g * t = t * g := mem_cent.mp (hJt hg)
    have hc : r * g * r⁻¹ * g⁻¹ ∈ R := by
      rw [mul_assoc, mul_assoc]
      refine R.mul_mem hr ?_
      rw [← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer (hJt hg)) _).mp (R.inv_mem hr)
    have hcL : r * g * r⁻¹ * g⁻¹ ∈ L :=
      L.mul_mem (hLn.conj_mem _ (hJL hg) r) (L.inv_mem (hJL hg))
    rcases hRL _ hc hcL with h | h
    · have : r * g * r⁻¹ = g := by rw [← mul_inv_eq_one, h]
      calc g * r = r * g * r⁻¹ * r := by rw [this]
        _ = r * g := by group
    · exfalso
      have h1 : r * g * r⁻¹ = t * g := by rw [← h]; group
      have h2 : r * g ^ orderOf g * r⁻¹ = (t * g) ^ orderOf g := by
        rw [← h1, conj_pow]
      have hcomm : Commute t g := hgt.symm
      rw [pow_orderOf_eq_one, mul_one, mul_inv_cancel, hcomm.mul_pow, pow_orderOf_eq_one,
        mul_one] at h2
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, sq, ht2, one_pow, one_mul] at h2
      have := hD.order
      rw [← h2, orderOf_one] at this
      exact absurd this (by norm_num)
  have hle : J ≤ Subgroup.centralizer ({r} : Set Y) := by
    rw [← hJ, Subgroup.closure_le]
    rintro g ⟨hg, hodd⟩
    exact mem_cent.mpr (hgen g hg hodd)
  intro j hj
  exact (mem_cent.mp (hle hj)).symm

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
