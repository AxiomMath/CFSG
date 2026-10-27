module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.ActB
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Orbit

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace LocalSetting

variable {L : LocalSetting (G := G)}

theorem exists_order7_actB : ∃ b : L.B, orderOf (L.actB b) = 7 := by
  have h7dvd : 7 ∣ Nat.card L.actB.range := by
    rw [L.card_range_actB]; norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨φ, hφ⟩ := exists_prime_orderOf_dvd_card' 7 h7dvd
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 φ.2
  refine ⟨b, ?_⟩
  have hφ' : orderOf (φ : MulAut L.E) = 7 := (Subgroup.orderOf_coe φ).trans hφ
  rw [hb, hφ']

theorem conj_pow_eq_of_action {c : G} {b : L.B}
    (hc : ∀ e ∈ L.E, c * e * c⁻¹ = (b : G) * e * (b : G)⁻¹) (n : ℕ) {e : G}
    (he : e ∈ L.E) :
    c ^ n * e * (c ^ n)⁻¹ = (b : G) ^ n * e * ((b : G) ^ n)⁻¹ := by
  have hN : ∀ e ∈ L.E, (b : G) * e * (b : G)⁻¹ ∈ L.E := fun e he =>
    (mem_normalizer_iff.1 (L.B_le_normalizer_E b.2) e).1 he
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    have h1 : (b : G) * e * (b : G)⁻¹ ∈ L.E := hN e he
    calc c ^ (n + 1) * e * (c ^ (n + 1))⁻¹ = c ^ n * (c * e * c⁻¹) * (c ^ n)⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
      _ = c ^ n * ((b : G) * e * (b : G)⁻¹) * (c ^ n)⁻¹ := by rw [hc e he]
      _ = (b : G) ^ n * ((b : G) * e * (b : G)⁻¹) * ((b : G) ^ n)⁻¹ := ih h1
      _ = (b : G) ^ (n + 1) * e * ((b : G) ^ (n + 1))⁻¹ := by rw [pow_succ', mul_inv_rev]; group

@[expose] def IsSigma (σ : G) : Prop :=
  σ * L.z = L.z * σ ∧ (∃ a : ℕ, σ ^ 7 ^ a = 1) ∧
    ∃ b : L.B, orderOf (L.actB b) = 7 ∧
      ∀ e ∈ L.E, σ * e * σ⁻¹ = (b : G) * e * (b : G)⁻¹

namespace IsSigma

variable {σ : G} (h : L.IsSigma σ)

include h

theorem comm_z : σ * L.z = L.z * σ := h.1

theorem exists_pow_eq_one : ∃ a : ℕ, σ ^ 7 ^ a = 1 := h.2.1

theorem pow_seven_apply_E {e : G} (he : e ∈ L.E) : σ ^ 7 * e * (σ ^ 7)⁻¹ = e := by
  obtain ⟨b, hb7, hact⟩ := h.2.2
  rw [L.conj_pow_eq_of_action hact 7 he]
  have hb7' : (L.actB b) ^ 7 = 1 := by rw [← hb7]; exact pow_orderOf_eq_one _
  have h := congrArg (fun φ : MulAut L.E => (((φ ⟨e, he⟩ : L.E) : G))) hb7'
  simpa [L.actB_pow_apply b 7 ⟨e, he⟩] using h

theorem free {e : G} (he : e ∈ L.E) (h1 : e ≠ 1) : σ * e * σ⁻¹ ≠ e := by
  obtain ⟨b, hb7, hact⟩ := h.2.2
  have hfree := (J1Std.orbit_of_prime_order L.card_E (L.actB b) hb7).1
  rw [hact e he]
  intro hc
  have hx : (L.actB b) ⟨e, he⟩ = ⟨e, he⟩ := Subtype.ext (by simpa [L.actB_apply] using hc)
  exact hfree ⟨e, he⟩ (fun hh => h1 (congrArg Subtype.val hh)) hx

theorem trans {e e' : G} (he : e ∈ L.E) (he' : e' ∈ L.E) (h1 : e ≠ 1) (h1' : e' ≠ 1) :
    ∃ i : ℕ, σ ^ i * e * (σ ^ i)⁻¹ = e' := by
  obtain ⟨b, hb7, hact⟩ := h.2.2
  obtain ⟨i, hi⟩ := (J1Std.orbit_of_prime_order L.card_E (L.actB b) hb7).2
    ⟨e, he⟩ ⟨e', he'⟩ (fun h => h1 (congrArg Subtype.val h))
    (fun h => h1' (congrArg Subtype.val h))
  refine ⟨i, ?_⟩
  rw [L.conj_pow_eq_of_action hact i he]
  simpa [L.actB_pow_apply b i ⟨e, he⟩] using congrArg Subtype.val hi

theorem pow_comm_z (i : ℕ) : σ ^ i * L.z = L.z * σ ^ i := (Commute.pow_left h.1 i)

end IsSigma

theorem exists_isSigma_of_action {c : G} (hcz : c * L.z = L.z * c) {b : L.B}
    (hb7 : orderOf (L.actB b) = 7)
    (hc : ∀ e ∈ L.E, c * e * c⁻¹ = (b : G) * e * (b : G)⁻¹) :
    ∃ k : ℕ, L.IsSigma (c ^ k) := by
  obtain ⟨k, hk, a, ha⟩ := exists_pow_seven_part c
  refine ⟨k, Commute.pow_left hcz k, ⟨a, ha⟩, b, hb7, fun e he => ?_⟩
  rw [L.conj_pow_eq_of_action hc k he]
  have hb7' : (L.actB b) ^ 7 = 1 := by rw [← hb7]; exact pow_orderOf_eq_one _
  have hbk : (L.actB b) ^ k = L.actB b := by
    rw [← Nat.div_add_mod k 7, hk, pow_add, pow_mul, hb7', one_pow, one_mul, pow_one]
  have h := congrArg (fun φ : MulAut L.E => (((φ ⟨e, he⟩ : L.E) : G))) hbk
  simpa [L.actB_pow_apply b k ⟨e, he⟩, L.actB_apply] using h

end LocalSetting

end CFSG.EvenSporadicStandard.ReeStd
