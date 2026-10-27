module

public import CFSG.ClassicalInvolution.Asc77.AscIHSL2
public import CFSG.ClassicalInvolution.AschTight.S1911F0a
public import CFSG.ClassicalInvolution.AschTight.S1911FusB
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {O : Subgroup G}

omit [Finite G] in
theorem exists_conj_eq_of_mul_mem_odd (hO : Odd (Nat.card O)) {s t : G} (hs : s * s = 1)
    (ht : t * t = 1) (hw : s⁻¹ * t ∈ O) : ∃ v ∈ O, v⁻¹ * s * v = t := by
  set w := s⁻¹ * t with hwdef
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have htw : t = s * w := by rw [hwdef]; group
  have hinv : s * w * s⁻¹ = w⁻¹ := by
    have h1 : s * w * (s * w) = 1 := by rw [← htw]; exact ht
    rw [hsi]
    calc s * w * s = (s * w * (s * w)) * w⁻¹ := by group
      _ = w⁻¹ := by rw [h1, one_mul]
  have hm : Odd (orderOf w) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hw)
  obtain ⟨k, hk⟩ := hm
  refine ⟨w ^ (k + 1), O.pow_mem hw _, ?_⟩
  have hvv : w ^ (k + 1) * w ^ (k + 1) = w := by
    rw [← pow_add, show k + 1 + (k + 1) = orderOf w + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hsv : s * w ^ (k + 1) * s⁻¹ = (w ^ (k + 1))⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  calc (w ^ (k + 1))⁻¹ * s * w ^ (k + 1) = s * (s⁻¹ * (w ^ (k + 1))⁻¹ * s) * w ^ (k + 1) := by
        group
    _ = s * (w ^ (k + 1) * w ^ (k + 1)) := by
        have h2 : s * (w ^ (k + 1))⁻¹ * s⁻¹ = w ^ (k + 1) := by
          calc s * (w ^ (k + 1))⁻¹ * s⁻¹ = (s * w ^ (k + 1) * s⁻¹)⁻¹ := by group
            _ = w ^ (k + 1) := by rw [hsv, inv_inv]
        have : s⁻¹ * (w ^ (k + 1))⁻¹ * s = w ^ (k + 1) := by
          rw [hsi] at h2 ⊢
          exact h2
        rw [this, mul_assoc]
    _ = t := by rw [hvv, htw]

omit [Finite G] in
theorem exists_pow_mul_self_eq_one (hO : Odd (Nat.card O)) {s x : G} (hs : s * s = 1)
    (hsO : s ∈ Subgroup.normalizer (O : Set G)) (hx : s⁻¹ * x ∈ O) :
    ∃ n : ℕ, x ^ n * x ^ n = 1 ∧ s⁻¹ * x ^ n ∈ O := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  set o := s⁻¹ * x with hodef
  have hxo : x = s * o := by rw [hodef]; group
  have hy : x * x ∈ O := by
    have : x * x = (s * o * s⁻¹) * o := by rw [hxo, hsi]; group
    rw [this]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp hsO o).mp hx) hx
  have hm : Odd (orderOf (x * x)) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hy)
  obtain ⟨k, hk⟩ := hm
  refine ⟨2 * k + 1, ?_, ?_⟩
  · rw [← (Commute.refl x).mul_pow, ← hk, pow_orderOf_eq_one]
  · have : s⁻¹ * x ^ (2 * k + 1) = o * (x * x) ^ k := by
      rw [pow_succ', pow_mul, hodef, ← pow_two]
      group
    rw [this]
    exact O.mul_mem hx (O.pow_mem hy k)

theorem exists_conj_commute_of_odd (hO : Odd (Nat.card O)) {s u : G} (hs : s * s = 1)
    (hu : u * u = 1) (hsO : s ∈ Subgroup.normalizer (O : Set G))
    (huO : u ∈ Subgroup.normalizer (O : Set G)) (hsu : u⁻¹ * (s * u * s⁻¹) ∈ O) :
    ∃ v ∈ O, s * (v * u * v⁻¹) = (v * u * v⁻¹) * s := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hk : s⁻¹ * (u * s * u⁻¹) ∈ O := by
    have e1 : s⁻¹ * (u * s * u⁻¹) = s * u * s * u := by rw [hsi, hui]; group
    have e2 : (u⁻¹ * (s * u * s⁻¹))⁻¹ = s * u⁻¹ * s⁻¹ * u := by group
    have hsu' := hsu
    rw [hui, hsi] at e2 hsu'
    rw [e1, ← e2]
    exact O.inv_mem hsu'
  obtain ⟨o, ho, hso⟩ := exists_mul_mem_centralizer_of_odd hO hu huO hk
  have hx : s⁻¹ * (s * o) ∈ O := by rw [inv_mul_cancel_left]; exact ho
  obtain ⟨n, htt, hto⟩ := exists_pow_mul_self_eq_one hO hs hsO hx
  have hcomm : u * (s * o) ^ n * u⁻¹ = (s * o) ^ n := by rw [← conj_pow, hso]
  obtain ⟨v, hv, hvt⟩ := exists_conj_eq_of_mul_mem_odd hO hs htt hto
  refine ⟨v, hv, ?_⟩
  have h1 : u * (v⁻¹ * s * v) = (v⁻¹ * s * v) * u := by
    rw [hvt]
    calc u * (s * o) ^ n = u * (s * o) ^ n * u⁻¹ * u := by group
      _ = (s * o) ^ n * u := by rw [hcomm]
  calc s * (v * u * v⁻¹) = v * ((v⁻¹ * s * v) * u) * v⁻¹ := by group
    _ = v * (u * (v⁻¹ * s * v)) * v⁻¹ := by rw [h1]
    _ = v * u * v⁻¹ * s := by group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
