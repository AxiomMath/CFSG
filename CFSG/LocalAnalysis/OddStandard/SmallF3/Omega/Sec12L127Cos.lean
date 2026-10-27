module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

theorem sec127_conj_coset {V O : Subgroup G} {u s : G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hOV : O ≤ normalizer (V : Set G))
    (hOodd : ∀ o ∈ O, Odd (orderOf o))
    (hOn : ∀ n ∈ normalizer (V : Set G), ∀ o ∈ O, n * o * n⁻¹ ∈ O)
    (hu : u ∈ normalizer (V : Set G)) (hu2 : u * u = 1)
    (hrange : ∀ d ∈ V, u * d = d * u → ∃ v ∈ V, u * v * u⁻¹ * v⁻¹ = d)
    (hc : u⁻¹ * s ∈ V ⊔ O) (hs2 : s * s = 1) : ∃ g : G, g⁻¹ * u * g = s := by
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left V O hOV
  have hc' : u⁻¹ * s ∈ ((V : Set G) * (O : Set G)) := by
    rw [← hcoe]
    exact hc
  obtain ⟨v, hv, o, ho, hvo⟩ := Set.mem_mul.mp hc'
  have hs : s = u * v * o := by
    calc s = u * (u⁻¹ * s) := by group
      _ = u * (v * o) := by rw [← hvo]
      _ = u * v * o := by group
  obtain ⟨w, hw⟩ : ∃ w : G, w = u * v := ⟨_, rfl⟩
  rw [← hw] at hs
  have hwN : w ∈ normalizer (V : Set G) := by
    rw [hw]
    exact (normalizer (V : Set G)).mul_mem hu (Subgroup.le_normalizer hv)
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hv2 : v * v = 1 := by
    have := hV.2 v hv
    rwa [pow_two] at this
  have hwwV : w * w ∈ V := by
    have h1 : w * w = (u * v * u⁻¹) * v := by
      rw [hw, huinv]
      group
    rw [h1]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hu v).mp hv) hv
  have ho' : w * o * w⁻¹ ∈ O := hOn w hwN o ho
  have hs2' : (w * o) * (w * o) = 1 := by
    rw [← hs]
    exact hs2
  have hwwO : w * w ∈ O := by
    have h0 : (w * o * w⁻¹) * (w * w) * o = 1 := by
      calc (w * o * w⁻¹) * (w * w) * o = (w * o) * (w * o) := by group
        _ = 1 := hs2'
    have h1 : w * w = (w * o * w⁻¹)⁻¹ * o⁻¹ := by
      calc w * w = (w * o * w⁻¹)⁻¹ * ((w * o * w⁻¹) * (w * w) * o) * o⁻¹ := by group
        _ = (w * o * w⁻¹)⁻¹ * 1 * o⁻¹ := by rw [h0]
        _ = (w * o * w⁻¹)⁻¹ * o⁻¹ := by rw [mul_one]
    rw [h1]
    exact O.mul_mem (O.inv_mem ho') (O.inv_mem ho)
  have hw2 : w * w = 1 := by
    have hsq : (w * w) * (w * w) = 1 := by
      have := hV.2 _ hwwV
      rwa [pow_two] at this
    have hod : orderOf (w * w) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have hodd := hOodd _ hwwO
    rcases (Nat.dvd_prime Nat.prime_two).mp hod with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hinv : w * o * w⁻¹ = o⁻¹ := by
    have h1 : (w * o * w⁻¹) * o = 1 := by
      calc (w * o * w⁻¹) * o = (w * o * w⁻¹) * (w * w) * o := by rw [hw2, mul_one]
        _ = (w * o) * (w * o) := by group
        _ = 1 := hs2'
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨j, hj⟩ := hOodd o ho
  obtain ⟨q, hqd⟩ : ∃ q : G, q = o ^ (j + 1) := ⟨_, rfl⟩
  have hq : q * q = o := by
    rw [hqd, ← pow_add]
    have : j + 1 + (j + 1) = orderOf o + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hwq : w * q * w⁻¹ = q⁻¹ := by
    rw [hqd, ← conj_pow, hinv, inv_pow]
  have hsq : s = q⁻¹ * w * q := by
    have hwq' : w * q = q⁻¹ * w := by
      calc w * q = (w * q * w⁻¹) * w := by group
        _ = q⁻¹ * w := by rw [hwq]
    calc s = w * o := hs
      _ = w * (q * q) := by rw [hq]
      _ = (w * q) * q := by group
      _ = (q⁻¹ * w) * q := by rw [hwq']
  have hcomm : u * v = v * u := by
    have h1 : (u * v * u⁻¹) * v = 1 := by
      calc (u * v * u⁻¹) * v = w * w := by rw [hw, huinv]; group
        _ = 1 := hw2
    have h2 : u * v * u⁻¹ = v⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    calc u * v = (u * v * u⁻¹) * u := by group
      _ = v⁻¹ * u := by rw [h2]
      _ = v * u := by rw [h3]
  obtain ⟨x, hx, hxc⟩ := hrange v hv hcomm
  have hxu : x⁻¹ * u * x = w := by
    have h1 : u * x * u⁻¹ = v * x := by
      calc u * x * u⁻¹ = (u * x * u⁻¹ * x⁻¹) * x := by group
        _ = v * x := by rw [hxc]
    have h2 : x⁻¹ * v * x = v := by
      have h3 := hV.comm (V.inv_mem hx) hv
      calc x⁻¹ * v * x = (v * x⁻¹) * x := by rw [h3]
        _ = v := by group
    calc x⁻¹ * u * x = x⁻¹ * (u * x * u⁻¹) * u := by group
      _ = x⁻¹ * (v * x) * u := by rw [h1]
      _ = (x⁻¹ * v * x) * u := by group
      _ = v * u := by rw [h2]
      _ = u * v := hcomm.symm
      _ = w := hw.symm
  refine ⟨x * q, ?_⟩
  calc (x * q)⁻¹ * u * (x * q) = q⁻¹ * (x⁻¹ * u * x) * q := by group
    _ = q⁻¹ * w * q := by rw [hxu]
    _ = s := hsq.symm

theorem sec127_odd_orderOf [Finite G] {X : Subgroup G} {x : G} (hx : x ∈ oddCoreIn X) :
    Odd (orderOf x) :=
  (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X).of_dvd_nat
    ((oddCoreIn X).orderOf_dvd_natCard hx)

theorem sec127_conj_coset_oddCore [Finite G] {V : Subgroup G} {u s : G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hu : u ∈ secN V) (hu2 : u * u = 1)
    (hrange : ∀ d ∈ V, u * d = d * u → ∃ v ∈ V, u * v * u⁻¹ * v⁻¹ = d)
    (hc : u⁻¹ * s ∈ V ⊔ oddCoreIn (secN V)) (hs2 : s * s = 1) :
    ∃ g : G, g⁻¹ * u * g = s :=
  sec127_conj_coset hV (CFSG.ClassicalInvolution.Balance.oddCoreIn_le (secN V))
    (fun _ ho => sec127_odd_orderOf ho)
    (fun _ hn _ ho => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hn ho) hu hu2 hrange
    hc hs2

end CFSG.OddStandard.SmallF3.Omega
