module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ComplementDefs
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

private theorem conj_mem_U {P E U : Subgroup G} {r : G} (h : NormSetting P E U r)
    {p u : G} (hp : p ∈ P) (hu : u ∈ U) : p * u * p⁻¹ ∈ U := by
  have huP : u ∈ P := h.U_le_E.trans h.E_le_P hu
  have h1 : p * u * p⁻¹ * u⁻¹ ∈ U := h.PP p hp u huP
  have h2 : p * u * p⁻¹ = (p * u * p⁻¹ * u⁻¹) * u := by group
  rw [h2]
  exact U.mul_mem h1 hu

private theorem pow2_conj_mem {P E U : Subgroup G} {r : G} (h : NormSetting P E U r)
    {p : G} (hp : p ∈ P) : r ^ 2 * p * (r ^ 2)⁻¹ ∈ P := by
  have h1 : r * (r * p * r⁻¹) * r⁻¹ ∈ P := h.r_P (r * p * r⁻¹) (h.r_P p hp)
  convert h1 using 1
  rw [pow_two]
  group

private theorem normOf_conj (r c x : G) :
    normOf r (c * x * c⁻¹) = c * normOf (c⁻¹ * r * c) x * c⁻¹ := by
  have hsq : (c⁻¹ * r * c) ^ 2 = c⁻¹ * r ^ 2 * c := by
    simp only [pow_two, mul_assoc, mul_inv_cancel_left]
  unfold normOf
  rw [hsq]
  group

private theorem normOf_mul_r_mem {P E U : Subgroup G} {r : G} (h : NormSetting P E U r)
    {q x : G} (hq : q ∈ P) (hx : x ∈ P) (hxU : normOf r x ∈ U) :
    normOf (q * r) x ∈ U := by
  have ha : r * x * r⁻¹ ∈ P := h.r_P x hx
  have hb : r ^ 2 * x * (r ^ 2)⁻¹ ∈ P := pow2_conj_mem h hx
  have hq' : q * (r * q * r⁻¹) ∈ P := P.mul_mem hq (h.r_P q hq)
  have hu1 : q * (r * x * r⁻¹) * q⁻¹ * (r * x * r⁻¹)⁻¹ ∈ U := h.PP q hq _ ha
  have hu2 : (q * (r * q * r⁻¹)) * (r ^ 2 * x * (r ^ 2)⁻¹) * (q * (r * q * r⁻¹))⁻¹ *
      (r ^ 2 * x * (r ^ 2)⁻¹)⁻¹ ∈ U := h.PP (q * (r * q * r⁻¹)) hq' _ hb
  have hU1 : x * (q * (r * x * r⁻¹) * q⁻¹ * (r * x * r⁻¹)⁻¹) * x⁻¹ ∈ U :=
    conj_mem_U h hx hu1
  have hU2 : (x * (r * x * r⁻¹)) *
      ((q * (r * q * r⁻¹)) * (r ^ 2 * x * (r ^ 2)⁻¹) * (q * (r * q * r⁻¹))⁻¹ *
        (r ^ 2 * x * (r ^ 2)⁻¹)⁻¹) * (x * (r * x * r⁻¹))⁻¹ ∈ U :=
    conj_mem_U h (P.mul_mem hx ha) hu2
  have hq2 : (q * r) ^ 2 = (q * (r * q * r⁻¹)) * r ^ 2 := by
    rw [pow_two]
    group
  have hfact : normOf (q * r) x =
      (x * (q * (r * x * r⁻¹) * q⁻¹ * (r * x * r⁻¹)⁻¹) * x⁻¹) *
      ((x * (r * x * r⁻¹)) *
        ((q * (r * q * r⁻¹)) * (r ^ 2 * x * (r ^ 2)⁻¹) * (q * (r * q * r⁻¹))⁻¹ *
          (r ^ 2 * x * (r ^ 2)⁻¹)⁻¹) * (x * (r * x * r⁻¹))⁻¹) *
      normOf r x := by
    unfold normOf
    rw [hq2]
    group
  rw [hfact]
  exact U.mul_mem (U.mul_mem hU1 hU2) hxU

private theorem normOf_mul_r2_mem {P E U : Subgroup G} {r : G} (h : NormSetting P E U r)
    {q x : G} (hq : q ∈ P) (hx : x ∈ P) (hxU : normOf r x ∈ U) :
    normOf (q * r ^ 2) x ∈ U := by
  have ha : r * x * r⁻¹ ∈ P := h.r_P x hx
  have hb : r ^ 2 * x * (r ^ 2)⁻¹ ∈ P := pow2_conj_mem h hx
  have hq'' : q * (r ^ 2 * q * (r ^ 2)⁻¹) ∈ P := P.mul_mem hq (pow2_conj_mem h hq)
  have hr2sq : r ^ 2 * r ^ 2 = r := by
    have hr4 : r ^ 4 = r := by rw [pow_succ, h.r_cube, one_mul]
    rw [← pow_add]
    simpa using hr4
  have hq2 : (q * r ^ 2) ^ 2 = (q * (r ^ 2 * q * (r ^ 2)⁻¹)) * r := by
    calc (q * r ^ 2) ^ 2 = q * (r ^ 2 * q * (r ^ 2)⁻¹) * (r ^ 2 * r ^ 2) := by
          rw [pow_two]; group
      _ = q * (r ^ 2 * q * (r ^ 2)⁻¹) * r := by rw [hr2sq]
  have hu1 : q * (r ^ 2 * x * (r ^ 2)⁻¹) * q⁻¹ * (r ^ 2 * x * (r ^ 2)⁻¹)⁻¹ ∈ U :=
    h.PP q hq _ hb
  have hu2 : (q * (r ^ 2 * q * (r ^ 2)⁻¹)) * (r * x * r⁻¹) *
      (q * (r ^ 2 * q * (r ^ 2)⁻¹))⁻¹ * (r * x * r⁻¹)⁻¹ ∈ U := h.PP _ hq'' _ ha
  have hU1 : x * (q * (r ^ 2 * x * (r ^ 2)⁻¹) * q⁻¹ * (r ^ 2 * x * (r ^ 2)⁻¹)⁻¹) * x⁻¹ ∈ U :=
    conj_mem_U h hx hu1
  have hU2 : (x * (r ^ 2 * x * (r ^ 2)⁻¹)) *
      ((q * (r ^ 2 * q * (r ^ 2)⁻¹)) * (r * x * r⁻¹) *
        (q * (r ^ 2 * q * (r ^ 2)⁻¹))⁻¹ * (r * x * r⁻¹)⁻¹) *
      (x * (r ^ 2 * x * (r ^ 2)⁻¹))⁻¹ ∈ U :=
    conj_mem_U h (P.mul_mem hx hb) hu2
  have hw : x * (r ^ 2 * x * (r ^ 2)⁻¹) * (r * x * r⁻¹) *
      (x * (r * x * r⁻¹) * (r ^ 2 * x * (r ^ 2)⁻¹))⁻¹ ∈ U := by
    have h1 : x * ((r ^ 2 * x * (r ^ 2)⁻¹) * (r * x * r⁻¹) * (r ^ 2 * x * (r ^ 2)⁻¹)⁻¹ *
        (r * x * r⁻¹)⁻¹) * x⁻¹ ∈ U := conj_mem_U h hx (h.PP _ hb _ ha)
    convert h1 using 1 <;> (rw [pow_two]; group)
  have hxba : x * (r ^ 2 * x * (r ^ 2)⁻¹) * (r * x * r⁻¹) ∈ U := by
    have hsplit : x * (r ^ 2 * x * (r ^ 2)⁻¹) * (r * x * r⁻¹) =
        (x * (r ^ 2 * x * (r ^ 2)⁻¹) * (r * x * r⁻¹) *
          (x * (r * x * r⁻¹) * (r ^ 2 * x * (r ^ 2)⁻¹))⁻¹) *
        normOf r x := by
      unfold normOf
      rw [pow_two]
      group
    rw [hsplit]
    exact U.mul_mem hw hxU
  have hfact : normOf (q * r ^ 2) x =
      (x * (q * (r ^ 2 * x * (r ^ 2)⁻¹) * q⁻¹ * (r ^ 2 * x * (r ^ 2)⁻¹)⁻¹) * x⁻¹) *
      ((x * (r ^ 2 * x * (r ^ 2)⁻¹)) *
        ((q * (r ^ 2 * q * (r ^ 2)⁻¹)) * (r * x * r⁻¹) *
          (q * (r ^ 2 * q * (r ^ 2)⁻¹))⁻¹ * (r * x * r⁻¹)⁻¹) *
        (x * (r ^ 2 * x * (r ^ 2)⁻¹))⁻¹) *
      (x * (r ^ 2 * x * (r ^ 2)⁻¹) * (r * x * r⁻¹)) := by
    unfold normOf
    rw [hq2]
    group
  rw [hfact]
  exact U.mul_mem (U.mul_mem hU1 hU2) hxba

theorem normKer_conj {P E U S : Subgroup G} {r : G} (h : NormSetting P E U r)
    (hS : ∀ x, x ∈ S ↔ x ∈ P ∧ normOf r x ∈ U) {c : G}
    (hcP : ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U)
    (hcr : ∃ q ∈ P, c⁻¹ * r * c = q * r ∨ c⁻¹ * r * c = q * r ^ 2) :
    ∀ x ∈ S, c * x * c⁻¹ ∈ S := by
  intro x hxS
  obtain ⟨hxP, hxU⟩ := (hS x).mp hxS
  obtain ⟨q, hqP, hq⟩ := hcr
  have hmem : normOf (c⁻¹ * r * c) x ∈ U := by
    rcases hq with hq | hq
    · rw [hq]
      exact normOf_mul_r_mem h hqP hxP hxU
    · rw [hq]
      exact normOf_mul_r2_mem h hqP hxP hxU
  rw [hS]
  exact ⟨hcP x hxP, by rw [normOf_conj]; exact hcU _ hmem⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
