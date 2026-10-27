module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMon
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

theorem conj_theta0e_cases {g : G12} (hg : g ∈ gammaU) :
    g * theta0e * g⁻¹ = theta0e ∨ g * theta0e * g⁻¹ = theta0e⁻¹ := by
  rcases (mem_gammaU.1 hg).2 with h | h
  · left
    have : g * theta0e = theta0e * g := LinearEquiv.ext fun x => h x
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
  · right
    have h2 : g * theta0e = theta0e⁻¹ * g := by
      refine LinearEquiv.ext fun x => ?_
      show g (theta0 x) = theta0e⁻¹ (g x)
      rw [h x]
      rfl
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]

theorem commute_conj_of_commute {g z : G12} (hg : g ∈ gammaU)
    (hz : z * theta0e = theta0e * z) : (g * z * g⁻¹) * theta0e = theta0e * (g * z * g⁻¹) := by
  have hz' : Commute z theta0e := hz
  rcases conj_theta0e_cases hg with h | h
  · have h' : theta0e = g * theta0e * g⁻¹ := h.symm
    have : Commute (g * z * g⁻¹) (g * theta0e * g⁻¹) := by
      have e1 : g * z * g⁻¹ = (MulAut.conj g) z := rfl
      have e2 : g * theta0e * g⁻¹ = (MulAut.conj g) theta0e := rfl
      rw [e1, e2]
      exact hz'.map (MulAut.conj g).toMonoidHom
    rw [h] at this
    exact this.eq
  · have : Commute (g * z * g⁻¹) (g * theta0e * g⁻¹) := by
      have e1 : g * z * g⁻¹ = (MulAut.conj g) z := rfl
      have e2 : g * theta0e * g⁻¹ = (MulAut.conj g) theta0e := rfl
      rw [e1, e2]
      exact hz'.map (MulAut.conj g).toMonoidHom
    rw [h] at this
    exact (this.inv_right).eq

theorem conj_diagE_type {m : G12} (hm : m ∈ monGamma) {c : Fin 6 → ZMod 3} {S : Finset (Fin 6)}
    (hS : S.card = 3) {j e : ZMod 3} (he : e ≠ 0) (hc : ∀ i, c i = j + if i ∈ S then e else 0) :
    ∃ (c' : Fin 6 → ZMod 3) (S' : Finset (Fin 6)) (j' e' : ZMod 3), m * diagE c * m⁻¹ = diagE c' ∧
      S'.card = 3 ∧ e' ≠ 0 ∧ ∀ i, c' i = j' + if i ∈ S' then e' else 0 := by
  obtain ⟨cm, π, ε, hm'⟩ := hm
  have hS' : (S.map π.toEmbedding).card = 3 := by rw [Finset.card_map, hS]
  have hmem : ∀ i, i ∈ S.map π.toEmbedding ↔ π.symm i ∈ S := fun i => by
    simp [Finset.mem_map_equiv]
  rcases MonAux.zmod2_cases ε with rfl | rfl
  · rw [MonAux.frobPow_zero, mul_one] at hm'
    refine ⟨fun i => c (π.symm i), S.map π.toEmbedding, j, e, ?_, hS', he, fun i => ?_⟩
    · rw [hm', MonAux.conj_mon_zero]
    · show c (π.symm i) = _
      rw [hc]
      by_cases h : π.symm i ∈ S
      · rw [if_pos h, if_pos ((hmem i).2 h)]
      · rw [if_neg h, if_neg (fun h' => h ((hmem i).1 h'))]
  · rw [MonAux.frobPow_one] at hm'
    refine ⟨fun i => (-c) (π.symm i), S.map π.toEmbedding, -j, -e, ?_, hS', neg_ne_zero.2 he,
      fun i => ?_⟩
    · rw [hm', MonAux.conj_mon_one]
    · show (-c) (π.symm i) = _
      simp only [Pi.neg_apply, hc]
      by_cases h : π.symm i ∈ S
      · rw [if_pos h, if_pos ((hmem i).2 h)]; ring
      · rw [if_neg h, if_neg (fun h' => h ((hmem i).1 h'))]; ring

end CFSG.GF2Type.Smith1979.IdxFour
