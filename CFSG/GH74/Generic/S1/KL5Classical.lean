module

public import CFSG.GH74.Generic.S1.KL5Matrix
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.Generic.S1

theorem kl5_false_of_classical (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {S : Type} [Group S] {t : StatedLieTag} {n p' f' : ℕ} (hp' : p' ≠ 2)
    (hS : StatedClassicalModel S t n p' f')
    (hdim : (t = .PSL ∧ n ≤ 4) ∨ (t = .PSU ∧ n ≤ 4) ∨ (t = .PSp ∧ n ≤ 2))
    {A B : Subgroup S} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAq : CFSG.IsQuasisimple ↥A) (hBq : CFSG.IsQuasisimple ↥B) {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSL 3 p f ∨
      StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSU 3 p f) : False := by
  obtain ⟨hadm, hrest⟩ := hS
  have hp : p'.Prime := hadm.1
  rcases hdim with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have h2 : (2 : K) ≠ 0 :=
      Ring.two_ne_zero (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp' hK)
    exact kl5_of_statedProj hGA (ι := Fin n) (by simpa using hn) h2 e hcomm hAq hBq hp2 hmodel
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have h2 : (2 : K) ≠ 0 :=
      Ring.two_ne_zero (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp'
        (f := f' * 2) (by rw [hK, ← pow_mul]))
    exact kl5_of_statedProj hGA (ι := Fin n) (by simpa using hn) h2 e hcomm hAq hBq hp2 hmodel
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
    have h2 : (2 : K) ≠ 0 :=
      Ring.two_ne_zero (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp' hK)
    exact kl5_of_statedProj hGA (ι := Fin n ⊕ Fin n) (by simp; omega) h2 e hcomm hAq hBq hp2 hmodel

end CFSG.GH74.Generic.S1
