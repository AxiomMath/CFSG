module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleLocal
public import CFSG.LargeExtraspecial.AS35WAlt

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

theorem card_centralizer_involution_alternatingGroup {n : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11)
    {w : alternatingGroup (Fin n)} (hw : orderOf w = 2) :
    Nat.card ↥(centralizer ({w} : Set (alternatingGroup (Fin n)))) * 2 = 8 * (n - 4).factorial ∨
      Nat.card ↥(centralizer ({w} : Set (alternatingGroup (Fin n)))) * 2 =
        384 * (n - 8).factorial := by
  rcases CFSG.LargeExtraspecial.AS35W.alt_inv_cases h8 h11 w hw with hc | hc
  · left
    rw [← card_centralizer_singleton_eq_of_isConj hc]
    exact CFSG.GH74.GLS.Layer3.card_centralizer_altX h8
  · right
    rw [← card_centralizer_singleton_eq_of_isConj hc]
    exact CFSG.GH74.GLS.Layer3.card_centralizer_altY h8

theorem AlmostSimpleLocal.false_of_mulEquiv_alternatingGroup {T : Type*} [Group T] {u : T}
    (h : AlmostSimpleLocal T u) {n : ℕ} (e : T ≃* alternatingGroup (Fin n)) (h8 : 8 ≤ n)
    (h11 : n ≤ 11) (hn : n ≠ 9) : False := by
  have hw : orderOf (e u) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h.orderOf_eq
  have hc := card_centralizer_singleton_mulEquiv e u
  have h60 := h.sixty_dvd
  have hle : Nat.card ↥(centralizer ({u} : Set T)) ≤ 960 :=
    Nat.le_of_dvd (by norm_num) h.card_dvd
  rw [← hc] at h60 hle
  have h1 := card_centralizer_involution_alternatingGroup h8 h11 hw
  generalize Nat.card ↥(centralizer ({e u} : Set (alternatingGroup (Fin n)))) = c at h60 hle h1
  clear hw hc h e
  rcases h1 with h1 | h1 <;>
    · interval_cases n <;> simp [Nat.factorial] at h1 <;> omega

end CFSG.EvenSporadicStandard.TwoHS.GH312
