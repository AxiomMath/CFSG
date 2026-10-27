module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltFin
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Swap

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Seven

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem sb_le_normalizer_alt7 (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hZ : center ↥J ≠ ⊥) (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) :
    Sb ≤ normalizer (J : Set A) := by
  by_contra hns
  have h := L1.swap_card_sq hfr hJ hZ hns
  rw [Nat.card_congr e.toEquiv, card_alt_fin (by norm_num)] at h
  revert h
  decide

theorem alt7_false_of_frame (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) : False := by
  by_cases hZ : center ↥J = ⊥
  · exact alt7_false_of_center_bot hfr hJ hZ e
  · exact alt7_false_of_normalizes hfr hJ (sb_le_normalizer_alt7 hfr hJ hZ e) e

end Seven

theorem cellAbs_Alt : CellAbs FAlt := by
  intro A _ _ zb Sb Vb J hfr hJ hnc hY
  obtain ⟨n, hn7, hn11, ⟨e⟩⟩ := hY
  by_cases h7 : n = 7
  · subst h7
    exact (alt7_false_of_frame hfr hJ e).elim
  by_cases h11 : n = 11
  · subst h11
    exact Or.inl (alt11_cover hfr hJ e)
  · exact (alt_mid_false hfr hJ hnc (by omega) (by omega) e).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
