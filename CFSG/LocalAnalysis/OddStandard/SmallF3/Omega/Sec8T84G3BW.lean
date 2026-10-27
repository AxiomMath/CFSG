module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AB
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BEz
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BIn

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G}
  {E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84g3b_cent_W (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4)
    (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) {y : G}
    (hy : y ∈ sec8t84g_Q E (F1 ⊔ F2))
    (hy3 : ∃ k : ℕ, y ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2))) :
    (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G) = ⊥ ∨
      (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G) = V1 ⊔ F1 ∨
      (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G) = V2 ⊔ F2 ∨
      (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G) = E ⊔ (F1 ⊔ F2) := by
  obtain ⟨H1, S1⟩ := sec8t84g3b_side1 h
  obtain ⟨H2, S2⟩ := sec8t84g3b_side2 h
  have hW1 : E ⊔ (F1 ⊔ F2) = (V1 ⊔ F1) ⊔ (V2 ⊔ F2) := sec8t84g3a_W_eq h.D
  have hW2 : E ⊔ (F1 ⊔ F2) = (V2 ⊔ F2) ⊔ (V1 ⊔ F1) := hW1.trans (sup_comm _ _)
  obtain ⟨k, hk⟩ := hy3
  have hodd : Odd (orderOf y) := sec8t84g3b_odd_of_pow (Odd.pow (by decide : Odd 3)) hk
  have hsup : (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G) =
      ((V1 ⊔ F1) ⊓ centralizer ({y} : Set G)) ⊔ ((V2 ⊔ F2) ⊓ centralizer ({y} : Set G)) := by
    rw [hW1]
    exact sec8t84g3b_cent_sup (sec8t84g3a_U_inf h.D)
      (fun u hu u' hu' => S1.UU'_comm u hu u' hu') (S1.conj_U_of_odd hW1 hy hodd)
      (S2.conj_U_of_odd hW2 hy hodd)
  rw [hsup]
  rcases S1.cent_U_dich hP hS4 hW1 hy hk with h1 | h1 <;>
    rcases S2.cent_U_dich hP hS4 hW2 hy hk with h2 | h2 <;> rw [h1, h2]
  · exact Or.inl (bot_sup_eq _)
  · exact Or.inr (Or.inr (Or.inl (bot_sup_eq _)))
  · exact Or.inr (Or.inl (sup_bot_eq _))
  · exact Or.inr (Or.inr (Or.inr hW1.symm))

theorem sec8t84g3b_exists_U (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4)
    (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) :
    (∃ y ∈ sec8t84g_Q E (F1 ⊔ F2), y ^ 3 ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) ∧
        (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G) = V2 ⊔ F2) ∧
      ∃ y ∈ sec8t84g_Q E (F1 ⊔ F2), y ^ 3 ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) ∧
        (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({y} : Set G) = V1 ⊔ F1 := by
  obtain ⟨H1, S1⟩ := sec8t84g3b_side1 h
  obtain ⟨H2, S2⟩ := sec8t84g3b_side2 h
  have hW1 : E ⊔ (F1 ⊔ F2) = (V1 ⊔ F1) ⊔ (V2 ⊔ F2) := sec8t84g3a_W_eq h.D
  have hW2 : E ⊔ (F1 ⊔ F2) = (V2 ⊔ F2) ⊔ (V1 ⊔ F1) := hW1.trans (sup_comm _ _)
  have hinf := sec8t84g3a_U_inf h.D
  exact ⟨S1.exists_cent_eq hP hS4 hW1 hinf, S2.exists_cent_eq hP hS4 hW2 (by rwa [inf_comm])⟩

end CFSG.OddStandard.SmallF3.Omega
