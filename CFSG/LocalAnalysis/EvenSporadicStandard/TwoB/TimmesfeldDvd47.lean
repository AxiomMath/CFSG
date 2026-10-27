module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.TimmesfeldReduction
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.LargeExtraspecial.Bridge Matrix
open scoped MatrixGroups

theorem not_dvd_47_prod_two : ¬ 47 ∣ ∏ i : Fin 14, (2 ^ 14 - 2 ^ (i : ℕ)) := by decide

theorem not_dvd_47_prod_four : ¬ 47 ∣ ∏ i : Fin 14, (4 ^ 14 - 4 ^ (i : ℕ)) := by decide

theorem not_dvd_47_card_psl : ¬ 47 ∣ Nat.card PSL(12 + 2, ZMod 2) := by
  intro h
  have h1 : Nat.card PSL(12 + 2, ZMod 2) ∣ Nat.card (SpecialLinearGroup (Fin 14) (ZMod 2)) :=
    Subgroup.card_quotient_dvd_card _
  have h2 := Matrix.card_SL_field (𝔽 := ZMod 2) 14
  rw [ZMod.card] at h2
  refine not_dvd_47_prod_two ?_
  have h3 := h.trans h1
  rw [h2] at h3
  simpa using h3

theorem not_dvd_47_card_psu : ¬ 47 ∣ Nat.card (timmesfeldPSU (12 + 2)) := by
  intro h
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h1 : Nat.card (timmesfeldPSU (12 + 2)) ∣
      Nat.card (ProjGenLinGroup (Fin (12 + 2)) (GaloisField 2 2)) :=
    Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (ProjGenLinGroup (Fin (12 + 2)) (GaloisField 2 2)) ∣
      Nat.card (GL (Fin (12 + 2)) (GaloisField 2 2)) :=
    Subgroup.card_quotient_dvd_card (Subgroup.center (GL (Fin (12 + 2)) (GaloisField 2 2)))
  have h3 := Matrix.card_GL_field (𝔽 := GaloisField 2 2) (12 + 2)
  rw [hq] at h3
  refine not_dvd_47_prod_four ?_
  have h4 := (h.trans h1).trans h2
  rw [h3] at h4
  exact h4

theorem not_dvd_47_card_alt2 {G : Type} [Group G]
    (h : Nonempty (G ≃* PSL(12 + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (12 + 2))) :
    ¬ 47 ∣ Nat.card G := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_47_card_psl
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_47_card_psu

@[expose] def Timmesfeld78Co1Dvd47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), 47 ∣ Nat.card G → orderOf z = 2 →
    CFSG.IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))) →
    Nat.card (CFSG.pCore 2 ↥(centralizer ({z} : Set G))) = 2 ^ 25 →
    centralizer ((CFSG.pCore 2 ↥(centralizer ({z} : Set G)) : Subgroup ↥(centralizer ({z} : Set G)))
      : Set ↥(centralizer ({z} : Set G))) ≤ CFSG.pCore 2 ↥(centralizer ({z} : Set G)) →
    (∃ S : Subgroup (↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G))),
      Nonempty (S ≃* Carrier .Co2)) →
    Nonempty (↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G)) ≃*
      Carrier .Co1)

theorem timmesfeld78Co1Dvd47_of_mainStatement (hM : MainStatement) :
    Timmesfeld78Co1Dvd47 := by
  intro G _ _ _ z h47 hz hext hcard hcen hCo2
  exact nonempty_quotient_co1_of_mainStatement hM z hz hext hcard hcen hCo2
    (fun h => not_dvd_47_card_alt2 h h47)

end CFSG.EvenSporadicStandard.TwoB
