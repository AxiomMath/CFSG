module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HU42
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2A8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Main

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M23Std

theorem noTen_of_noCommutingFive {E : Type} [Group E]
    (h : ∀ u y : E, u * u = 1 → u ≠ 1 → orderOf y = 5 → u * y ≠ y * u) (g : E) :
    orderOf g ≠ 10 := by
  intro hg
  have h10 : g ^ 10 = 1 := by simpa [hg] using pow_orderOf_eq_one g
  have hu1 : g ^ 5 ≠ 1 := by
    intro h5
    have := Nat.le_of_dvd (by norm_num) (hg ▸ orderOf_dvd_of_pow_eq_one h5)
    omega
  have hy : orderOf (g ^ 2) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  exact h (g ^ 5) (g ^ 2) (by rw [← pow_add]; exact h10) hu1 hy
    (Commute.pow_pow_self g 5 2).eq

variable {G : Type} [Group G] [Finite G] {z : G}

theorem prop21_a8 (hz : orderOf z = 2)
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (hG : Nat.card G ∣ gl8)
    (hA8 : Nonempty (egaLayer (G ⧸ fusionOddCore G) ≃* alternatingGroup (Fin 8))) :
    Nonempty (egaLayer G ≃* alternatingGroup (Fin 8)) ∧
      z ∉ egaLayer G ⊔ centralizer (egaLayer G : Set G) := by
  have hE := eData_A8 hA8
  obtain ⟨e⟩ := hA8
  have hbig : 1440 < Nat.card (egaLayer (G ⧸ fusionOddCore G)) := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_eight]
    norm_num
  have hsimp := isSimpleGroup_of_eData hE
  have hten := noTen_of_noCommutingFive (E := ↥(egaLayer (G ⧸ fusionOddCore G)))
    fun u y hu hu1 hy => P21H.no_commuting_five_alt8 ⟨e⟩ u y hu hu1 hy
  obtain ⟨U, -, ⟨eU⟩, hU, hzU⟩ := prop21_simple_case hz hC hG hE hbig
    fun u hu hu1 => noBadCent_of_noTen (by omega) hten u hu hu1
  subst hU
  exact ⟨⟨eU.trans e⟩, hzU⟩

theorem prop21_u42
    (hz : orderOf z = 2)
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (hG : Nat.card G ∣ gl8)
    (hU42 : LieModel (egaLayer (G ⧸ fusionOddCore G)) .PSU 4 2 1) :
    LieModel (egaLayer G) .PSU 4 2 1 ∧
      z ∉ egaLayer G ⊔ centralizer (egaLayer G : Set G) := by
  have hE := eData_U42 hU42
  have hc := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU42
  have hbig : 1440 < Nat.card (egaLayer (G ⧸ fusionOddCore G)) := by
    rw [card_of_statedClassicalModel_psu_four_two hc]
    norm_num
  have hsimp := isSimpleGroup_of_eData hE
  have hten := noTen_of_noCommutingFive (E := ↥(egaLayer (G ⧸ fusionOddCore G)))
    fun u y hu hu1 hy => P21H.no_commuting_five_u42 hU42 u y hu hu1 hy
  obtain ⟨U, -, ⟨eU⟩, hU, hzU⟩ := prop21_simple_case hz hC hG hE hbig
    fun u hu hu1 => noBadCent_of_noTen (by omega) hten u hu hu1
  subst hU
  exact ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eU.symm hU42, hzU⟩

end CFSG.EvenSporadicStandard.M22Std
