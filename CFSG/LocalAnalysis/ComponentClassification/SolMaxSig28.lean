module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

namespace Sig28

variable {X : Type} [Group X]

theorem exists_le_sup_zpowers_of_klein [Finite X] {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) {e : X} (heE : e ∈ E)
    (he1 : e ≠ 1) : ∃ u ∈ E, E ≤ zpowers e ⊔ zpowers u := by
  classical
  obtain ⟨hE4, hEsq⟩ := card_sq_of_klein hE
  have he2 : orderOf e = 2 := orderOf_eq_prime (hEsq e heE) he1
  have hze : Nat.card (zpowers e) = 2 := by rw [Nat.card_zpowers, he2]
  obtain ⟨u, huE, hue⟩ : ∃ u ∈ E, u ∉ zpowers e := by
    by_contra h
    push Not at h
    have hle : E ≤ zpowers e := fun u hu => h u hu
    have := Subgroup.card_le_of_le hle
    omega
  refine ⟨u, huE, ?_⟩
  set B := zpowers e ⊔ zpowers u with hBdef
  have hBE : B ≤ E := sup_le (zpowers_le.mpr heE) (zpowers_le.mpr huE)
  have hdvd : Nat.card B ∣ 4 := hE4 ▸ Subgroup.card_dvd_of_le hBE
  have hzB : zpowers e ≤ B := le_sup_left
  have hne : zpowers e ≠ B := fun h => hue (h ▸ mem_sup_right (mem_zpowers u))
  have hlt : Nat.card (zpowers e) < Nat.card B := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hzB) fun h => hne ?_
    exact Subgroup.eq_of_le_of_card_ge hzB h.ge
  have h2B : 2 ∣ Nat.card B := hze ▸ Subgroup.card_dvd_of_le hzB
  have hB4 : Nat.card B = 4 := by
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    set c := Nat.card B with hc
    interval_cases c <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hBE (by rw [hB4, hE4])).ge

theorem goldschmidtGeneration_klein [Finite X] {E Y : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hEY : E ≤ normalizer (Y : Set X)) (hY : Odd (Nat.card Y)) (hYE : ⁅Y, E⁆ = Y) :
    Y ⊓ centralizer (E : Set X) =
      ⨆ (U₀ : Subgroup X) (_ : U₀ ≤ E) (_ : ∃ u ∈ E, E ≤ U₀ ⊔ zpowers u),
        Y ⊓ centralizer (E : Set X) ⊓ ⁅Y ⊓ centralizer (U₀ : Set X), E⁆ := by
  classical
  have hK4 : IsKleinFour ↥E := by
    obtain ⟨hE4, hE2⟩ := card_sq_of_klein hE
    exact isKleinFour_of_card hE4 fun g => Subtype.ext (by rw [← sq]; exact hE2 g g.2)
  have hF := FooteLit.inf_centralizer_eq_iSup_of_isKleinFour hK4 hEY hY hYE
  refine le_antisymm (hF.le.trans ?_) ?_
  · refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    obtain ⟨u, huE, hEu⟩ := exists_le_sup_zpowers_of_klein hE hw hw1
    have hCw : centralizer ((zpowers w : Subgroup X) : Set X) = centralizer ({w} : Set X) := by
      rw [zpowers_eq_closure, centralizer_closure]
    have hcY : ⁅Y ⊓ centralizer ({w} : Set X), E⁆ ≤ Y :=
      (commutator_mono inf_le_left le_rfl).trans hYE.le
    refine le_iSup₂_of_le (zpowers w) (zpowers_le.mpr hw) (le_iSup_of_le ⟨u, huE, hEu⟩ ?_)
    rw [hCw]
    exact le_inf (le_inf (inf_le_left.trans hcY) inf_le_right) inf_le_left
  · exact iSup₂_le fun U₀ _ => iSup_le fun _ => inf_le_left

end Sig28

end CFSG.ComponentClassification.SolMax
