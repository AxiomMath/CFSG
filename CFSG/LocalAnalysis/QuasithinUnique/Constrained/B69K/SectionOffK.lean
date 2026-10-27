module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs
public import CFSG.Quasithin.Background.FFC10B
public import CFSG.Quasithin.Background.FFC11B

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69K

open CFSG.Quasithin.B69

variable {V : Type} [CommGroup V] [Finite V]

theorem sectionOffenderK (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hH : B69.CompHypK X T M A L) {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) :
    ∃ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) ∧
      IsFFStarOffender (autSec (L ⊔ A) W (W ⊓ fixV L)) B := by
  obtain ⟨-, hmp, hO2, hFF, hns, hA, hL, hLA⟩ := hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hAoff : IsFFStarOffender X A := hA.1
  have hAel : IsElemAbelian2 A := hAoff.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAZ : ∀ b ∈ A, ∀ w ∈ W ⊓ fixV L, b w ∈ W ⊓ fixV L :=
    isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn)
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) := B1.le_stabSub_of_invariant hAZ
  have hMW : L ⊔ A ≤ stabSub W := sup_le hLW hAWs
  have hMZ : L ⊔ A ≤ stabSub (W ⊓ fixV L) := sup_le hLZ hAZs
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  have hmapA := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMZ (le_sup_right : A ≤ L ⊔ A)
  have hnA : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  have hineq := sec_card_le_of_offender hAoff hLq hAn hW hAW hnA
  have hA2 : IsA2 (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec A W (W ⊓ fixV L)) := by
    refine ⟨autSec_mono le_sup_right W _, ?_, ?_, ?_⟩
    · intro hbot
      apply hnA
      rw [commSub_eq_bot_iff]
      intro w hw a ha
      have hmem : B5.secHom A hAWs hAZs ⟨a, ha⟩ ∈ autSec A W (W ⊓ fixV L) := by
        rw [← B5.range_secHom A hAWs hAZs]
        exact ⟨⟨a, ha⟩, rfl⟩
      rw [hbot] at hmem
      have h1 : B5.secHom A hAWs hAZs ⟨a, ha⟩ = 1 := Subgroup.mem_bot.1 hmem
      exact sec_triv_imp_triv hLq hAn hW hAW ha
        (fun w' hw' => (((B5.mem_ker_secHom A hAWs hAZs ⟨a, ha⟩).1 (MonoidHom.mem_ker.2 h1)).2 w' hw').2)
        w hw
    · intro φ hφ ψ hψ
      rw [← hmapA] at hφ hψ
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hψ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAel.1 _ ha _ hb)
    · intro φ hφ
      rw [← hmapA] at hφ
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hAel.2 _ ha)
      rw [this, map_one]
  have hr : rAV (autSec A W (W ⊓ fixV L)) ≤ 1 := (rAV_le_one_iff hS2 hA2).2 hineq
  obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le hS2 hA2 hr
  exact ⟨B, hBA, hB⟩

end B69K

end CFSG.Quasithin
