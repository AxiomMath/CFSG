module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SuzCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelRow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore
open CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.HypOne
open CFSG.EvenSporadicStandard.HypOne.Suz CFSG.Blueprint.NativeSporadic

theorem suz_autRowData :
    AutRowData suzM suzT where
  model := autModel
  index := suz_index_two
  centerInv := centerInv_suz
  outerLe := by
    intro a ha ha2 w hw hwM hww hall
    have hw1 : w ≠ 1 := fun e => hwM (e ▸ suzM.one_mem)
    have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
    have hle : centralizerIn suzM a ≤ centralizerIn suzM w := fun y hy => by
      have hy' := mem_centralizerIn.1 hy
      exact mem_centralizerIn.2 ⟨hy'.1, hall y hy'.1 hy'.2⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rcases card_centralizerIn_suzM_inner ha ha2 with h1 | h1 <;>
      rcases card_centralizerIn_suzM_outer hw hwM hw2 with h2 | h2 <;> rw [h1, h2] at hdvd <;>
      norm_num at hdvd

theorem suz_outerCentre
    (α : MulAut ↥suzM) (w : Equiv.Perm (Fin 1782)) (hw : w ∈ suzT) (hwM : w ∉ suzM)
    (_ : ∀ p : suzM, ((α p : suzM) : Equiv.Perm (Fin 1782)) = w * p * w⁻¹) (hww : w * w = 1)
    (z : Equiv.Perm (Fin 1782)) (hz : z ∈ suzM) (hz2 : orderOf z = 2) (_ : z * w = w * z)
    (hall : ∀ y ∈ suzM, y * w = w * y → y * z = z * y) : False := by
  have hw1 : w ≠ 1 := fun e => hwM (e ▸ suzM.one_mem)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  have hle : centralizerIn suzM w ≤ centralizerIn suzM z := fun y hy => by
    have hy' := mem_centralizerIn.1 hy
    exact mem_centralizerIn.2 ⟨hy'.1, hall y hy'.1 hy'.2⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rcases card_centralizerIn_suzM_outer hw hwM hw2 with h1 | h1 <;>
    rcases card_centralizerIn_suzM_inner hz hz2 with h2 | h2 <;> rw [h1, h2] at hdvd <;>
    norm_num at hdvd

theorem suz_autCenterCond_native :
    AutCenterCond ↥suzM :=
  AutCenterCondExc.toCond (suz_autRowData.autCenterCondExc
    fun α w hw hwM hα hww z hz hz2 hzw hall => suz_outerCentre α w hw hwM hα hww z hz hz2 hzw hall)

theorem exists_commuting_suz :
    ∀ u ∈ suzM, orderOf u = 2 → ∀ w ∈ suzT, w * w = 1 →
      ∃ x ∈ suzM, (x * u * x⁻¹) * w = w * (x * u * x⁻¹) := by
  refine exists_commuting_conj_of_cover (P := suzM) (R := suzT)
    [suzInv 0, suzInv 1] [suzInv 0, suzInv 1, suzInv 2, suzInv 3] cover_suzM cover_suzT
    (fun r hr c hc => ?_) (fun r hr r' hr' => ?_) suzM_le_suzT
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact exists_suzM_conj (i := 0) (by norm_num) hc
    · exact exists_suzM_conj (i := 1) (by norm_num) hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl | rfl | rfl <;>
      exact exists_commuting_rep (by norm_num) (by norm_num)

theorem suz_umovesCond_native :
    UMovesCond ↥suzM :=
  AutModel.umovesCond autModel fun u hu hu2 w hw hww => exists_commuting_suz u hu hu2 w hw hww

end CFSG.EvenSporadicStandard.Solomon78
