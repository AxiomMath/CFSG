module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.CaseIIA
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.CaseIIM0
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.FirstStage
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Fusion

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

@[expose] def CaseTwoImpossible (H : LocalSetting G) : Prop :=
  ∀ S Λ : Subgroup G, Stage H S Λ → 2 ∣ S.index →
    ¬ ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H.RC S → P ≤ S

theorem caseTwoImpossible (H : LocalSetting G) : CaseTwoImpossible H := by
  intro S Λ h hS hcase
  obtain ⟨T, hT, hST, hTN, hTcard⟩ := h.exists_sylow_N hS
  have hconj : ∀ x ∈ T, IsConj H.z x → x ∈ S := by
    by_cases hΛ : 8 < Nat.card Λ
    · exact h.caseII_conj_le hcase hΛ hT hTN
    · have hΛ8 : Nat.card Λ = 8 := by
        have := Subgroup.card_le_of_le h.E_le
        rw [H.card_E] at this
        omega
      have hSV : S = H.V := by
        symm
        refine Subgroup.eq_of_le_of_card_ge h.V_le ?_
        rw [h.card_S, hΛ8, H.card_V]
      have hΛE : Λ = H.E := by
        symm
        refine Subgroup.eq_of_le_of_card_ge h.E_le ?_
        rw [H.card_E, hΛ8]
      subst hSV
      subst hΛE
      exact fun x hx hxc => H.conj_mem_V_of_first_stage h hS hcase (hTN hx) hxc
  have hnd := h.caseII_not_two_dvd_index_of_conj_le hT hST hTN hTcard hconj
  obtain ⟨M₀, hM₀T, hΛM, hzM, hrel⟩ := h.exists_M0 hcase hT hST hTN hTcard
  have := H.simple
  refine hnd (J1Std.two_dvd_index_of_avoid H.nonabelian hT hM₀T hrel (hST h.z_mem) hzM H.order_z
    (fun g hg => ?_))
  have hgT : g⁻¹ * H.z * g ∈ T := hM₀T hg
  have hgc : IsConj H.z (g⁻¹ * H.z * g) := _root_.isConj_iff.2 ⟨g⁻¹, by simp⟩
  have hgS := hconj _ hgT hgc
  have hgΛ : g⁻¹ * H.z * g ∉ Λ := fun hh => h.not_isConj_of_mem hh hgc
  have h1 := (h.cover _ hgS).resolve_left hgΛ
  apply hzM
  have h2 := mul_mem (inv_mem hg) (hΛM h1)
  have e : (g⁻¹ * H.z * g)⁻¹ * (g⁻¹ * H.z * g * H.z) = H.z := by group
  rwa [e] at h2

end CFSG.EvenSporadicStandard.ReeStd
