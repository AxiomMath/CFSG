module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.CaseIIA
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.CaseIIM0
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.FirstStage
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Next

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def CaseTwoImpossible (H : Setting G) : Prop :=
  ∀ S Λ : Subgroup G, Stage H S Λ → 2 ∣ S.index → Nat.card (H.RC S) ≠ Nat.card S

theorem caseTwoImpossible (H : Setting G) : CaseTwoImpossible H := by
  intro S Λ h hS hcase
  obtain ⟨T, hT, hST, hTN, hTcard⟩ := h.exists_sylow_N hS
  have hconj : ∀ x ∈ T, IsConj H.z x → x ∈ S := by
    by_cases hΛ : 8 < Nat.card Λ
    · exact h.caseII_conj_le hS hcase hΛ hT hST hTN hTcard
    · have hΛ8 : Nat.card Λ = 8 := by
        have := Subgroup.card_le_of_le h.E_le
        rw [H.card_E] at this
        omega
      have hSV : S = H.V := by
        symm
        refine Subgroup.eq_of_le_of_card_ge h.V_le ?_
        rw [h.card_S, hΛ8, H.card_V]
      subst hSV
      exact fun x hx hxc => H.conj_mem_V_of_first_stage hS hcase (hTN hx) hxc
  have hnd := h.caseII_not_two_dvd_index_of_conj_le hS hT hST hTN hTcard hconj
  obtain ⟨M₀, hM₀T, hΛM, hzM, hrel⟩ := h.exists_M0 hS hcase hT hST hTN hTcard
  have := H.simple
  refine hnd (two_dvd_index_of_avoid H.nonabelian hT hM₀T hrel (hST h.z_mem) hzM H.order_z
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


theorem ascentStep_of_caseTwoImpossible {H : Setting G} (hII : CaseTwoImpossible H) :
    AscentStep H := by
  intro S Λ h hidx
  have h8 : Nat.card (H.RC S) = 8 * Nat.card S :=
    (h.RC_cases hidx).resolve_left (hII S Λ h hidx)
  obtain ⟨Λ', hst, hidx'⟩ := h.next h8
  exact ⟨H.RC S, Λ', hst, hidx', h8⟩

end CFSG.EvenSporadicStandard.J1Std
