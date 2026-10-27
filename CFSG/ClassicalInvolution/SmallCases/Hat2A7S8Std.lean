module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Setup


theorem a7C27_nbr_proved : A7C27_nbr := by
  intro G _ _ _ Ω K hs hedge
  have hΩ : HypOmegaGen Ω := hs.hyp
  unfold DEdgeless at hedge
  push Not at hedge
  obtain ⟨K₀, hK₀, J₀, hJ₀, hadj⟩ := hedge
  have hnbr : J₀ ∈ omegaNbr Ω K₀ := by
    rcases hadj with h | h
    · exact h
    · exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ₀ hK₀ h
  obtain ⟨g, hg⟩ := hs.trans K₀ hK₀
  have h1 := omegaNbr_conj hΩ.conjInvariant hnbr g⁻¹
  rw [← hg, conjSub_inv_conjSub] at h1
  exact ⟨conjSub g⁻¹ J₀, h1, trivial⟩

theorem a7C27_setup_proved : A7C27_setup := by
  intro G _ _ _ Ω K hs hnt _ z hz J hJ t ht
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hJΩ, hJK, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := T3.exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    Thompson.le_normalizer_biSup_of_acts hηinv
  exact ⟨S, R, T, ⨆ U ∈ η, U,
    { stand := hs
      noTwins := hnt
      hz := hz
      hJ := hJ
      ht := ht
      hR := ⟨mem_RSet_of_isSylow2In hs.mem hRK, hRK.1, le_sup_right.trans hS⟩
      hT := ⟨hT, hTJ, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
        fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩ }⟩

end Setup

end CFSG.ClassicalInvolution.Hat2A7S
