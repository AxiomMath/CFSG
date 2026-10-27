module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraph

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem c27_setupE {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K)
    (hsyl : ∀ {M R : Subgroup G}, M ∈ Ω → R ∈ RSet Ω → R ≤ M → IsSylow2In R M)
    (hl69 : ∀ S : Sylow 2 G, ∃ η ∈ etaSet Ω (S : Subgroup G),
      ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) :
    ∃ (S : Sylow 2 G) (R T W : Subgroup G),
      (R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)) ∧ (T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)) ∧
        (W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W) := by
  obtain ⟨hJΩ, hJK, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := hsyl hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := T3.exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := hl69 S
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    le_normalizer_biSup_of_acts hηinv
  exact ⟨S, R, T, ⨆ U ∈ η, U, ⟨mem_RSet_of_isSylow2In hK hRK, hRK.1, le_sup_right.trans hS⟩,
    ⟨hT, hTJ, le_sup_left.trans hS⟩,
    ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
      fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩⟩

theorem c27_nbrE {K : Subgroup G} (hcl : ConjInvariant Ω)
    (hsymm : ∀ {A B : Subgroup G}, A ∈ Ω → B ∈ Ω → B ∈ omegaNbr Ω A → A ∈ omegaNbr Ω B)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hedge : ¬ DEdgeless Ω) :
    ∃ J ∈ omegaNbr Ω K, True := by
  unfold DEdgeless at hedge
  push Not at hedge
  obtain ⟨K₀, hK₀, J₀, hJ₀, hadj⟩ := hedge
  have hnbr : J₀ ∈ omegaNbr Ω K₀ := by
    rcases hadj with h | h
    · exact h
    · exact hsymm hJ₀ hK₀ h
  obtain ⟨g, hg⟩ := htrans K₀ hK₀
  have h1 := omegaNbr_conj hcl hnbr g⁻¹
  rw [← hg, conjSub_inv_conjSub] at h1
  exact ⟨conjSub g⁻¹ J₀, h1, trivial⟩

end CFSG.ClassicalInvolution.Asc77
