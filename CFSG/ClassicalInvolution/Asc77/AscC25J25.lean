module

public import CFSG.ClassicalInvolution.Asc77.AscC25J24
public import CFSG.ClassicalInvolution.Asc77.AscC25J12
public import CFSG.ClassicalInvolution.Asc77.AscC25J13
public import CFSG.ClassicalInvolution.Asc77.AscC25J14c
public import CFSG.ClassicalInvolution.Asc77.AscC25J23
public import CFSG.ClassicalInvolution.Uniform.U3Thm4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem typed9_of_cit3 (hc3 : Q3.CIT3Inductive) : Typed9 p f := by
  intro h9 G _ _ _ Ω K K' W S R R' z t u₁ u₂ t' h a haS ha2 hF' hat
  obtain ⟨hp3, hf2⟩ := eq_three_two_of_pow_eq_nine (Fact.out : p.Prime) h9
  subst hp3
  obtain ⟨hzA, hL⟩ := weak_member_data9 h h9 haS ha2 hF'
  have hzKa : z ∈ K' ⊓ Subgroup.centralizer ({a} : Set G) := ⟨h.hz'.mem, hzA⟩
  have hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K' a)) :=
    crossIn_hypOmegaModU h.hΩ h.hK' h.hz' hzA hL
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := crossIn_twinSect0 h hF' hat hzA hΛ
  refine ⟨hzA, ht'a, hzX, a₀, b₀, T, ?_⟩
  have hf1 : f / 2 = 1 := by omega
  rw [hf1]
  set L := crossIn K' a with hLdef
  set X := conjGen L with hX
  have hne : (conjFamily L).Nonempty := ⟨L, ⟨1, conjSub_one L⟩⟩
  have hIn : Q3.InClass3 (restrictFamily (conjFamily L) X) := T3CII.inClass3_layer hΛ hne
  obtain ⟨ι, -, ⟨D3⟩⟩ := hc3 ↥X (restrictFamily (conjFamily L) X) hIn
  have hΦ : HypOmegaModU (.sl2 3 1) (oddQuotientFamily (restrictFamily (conjFamily L) X)) :=
    hypOmegaModU_oddQuotientFamily (hypOmegaModU_restrict hΛ X)
  have hO : classicalInvolutionOddCore (↥X ⧸ classicalInvolutionOddCore ↥X) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥X
  have hA := aEmpty_secFamily hΛ (crossIn_aEmpty h hΛ)
  have h4 : Thm4BelowU 3 1 (Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) + 1) :=
    thm4BelowU_of_citBelowT ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mpr
      (fun Y _ _ _ Λ' hΛ' => hc3 Y Λ' hΛ'))
  rcases classify_sect h4 (Nat.lt_succ_self _) hΦ hO hA (LieSystemDataU.ofQ3 D3) T with
    hall | ⟨D', t₁, k₁, hCI, htags⟩
  · left
    have hu : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        IsUniqueInvolution (conjSub c L) (c * ⟨z, hzA⟩ * c⁻¹) := fun c =>
      crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa c
    have hconn' : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        secImg X (conjSub c L) = secImg X L ∨
        secImg X (conjSub c L) = secImg X (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) L) :=
      fun c => hall _ ((mem_secFamily_iff L _).mpr ⟨c, rfl⟩)
    unfold zStarOf
    refine Subgroup.mem_map.mpr ⟨⟨z, hzA⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    exact (central_of_connected L ⟨z, hzA⟩ hu hzX _ T.hzA' hconn' c).symm
  · right
    have hne' : (oddQuotientFamily (restrictFamily (conjFamily L) X)).Nonempty := ⟨_, T.hA⟩
    have hε : (!piSign 3 1) = true := by decide
    rcases htags with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hh | hh | hh | hh
    · left
      exact ⟨.PSp, 2, Or.inl ⟨rfl, rfl, rfl⟩, D', hCI⟩
    · right
      exact ⟨.PSL, 4, Or.inr (Or.inl ⟨rfl, hε, rfl, rfl⟩), D', hCI⟩
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inl hh) (crossIn_nc4_excl h hzA)).elim
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inr (Or.inl hh)) (crossIn_nc4_excl h hzA)).elim
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inr (Or.inr (Or.inl hh)))
        (crossIn_nc4_excl h hzA)).elim
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inr (Or.inr (Or.inr hh)))
        (crossIn_nc4_excl h hzA)).elim

end Final

end CFSG.ClassicalInvolution.Asc77.C25J
