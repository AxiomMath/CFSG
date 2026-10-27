module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutInput
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutJanko
public import CFSG.Sporadic.ONOddCore.FixedRankOne
public import CFSG.Walter.J1Props.Elt
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

theorem onOuterComponentsInput_of_local
    (hloc : ONOuterLocalInput) : ONOuterComponentsInput := by
  intro G _ hG α hα2 hα B hB
  obtain ⟨ψ⟩ := hG
  have : Finite G := Finite.of_equiv _ (ψ.trans ONSchreier.onEquivPv).symm.toEquiv
  obtain ⟨⟨V, hVfix, hVea, hV4⟩, -⟩ :=
    Sporadic.ONOddCore.glq_sporadic_outer_involution_fixed_rank_one_ON_exclusion ⟨ψ⟩ α hα2
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV4
    exact absurd hV4 (by norm_num)
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hv2 : v ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian v hvV
  have hvfix : v ∈ fixSub α := hVfix hvV
  set z : fixSub α := ⟨v, hvfix⟩ with hzdef
  have hz : orderOf z = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hv1 (Subtype.ext ?_)
    · exact hv2
    · have h' : (z : G) = 1 := congrArg Subtype.val h
      exact h'
  obtain ⟨hJ⟩ := ONOut.nonempty_jankoHyp₀ (hloc G ⟨ψ⟩ α hα2 hα) hz
  have : IsSimpleGroup (fixSub α) := hJ.isSimpleGroup
  obtain ⟨eJ⟩ := hJ.nonempty_mulEquiv_walterJ1
  have hcard : Nat.card (fixSub α) = 175560 := by
    rw [Nat.card_congr eJ.toEquiv]
    exact Walter.J1Props.card_walterJ1
  have hZ : center (fixSub α) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (fixSub α)) with h | h
    · exact h
    · exfalso
      have ha : ((hJ.iso.symm ONOut.a5Three : hJ.F) : fixSub α) ∈ center (fixSub α) :=
        h ▸ mem_top _
      have hab := mem_center_iff.mp ha ((hJ.iso.symm ONOut.a5Two : hJ.F) : fixSub α)
      apply ONOut.a5_not_comm
      apply hJ.iso.symm.injective
      rw [map_mul, map_mul]
      exact Subtype.ext hab.symm
  have hBtop : B = ⊤ := QuasithinUnique.Id2519.isComponent_eq_top_of_isSimpleGroup hB
  have hZB : Nat.card (center B) = 1 := by
    have hbot : center B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxC : (x : fixSub α) ∈ center (fixSub α) := by
        rw [mem_center_iff]
        intro g
        have hg : g ∈ B := hBtop ▸ mem_top g
        exact congrArg Subtype.val (mem_center_iff.mp hx ⟨g, hg⟩)
      rw [hZ, mem_bot] at hxC
      exact Subtype.ext hxC
    rw [hbot, Subgroup.card_bot]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
  rw [hZB, mul_one] at h1
  rw [← h1, hBtop, Subgroup.card_top, hcard]

end CFSG.ComponentClassification.SolMax
