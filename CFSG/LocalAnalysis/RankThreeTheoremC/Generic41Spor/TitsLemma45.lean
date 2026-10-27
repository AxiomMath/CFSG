module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G]

theorem tits_lemma45_G {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hS : Setting G)
    (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : TitsFacts)
    (hc : PointConfig IsTitsType G 5 P M x J) {U : Subgroup G} (hU : IIPlane 5 P x J U) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hTcard, hTel, -⟩ := plane_T_structure hX.sylow hc
  have hT2 : 2 ≤ CFSG.Open.pRank 5 (u3T P x J) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.le_pRank_of_elemAbelian_card (by norm_num) le_rfl hTel
      hTcard
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTC : u3T P x J ≤ Subgroup.centralizer ({x} : Set G) := hTS.trans inf_le_right
  have hTJ : u3T P x J ≤ J := inf_le_right
  have ha : ∃ a ∈ U ⊓ u3T P x J, a ≠ 1 := by
    have hne : U ⊓ u3T P x J ≠ ⊥ := by
      intro h
      have := hU.card_inf
      rw [h, Subgroup.card_bot] at this
      norm_num at this
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨(a : G), a.2, fun h => ha1 (Subtype.ext h)⟩
  refine typeII_lemma45_lift hS hD1 hU0 hX.lemma45 hX.maximal
    (fun A B _ _ e h => ⟨h.1, isoLie_of_mulEquiv e h.2⟩) hc hT2 hU.elem hU.card hU.le hU.mem ha ?_
  intro X _ ρ K R U₀ hf
  obtain ⟨a, ⟨haU, haT⟩, ha1⟩ := ha
  intro h
  have hmem : ρ ⟨a, hTC haT⟩ ∈ U₀ ⊓ K :=
    ⟨hf.U₀_mem ⟨a, hTC haT⟩ haU, hf.K_mem ⟨a, hTC haT⟩ (hTJ haT)⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact ha1 (hf.inj ⟨a, hTC haT⟩ haT hmem)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
