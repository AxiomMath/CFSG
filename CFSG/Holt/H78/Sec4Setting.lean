module

public import CFSG.Holt.H78.Sec4Defs
import CFSG.Holt.H78.OrbitalOdd
import CFSG.Holt.H78.Refine
public import CFSG.Holt.H78.Sections

public section

namespace CFSG.Holt.H78


variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Hyp.toSetting (hS : Sec4Hyp G Ω) : Sec4Setting G Ω where
  toSec4Hyp := hS
  known_inducedPerm _ hlt _ := hS.below.mono (Or.inl hlt)
  star_centralizerImage hP h3 := isStarGroup_centralizerImage hS.star hP h3
  star_twoPoint hαβ h3 := isStarGroup_twoPointSection hS.star hS.below hαβ h3
  card_twoPoint_lt α β _ := hS.star.card_twoPoint_lt α β
  longInv_inducedPerm hX hlt hY hne y :=
    mem_longInv_inducedPerm_iff hS.star hX hY (hS.below.mono (Or.inl hlt)) hne y
  frattini hΓ _ hV hVΓ _ hy hyΓ :=
    exists_mem_longInv_centralizer_smul_eq hS.star hS.below hΓ hV hVΓ hy hyΓ
  sylow_twoPoint hαβ hγ _ hT := lemma_3_2_i hS.star hS.below hαβ hγ hT
  odd_fixingSubgroup_orbit hΓ := haveI := hS.preprimitive; lemma_3_4 hS.star hΓ
  holtDelta'_eq_orbit hαβ hγ := lemma_3_3_iii_orbit hS.star hS.below hαβ hγ
  centralizer_twoPoint hαβ _ hS' := lemma_3_3_iii_centralizer hS.star hS.below hαβ hS'
  card_longInvSwap_typeL hv D hO _ _ _ hab := lemma_3_5_i hS.star hS.below hv D hO hab
  exists_one_lt_card_holtDelta hv hvα _ hPn hPodd hP1 := haveI := hS.preprimitive
    lemma_3_5_ii_exists hS.star hS.below hS.pPrimeCore_eq_bot hv hvα hPn hPodd hP1

end CFSG.Holt.H78
