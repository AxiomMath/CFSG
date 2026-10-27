module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaR

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

structure ThreeEightHyp (G T V : Subgroup Γ) : Prop where
  charTwo : CharTwo G
  sylow : IsSylowOf 2 T G
  ne : cStarIn G T ≠ G
  normal : G ≤ Subgroup.normalizer (V : Set Γ)
  le_V : omegaOneCenterOf T ≤ V
  V_le : V ≤ omegaOneCenterOf (pCoreOf 2 G)
  natural : (∃ n : ℕ, 1 ≤ n ∧ IsNatSL G V n) ∨ (∃ m : ℕ, 1 ≤ m ∧ IsNatSym G V (2 * m + 1))

structure NatTailData (G T Ê : Subgroup Γ) : Prop where
  subnormal : IsSubnormal Ê G
  not_le : ¬ Ê ≤ cStarIn G T
  baum_le : baum T ≤ Subgroup.normalizer (Ê : Set Γ)
  caseTwo : baum T ⊔ Ê = G → ∃ V : Subgroup Γ, ThreeEightHyp G T V

theorem le_of_isSubnormal_bhs {L K : Subgroup Γ} (h : IsSubnormal L K) : L ≤ K :=
  h.le

variable [Finite Γ] {G T : Subgroup Γ}

theorem false_of_subnormal_block (h : MinCex G T) (h4 : Seven4 G T) {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) (hsub : IsSubnormal F G) : False := by
  have hFmax : F ∈ btBlocksMax G T := mem_btBlocksMax_of_subnormal h hF hsub
  have hFΩ : F ∈ omegaSet G T :=
    ⟨mem_bStarG_of_mem_bStarT ⟨⟨hFmax, hF⟩, hFn⟩, hsub⟩
  exact h4 F hFΩ.1 hsub

end CFSG.CGT.PushingUpLit.BHS7
