module

public import CFSG.ClassicalInvolution.RouteD.GapsPatternDFinal
public import CFSG.ClassicalInvolution.RouteD.GapsOrthPairs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.Timmesfeld (edgeD)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

local macro "idx_tac" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (apply fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

theorem adapted_pattern_D5
    (hF : OrthFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 5 p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f .POmegaPlus 5 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus 5 Ω z) (nd : DNodes p f 5 Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp : Fin 5} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp) :
    pp.val = 0 ∧ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.J pp) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hβJ : ∀ a, β ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact hnKβ this
  have hsymm : Commute (nd.w pp) t :=
    (commute_of_conjSub_eq' h2 (c.hex _ (nd.mem pp)) (nd.cl pp) hnorm).symm
  have hp0 : pp.val = 0 := by
    by_contra hne
    have hpv := pp.isLt
    obtain ⟨pv, hpv'⟩ := pp
    simp only at hne hpv
    interval_cases pv
    · exact hne rfl
    ·
      obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem ⟨0, by omega⟩)
        (nd.cl ⟨0, by omega⟩)
      refine absurd (pair_config cx (pairBound_plus c.hp2 (by norm_num) c.hq)
        (nd.mem_loc ⟨0, by omega⟩ c.hK (nd.commK _))
        (nd.mem_loc ⟨0, by omega⟩ hβ (hfix _ (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨2, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨3, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        c.hz ht (nd.cl _) (nd.cl _) hKne hnKβ hzt hnormK
        (nd.ne_J hΩ (by idx_tac)) (nd.not_commutes_of_adj (by idx_tac)) (nd.commute_w h2 _ _)
        (nd.conjSub_w h2 (by idx_tac)) (nd.commK _) (nd.commK _) (hfix _ (by idx_tac))
        (hfix _ (by idx_tac))) (by norm_num)
    ·
      obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem ⟨3, by omega⟩)
        (nd.cl ⟨3, by omega⟩)
      refine absurd (pair_config cx (pairBound_plus c.hp2 (by norm_num) c.hq)
        (nd.mem_loc ⟨3, by omega⟩ c.hK (nd.commK _))
        (nd.mem_loc ⟨3, by omega⟩ hβ (hfix _ (by idx_tac)))
        (nd.mem_loc ⟨3, by omega⟩ (nd.mem ⟨0, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨3, by omega⟩ (nd.mem ⟨1, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        c.hz ht (nd.cl _) (nd.cl _) hKne hnKβ hzt hnormK
        (nd.ne_J hΩ (by idx_tac)) (nd.not_commutes_of_adj (by idx_tac)) (nd.commute_w h2 _ _)
        (nd.conjSub_w h2 (by idx_tac)) (nd.commK _) (nd.commK _) (hfix _ (by idx_tac))
        (hfix _ (by idx_tac))) (by norm_num)
    ·
      obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem ⟨0, by omega⟩)
        (nd.cl ⟨0, by omega⟩)
      exact chain5_false cx (chainBound0_plus c.hp2 (by norm_num) c.hq) (by norm_num)
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨4, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨2, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨3, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ hβ (hfix _ (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ c.hK (nd.commK _))
        (nd.cl _) (nd.cl _) (nd.cl _) ht c.hz
        ⟨nd.ne_J hΩ (by idx_tac), nd.not_commutes_of_adj (by idx_tac), nd.commute_w h2 _ _,
          nd.conjSub_w h2 (by idx_tac)⟩
        ⟨nd.ne_J hΩ (by idx_tac), nd.not_commutes_of_adj (by idx_tac), nd.commute_w h2 _ _,
          nd.conjSub_w h2 (by idx_tac)⟩
        ⟨(hβJ _).symm, fun h => hmov (commutes_symm h), hsymm, hnorm⟩
        ⟨hKne.symm, fun h => hnKβ (commutes_symm h), hzt.symm,
          conjSub_eq_of_standardPair h2 (linearBlockStandardPair_symm hW) c.hz.mem
            c.hz.orderOf_eq_two⟩
        (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)) (commutes_symm (hfix _ (by idx_tac)))
        (commutes_symm (nd.commK _)) (commutes_symm (hfix _ (by idx_tac)))
        (commutes_symm (nd.commK _)) (commutes_symm (nd.commK _))
    ·
      obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem ⟨0, by omega⟩)
        (nd.cl ⟨0, by omega⟩)
      exact chain5_false cx (chainBound0_plus c.hp2 (by norm_num) c.hq) (by norm_num)
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨3, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨2, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨4, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ hβ (hfix _ (by idx_tac)))
        (nd.mem_loc ⟨0, by omega⟩ c.hK (nd.commK _))
        (nd.cl _) (nd.cl _) (nd.cl _) ht c.hz
        ⟨nd.ne_J hΩ (by idx_tac), nd.not_commutes_of_adj (by idx_tac), nd.commute_w h2 _ _,
          nd.conjSub_w h2 (by idx_tac)⟩
        ⟨nd.ne_J hΩ (by idx_tac), nd.not_commutes_of_adj (by idx_tac), nd.commute_w h2 _ _,
          nd.conjSub_w h2 (by idx_tac)⟩
        ⟨(hβJ _).symm, fun h => hmov (commutes_symm h), hsymm, hnorm⟩
        ⟨hKne.symm, fun h => hnKβ (commutes_symm h), hzt.symm,
          conjSub_eq_of_standardPair h2 (linearBlockStandardPair_symm hW) c.hz.mem
            c.hz.orderOf_eq_two⟩
        (nd.commutes_of_not_adj (by idx_tac) (by idx_tac)) (commutes_symm (hfix _ (by idx_tac)))
        (commutes_symm (nd.commK _)) (commutes_symm (hfix _ (by idx_tac)))
        (commutes_symm (nd.commK _)) (commutes_symm (nd.commK _))
  refine ⟨hp0, ?_⟩
  refine scenario_C hF c hsingle hshape nd hβ ht ⟨W, hW⟩ (pp := pp) (b := ⟨2, by omega⟩) hfix hmov
    hnorm ?_ ?_ <;>
  idx_tac

end CFSG.ClassicalInvolution.RouteD.Gaps
