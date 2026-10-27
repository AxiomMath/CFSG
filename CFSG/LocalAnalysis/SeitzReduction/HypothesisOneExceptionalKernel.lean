module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptional
public import CFSG.LocalAnalysis.SeitzReduction.FoursGroupExceptionalBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.EvenSmallLie
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_sylow_eq_two_of_exceptional (hH : ExceptionalHypothesisOne) (hset : StandardSetting G L)
    (hZ : center L = ⊥) {τ : StatedLieTag} {f : ℕ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .twistedE6 ∨ τ = .E7 ∨ τ = .E8)
    (hL : LieModel (L ⧸ center L) τ 0 2 f) (S : Sylow 2 (centralizer (L : Set G))) :
    Nat.card S = 2 :=
  card_sylow_eq_two_of_standard_of_center_eq_bot hset hZ (hH _ τ f hτ hL) S

theorem inf_centralizer_eq_zpowers_of_exceptional (hH : ExceptionalHypothesisOne)
    (hset : StandardSetting G L) (hZ : center L = ⊥) {τ : StatedLieTag} {f : ℕ}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .twistedE6 ∨ τ = .E7 ∨ τ = .E8)
    (hL : LieModel (L ⧸ center L) τ 0 2 f) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot hset hZ (hH _ τ f hτ hL) htC ht

end CFSG.SeitzReduction
