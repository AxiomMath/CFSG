module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Core
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem Ivk73Cfg.center_L_eq_bot (h : Ivk73Cfg N L K Q) : center ↥L = ⊥ := by
  have := h.simple
  exact LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup
    (exists_noncomm_of_le_isQuasisimple h.K_le h.K_quasi)

theorem Ivk73Cfg.false_of_rank_out
    (h : Ivk73Cfg N L K Q) {r s : ℕ} (hrs : r + s ≤ 3)
    (hL : ∀ E : Subgroup ↥L, (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ r)
    (hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ s) : False := by
  refine h.false_of_autRank fun E hE => ?_
  have h1 := GHInv.card_le_two_pow_add_of_aut h.center_L_eq_bot hL hOut E hE
  have h2 : 2 ^ (r + s) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hrs
  omega

end CFSG.GH74.GLS.IVK
