module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic

public section

namespace CFSG.QuasithinUnique.Bridge.Over

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Ω : Type} [Group Ω]

theorem lift_to_subgroup {L T X K : Subgroup Ω} (hT : IsSylowTwoOf T L) (hTX : T ≤ X)
    (hXL : X ≤ L) (hXne : X ≠ L) (hKX : K ≤ X) (hsub : IsSubnormal K X) :
    IsSylowTwoOf (T.subgroupOf L) ⊤ ∧ T.subgroupOf L ≤ X.subgroupOf L ∧
      X.subgroupOf L ≠ ⊤ ∧ K.subgroupOf L ≤ X.subgroupOf L ∧
      IsSubnormal (K.subgroupOf L) (X.subgroupOf L) := by
  refine ⟨⟨le_top, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  · rw [show ((T.subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index = (T.subgroupOf L).index from
      Subgroup.relIndex_top_right _]
    exact hT.2.2
  · exact fun x hx => Subgroup.mem_subgroupOf.2 (hTX (Subgroup.mem_subgroupOf.1 hx))
  · intro htop
    exact hXne (le_antisymm hXL (Subgroup.subgroupOf_eq_top.1 htop))
  · exact fun x hx => Subgroup.mem_subgroupOf.2 (hKX (Subgroup.mem_subgroupOf.1 hx))
  · exact A3.subnormal_comap L.subtype hsub

theorem lift_quasisimple_or_card_three {L K : Subgroup Ω} (hKL : K ≤ L)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    CFSG.IsQuasisimple ↥(K.subgroupOf L) ∨ Nat.card ↥(K.subgroupOf L) = 3 := by
  rcases hK with hq | h3
  · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKL).symm hq)
  · exact Or.inr (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, h3])

theorem not_le_center_of_not_le_centralizer {L K : Subgroup Ω} (hKL : K ≤ L)
    (hKc : ¬ K ≤ Subgroup.centralizer (L : Set Ω)) : ¬ K.subgroupOf L ≤ Subgroup.center ↥L := by
  intro h
  apply hKc
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.1
    (h (show (⟨k, hKL hk⟩ : ↥L) ∈ K.subgroupOf L from hk))) ⟨l, hl⟩)

theorem false_of_overgroups [Finite Ω] {L T X K : Subgroup Ω} (hLq : CFSG.IsQuasisimple ↥L)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (hT : IsSylowTwoOf T L) (hTX : T ≤ X)
    (hXL : X ≤ L) (hXne : X ≠ L) (hKX : K ≤ X) (hsub : IsSubnormal K X)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3)
    (hKc : ¬ K ≤ Subgroup.centralizer (L : Set Ω))
    (hov : Overgroups (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨hT', hTX', hXne', hKX', hsub'⟩ := lift_to_subgroup hT hTX hXL hXne hKX hsub
  have hKL : K ≤ L := hKX.trans hXL
  obtain ⟨hT'', hTX'', hXne'', hKX'', hsub'', hK''⟩ := reduce_center hLq hodd hT' hTX' hXne' hKX'
    hsub' (lift_quasisimple_or_card_three hKL hK) (not_le_center_of_not_le_centralizer hKL hKc)
  exact false_of_charTwo (hov _ _ hT'' hTX'' hXne'') hKX'' hsub'' hK''

end CFSG.QuasithinUnique.Bridge.Over
