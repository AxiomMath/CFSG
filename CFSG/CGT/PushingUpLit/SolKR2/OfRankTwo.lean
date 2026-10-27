module

public import CFSG.CGT.PushingUpLit.SolKR2.Defs
public import CFSG.CGT.PushingUpLit.SolKAb.Rank

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.CGT.PushingUpLit.SolKAb
open CFSG.RankThree.GF2n.Tim78 (omegaTwoSub mem_omegaTwoSub_iff)
open CFSG.RankThree.PartTwo (omegaOneSub)
open CFSG.Open (IsElemAbelian)

theorem R2.of_rankTwo {G : Type} [Group G] [Finite G] {K : Subgroup G} (S : STSetting G K)
    (R : Sylow 2 K) (hc : IsCommSubgroup (sylowImg R)) (hne : ¬ IsElemAbelian 2 (sylowImg R))
    (h4 : Nat.card ↥(omegaOneSub (sylowImg R)) = 4)
    (hH : ∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x ∈ sylowImg R ∧ x ^ 4 = 1) ∧
      Nonempty (↥H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))) :
    R2 (Subgroup.normalizer (K : Set G)) (sylowImg R) := by
  obtain ⟨H, hHdef, ⟨e⟩⟩ := hH
  have hHU : H = omegaTwoSub (sylowImg R) := by
    ext x
    rw [hHdef, mem_omegaTwoSub_iff hc]
  subst hHU
  exact { H := S.hypH R hc, card4 := h4, c4c4 := ⟨e⟩, ne := hne }

end CFSG.CGT.PushingUpLit.SolKR2
