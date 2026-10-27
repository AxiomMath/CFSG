module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7MainC

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

theorem i227_assembly
    (hCop : I22_7Coprime) (hComps : I22_7Comps) (hRank : I22_7Rank) (hU : I22_7ThreeRankU)
    (hFi : Fi22WeakCore3) : Input24_7K := by
  intro G _ _ K P hK hLK hF hPK hP3 hPcard
  have hcov : FiCoverK ↥K := i227m_fiCoverK_of_subgroup hK hLK hF
  have hP'3 : IsPGroup 3 (P.subgroupOf K) :=
    hP3.of_injective (Subgroup.subgroupOfEquivOfLe hPK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPK).injective
  have hP'card : Nat.card (P.subgroupOf K) = 3 ^ (Nat.card ↥K).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]
    exact hPcard
  have h := i227m_abstract hCop hComps hRank hU hFi hcov hP'3 hP'card
  intro x hx
  exact i227m_map_weakCoreIn_subtype (p := 3) (by norm_num) (K := K) (P := P)
    ⟨⟨x, hx⟩, h (Subgroup.mem_top _), rfl⟩

end CFSG.HardMathSupport.Solomon.Coordinator
