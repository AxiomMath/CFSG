module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7MainR
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22Two
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7MainQ

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

theorem i227m_five_le_pRank
    {K : Type} [Group K] [Finite K] (hK : FiCoverK K) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨e⟩ := hK.fi
  obtain ⟨V, hV, hVc⟩ := i1021_fi22_two_rank_five e
  exact i1021_fi22_of_two_rank e hV hVc K (QuotientGroup.mk' (GLAPPrimeCore 5 K))
    (QuotientGroup.mk'_surjective _)

theorem i227m_core
    (hCop : I22_7Coprime) (hComps : I22_7Comps) (hRank : I22_7Rank) (hU : I22_7ThreeRankU)
    (hFi : Fi22WeakCore3) {K : Type} [Group K] [Finite K] (hK : FiCoverK K)
    (hY : GLAPPrimeCore 3 K = ⊥) {P : Subgroup K} (hP3 : IsPGroup 3 P)
    (hPcard : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    (⊤ : Subgroup K) ≤ weakCoreIn 3 P ⊤ := by
  set R : Subgroup K := GLAPPrimeCore 5 K with hR
  set W : Subgroup K := ⁅R, (⊤ : Subgroup K)⁆ with hWdef
  have hWn : W.Normal := Subgroup.commutator_normal R ⊤
  have hQ := i227m_quotient_weakCore hFi hK hP3 hPcard
  by_cases hcomp : ∃ J : Subgroup K, J ≤ W ∧ IsSubnormal J ⊤ ∧ CFSG.Open.IsQuasisimple ↥J
  · obtain ⟨J, hJW, hJ, hq⟩ := hcomp
    exact hComps K hK hY J hJW hJ hq P hP3 hPcard
  · have hNo : NoCompIn W := fun J hJW hJ hq => hcomp ⟨J, hJW, hJ, hq⟩
    by_cases h3 : 3 ≤ CFSG.Open.pRank 3 (oThreeIn W)
    · exact hU K hK hY W hWdef hNo h3 P hP3 hPcard hQ
    · have hle : CFSG.Open.pRank 3 (oThreeIn W) ≤ 2 := by omega
      have hW : W = ⊥ := hRank K hK.perfect hY R W hWdef hNo hle
      have hrk : 3 ≤ CFSG.Open.pRank 3 P :=
        i227m_three_le_pRank_of_sylow (i227m_five_le_pRank hK) hPcard
      exact hCop K W (by rw [hW]; simp) P hP3 hrk hQ

theorem i227m_abstract
    (hCop : I22_7Coprime) (hComps : I22_7Comps) (hRank : I22_7Rank) (hU : I22_7ThreeRankU)
    (hFi : Fi22WeakCore3) {K : Type} [Group K] [Finite K] (hK : FiCoverK K)
    {P : Subgroup K} (hP3 : IsPGroup 3 P)
    (hPcard : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    (⊤ : Subgroup K) ≤ weakCoreIn 3 P ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup K := GLAPPrimeCore 3 K with hY
  have hK' : FiCoverK (K ⧸ Y) := i227m_fiCoverK_quotient hK Y (i227m_primeCore_three_le_five hK)
  obtain ⟨hPb3, hPbcard⟩ := i227m_sylow_map hP3 hPcard Y
  have hcore := i227m_core hCop hComps hRank hU hFi hK' (i227m_primeCore_three_quotient K) hPb3
    hPbcard
  exact hCop K Y CFSG.pPrimeCore_coprime_card P hP3
    (i227m_three_le_pRank_of_sylow (i227m_five_le_pRank hK) hPcard) hcore

end CFSG.HardMathSupport.Solomon.Coordinator
