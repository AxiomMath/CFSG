module

public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TInd
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FPar

open CFSG.Open

theorem commute_of_pPrime_normal_of_le_layer {S : Type} [Group S] [Finite S] {p : ℕ}
    {W P M : Subgroup S} (hP : IsSubnormal P W) (hperf : ⁅P, P⁆ = P) (hPL : P ≤ GLALayer W)
    (hres : ∀ N : Subgroup S, N ≤ P → (N.subgroupOf P).Normal → Nat.Coprime p (N.relIndex P) →
      N = P)
    (hMP : M ≤ P) (hMn : (M.subgroupOf P).Normal) (hMp : Nat.Coprime p (Nat.card M)) :
    ∀ m ∈ M, ∀ x ∈ P, m * x = x * m := by
  classical
  have hPeq := CFSG.StandardType.eq_sSup_components_of_perfect_isSubnormal hP hperf hPL
  have hMsn : IsSubnormal M W := IsSubnormal.step hMP hMn hP
  have hMW : M ≤ W := hMP.trans (IsSubnormal.le hP)
  have hkey : ∀ K : Subgroup S, IsComponentOf K W → K ≤ P → ⁅K, M⁆ = ⊥ := by
    intro K hK hKP
    rcases CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_comp_le_or_comm hK hMW hMsn with
      hKM | hcomm
    · exfalso
      have hKp : Nat.Coprime p (Nat.card K) :=
        hMp.coprime_dvd_right (Subgroup.card_dvd_of_le hKM)
      have hKN : P ≤ Subgroup.normalizer (K : Set S) :=
        hPL.trans (CFSG.StandardType.GLALayer_le_normalizer_of_isComponentOf hK)
      have hKn : (K.subgroupOf P).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mpr hKN
      set C : Subgroup S := P ⊓ Subgroup.centralizer (K : Set S) with hCdef
      have hCP : C ≤ P := by
        rw [hCdef]
        exact inf_le_left
      have hCnormK : C ≤ Subgroup.normalizer (K : Set S) := by
        rw [hCdef]
        exact (inf_le_right : P ⊓ Subgroup.centralizer (K : Set S) ≤
          Subgroup.centralizer (K : Set S)).trans (Subgroup.centralizer_le_normalizer _)
      have hCn : (C.subgroupOf P).Normal := by
        refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
        rw [hCdef]
        refine (le_inf Subgroup.le_normalizer ?_).trans
          Subgroup.inf_normalizer_le_normalizer_inf
        exact hKN.trans (CFSG.Walter.Huppert.normalizer_le_normalizer_centralizer K)
      have hsup : C ⊔ K = P := by
        rw [sup_comm]
        refine le_antisymm (sup_le hKP hCP) ?_
        rw [hPeq]
        refine sSup_le fun K' hK' => ?_
        by_cases hK'K : K' = K
        · rw [hK'K]
          exact le_sup_left
        · rcases CFSG.LocalAnalysis.GLTheoremA.I142N.isComponent_commute_or_eq hK'.1 hK with
            hEq | hcomm'
          · exact absurd hEq hK'K
          · have hle : K' ≤ C := by
              rw [hCdef]
              exact le_inf hK'.2 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm')
            exact hle.trans le_sup_right
      have hidx : Nat.Coprime p (C.relIndex P) := by
        have hidxeq : C.relIndex P = C.relIndex K := by
          rw [← hsup]
          exact (CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer
            hCnormK).symm
        refine hKp.coprime_dvd_right ?_
        rw [hidxeq]
        exact Subgroup.relIndex_dvd_card C K
      have hCPeq : C = P := hres C hCP hCn hidx
      have hKcent : K ≤ Subgroup.centralizer (K : Set S) := by
        intro x hx
        have hxP : x ∈ P := hKP hx
        rw [← hCPeq] at hxP
        exact hxP.2
      obtain ⟨a, b, hab⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_exists_noncomm_of_isQuasisimple hK.2.2
      refine hab (Subtype.ext ?_)
      show (a : S) * (b : S) = (b : S) * (a : S)
      exact (Subgroup.mem_centralizer_iff.1 (hKcent a.2) (b : S) b.2).symm
    · exact hcomm
  have hPle : P ≤ Subgroup.centralizer (M : Set S) := by
    rw [hPeq]
    exact sSup_le fun K hK =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hkey K hK.1 hK.2)
  intro m hm x hx
  exact Subgroup.mem_centralizer_iff.1 (hPle hx) m hm

theorem odd_card_of_commute_of_isSubnormal {S : Type} [Group S] [Finite S]
    {W P M : Subgroup S} (hP : IsSubnormal P W) (hO : pCoreOf 2 W = ⊥) (hMP : M ≤ P)
    (hMc : ∀ m ∈ M, ∀ x ∈ P, m * x = x * m) : Odd (Nat.card M) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨m, hmord⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  have hmP : (m : S) ∈ P := hMP m.2
  have hm2 : (m : S) ^ 2 = 1 := by
    have h1 := congrArg (fun t : ↥M => (t : S)) (pow_orderOf_eq_one m)
    rw [hmord] at h1
    simpa using h1
  have hmne : (m : S) ≠ 1 := by
    intro h1
    have hm1 : (m : ↥M) = 1 := Subtype.ext (by simpa using h1)
    rw [hm1, orderOf_one] at hmord
    omega
  have hordS : orderOf (m : S) = 2 := orderOf_eq_prime hm2 hmne
  have hK2 : IsPGroup 2 (Subgroup.zpowers (m : S)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hordS]
    norm_num
  have hKP : Subgroup.zpowers (m : S) ≤ P := by
    rw [Subgroup.zpowers_le]
    exact hmP
  have hKcent : Subgroup.zpowers (m : S) ≤ Subgroup.centralizer (P : Set S) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hMc (m : S) m.2 x hx).symm
  have hKn : ((Subgroup.zpowers (m : S)).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mpr
      ((Subgroup.le_centralizer_iff.mpr hKcent).trans (Subgroup.centralizer_le_normalizer _))
  have hcore := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2
    (IsSubnormal.step hKP hKn hP) hK2
  rw [hO] at hcore
  exact hmne (Subgroup.mem_bot.mp (hcore (Subgroup.mem_zpowers (m : S))))

end CFSG.LocalAnalysis.GLTheoremA.I141FPar

end
