module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC

theorem invariantTwoJoin_le_relPPrimeCore {X : Type} [Group X] [Finite X] {p : ℕ}
    {L D : Subgroup X} [L.Normal] (hF : ThompsonFrame p D) {d : X} (hd : d ∈ D) (hd1 : d ≠ 1) :
    invariantTwoJoinIn D (L ⊓ Subgroup.centralizer ({d} : Set X)) ≤
      relPPrimeCore p (L ⊓ Subgroup.centralizer ({d} : Set X)) := by
  obtain ⟨O, hO⟩ := hF.signalizer d hd hd1
  have hjoin : invariantTwoJoinIn D (L ⊓ Subgroup.centralizer ({d} : Set X)) ≤
      O ⊓ (L ⊓ Subgroup.centralizer ({d} : Set X)) := by
    refine invariantTwoJoinIn_le_of_forall fun W hWH hW2 hDW => ?_
    refine le_inf (hO.le W (hWH.trans inf_le_right) ?_ hDW) hWH
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hW2
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hF.prime Nat.prime_two).2 hF.odd)
  refine hjoin.trans ?_
  unfold relPPrimeCore
  refine le_sSup ⟨inf_le_right, ?_, ?_⟩
  ·
    refine (Subgroup.normal_subgroupOf_iff inf_le_right).2 fun h k hh hk => ?_
    have hhO := Subgroup.mem_inf.mp hh
    have hkC : k ∈ Subgroup.centralizer ({d} : Set X) := (Subgroup.mem_inf.mp hk).2
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hO.normal hkC) h).mp hhO.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hhO.2) (Subgroup.inv_mem _ hk)
  ·
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hO.coprime

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
