module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevHasBN
public import CFSG.Milestones.ASVolI.I2
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BNConj
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient

public section

namespace CFSG.GroupTheory

theorem gomiChevHasBN_holds :
    GomiChevHasBN := by
  intro X _ _ hX ⟨t, n, f, ht, hM⟩ Q
  obtain ⟨B₀, N₀, h₀⟩ := CFSG.ASVolI.ChIJK.lieModel_has_splitBNPair Nat.prime_two ht hM
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X :=
    (QuotientGroup.ker_mk' (Subgroup.center X)).le
  have hcop : ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (Subgroup.center X)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.1 hX.coprime_card_center.symm
  have hcomap : CFSG.ASVolI.ChIJK.IsSplitBNPair 2
      (B₀.comap (QuotientGroup.mk' (Subgroup.center X)))
      (N₀.comap (QuotientGroup.mk' (Subgroup.center X))) :=
    CFSG.ASVolI.ChIJK.burnsideI2BN_comap Nat.prime_two h₀ (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective (Subgroup.center X)) hker hcop
  obtain ⟨B', N', hBN', -, hNB, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22k108bn_exists_conj_split hcomap Q.isPGroup'
      Q.not_dvd_index
  subst hNB
  have hPre := CFSG.ASVolI.ChIJK.burnsideI2BN_toPre hBN'
  have : (CFSG.GH74.BNPair.cartan (Subgroup.normalizer ((Q : Subgroup X) : Set X)) N').Normal :=
    hPre.normal_inter
  obtain ⟨S, hS⟩ := CFSG.ASVolI.ChIJK.burnsideI2BN_exists_isBNPair hPre
  exact ⟨N', this, S, hS⟩

end CFSG.GroupTheory
