module

public import CFSG.GroupTheory.WeirSylow.CrossRankForms
public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.KF.ClsSpWit
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.SectionRank

theorem twoLocalPrimeRank_statedSp_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ p : ℕ} (hℓ : 1 ≤ ℓ) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1) :
    GLATwoLocalRank p ↥(StatedSp ℓ F) = ℓ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hq2 : 1 ≤ Nat.card F := Nat.card_pos
  have hp_sq : p ∣ Nat.card F ^ 2 - 1 := by
    obtain ⟨n, hn⟩ : ∃ n, Nat.card F = n + 1 := ⟨Nat.card F - 1, by omega⟩
    have h : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      rw [hn]
      have : (n + 1) ^ 2 - 1 = n * (n + 2) := by
        have h := Nat.sq_sub_sq (n + 1) 1
        simp only [Nat.one_pow] at h
        rw [h]
        have h1 : n + 1 - 1 = n := by omega
        rw [h1]
        ring
      simpa using this
    rw [h]
    exact dvd_mul_of_dvd_left hpq _
  have htop : CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSp ℓ F)) = ℓ :=
    CFSG.GroupTheory.WeirSylow.pRank_top_statedSp_eq_of_dvd (K := F) hodd hp_sq ℓ
  have hle : GLATwoLocalRank p ↥(StatedSp ℓ F) ≤ ℓ := by
    change CFSG.Open.twoLocalPrimeRank p ↥(StatedSp ℓ F) ≤ ℓ
    have hne : ({k | ∃ H : Subgroup ↥(StatedSp ℓ F), IsTwoLocal H ∧
        CFSG.Open.pRank p H = k} : Set ℕ).Nonempty :=
      ⟨_, Subgroup.normalizer
          ((CFSG.SignalizerFunctorTheorem.NonLocal.spSiegel ℓ F : Subgroup ↥(StatedSp ℓ F)) :
            Set ↥(StatedSp ℓ F)),
        ⟨CFSG.SignalizerFunctorTheorem.NonLocal.spSiegel ℓ F,
          CFSG.LocalAnalysis.GLTheoremA.spSiegel_ne_bot (F := F) hℓ,
          CFSG.LocalAnalysis.GLTheoremA.isPGroup_spSiegel (F := F) ℓ, rfl⟩, rfl⟩
    refine csSup_le hne ?_
    rintro k ⟨H, hH, hk⟩
    rw [← hk]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : H ≤ ⊤)).trans (le_of_eq htop)
  have hge : ℓ ≤ GLATwoLocalRank p ↥(StatedSp ℓ F) := by
    have h1 : ℓ ≤ CFSG.Assembly.RankThreeEven.localRank p
        (CFSG.Open.StatedProj (StatedSp ℓ F)) := by
      refine CFSG.RankThree.PartOne.KFU.le_localRank_statedSp_torus (K := F) hp hp2 ?_ hℓ
      rw [Nat.card_units]
      exact hpq
    rwa [CFSG.RankThree.PartOne.KFU.localRank_statedProj_eq hℓ hp] at h1
  exact le_antisymm hle hge

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
