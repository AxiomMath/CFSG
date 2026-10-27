module

public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.RankThree.PerfectCover CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Multiplier

theorem card_center_dvd_hopf {L X : Type} [Group L] [Finite L] [Group X] (hL : CFSG.IsQuasisimple L)
    (e : L ⧸ center L ≃* X) [Finite (CFSG.Open.griessHopfMultiplier X)] :
    Nat.card (center L) ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
  have : Group.IsPerfect L := hL.1
  let q := centralQuotientMap e
  have hq : Function.Surjective q := centralQuotientMap_surjective e
  have hk : q.ker = center L := centralQuotientMap_ker e
  have : Finite X := finite_of_surjective_monoidHom q hq
  have : Group.IsPerfect X := isPerfect_of_quasisimple_quotient hL e
  let ψ : hopfMultiplier X →* q.ker := hopfMultiplierToKer q hq hk.le
  have hψ : Function.Surjective ψ := hopfMultiplierToKer_surjective q hq hk.le
  have h1 : Nat.card q.ker ∣ Nat.card (hopfMultiplier X) := Subgroup.card_dvd_of_surjective hψ
  have h2 : Nat.card (hopfMultiplier X) = Nat.card (CFSG.Open.griessHopfMultiplier X) :=
    (Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv).symm
  rw [← hk, ← h2]
  exact h1

theorem center_eq_bot_of_hopf_subsingleton {L X : Type} [Group L] [Finite L] [Group X]
    (hL : CFSG.IsQuasisimple L) (e : L ⧸ center L ≃* X)
    (hM : Subsingleton (CFSG.Open.griessHopfMultiplier X)) : center L = ⊥ := by
  have : Group.IsPerfect L := hL.1
  let q := centralQuotientMap e
  have hq : Function.Surjective q := centralQuotientMap_surjective e
  have hk : q.ker = center L := centralQuotientMap_ker e
  have : Finite X := finite_of_surjective_monoidHom q hq
  have : Group.IsPerfect X := isPerfect_of_quasisimple_quotient hL e
  let ψ : hopfMultiplier X →* q.ker := hopfMultiplierToKer q hq hk.le
  have hψ : Function.Surjective ψ := hopfMultiplierToKer_surjective q hq hk.le
  have hsub : Subsingleton (hopfMultiplier X) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (hopfMultiplierEquivGriess X).surjective a
    obtain ⟨b', rfl⟩ := (hopfMultiplierEquivGriess X).surjective b
    rw [Subsingleton.elim a' b']
  have : Subsingleton ↥q.ker := hψ.subsingleton
  rw [← hk]
  exact Subgroup.eq_bot_of_subsingleton _

theorem g2_center_eq_bot
    {L : Type} [Group L] [Finite L] {p f : ℕ} (hL : CFSG.IsQuasisimple L)
    (hmodel : LieModel (L ⧸ center L) .G2 0 p f) (hq : 5 ≤ p ^ f) : center L = ⊥ := by
  rcases hmodel with ⟨ht, -⟩ | ⟨-, -, hadm, hU⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hU
    have hK5 : 5 ≤ Nat.card K := by rw [hK]; exact hq
    exact center_eq_bot_of_hopf_subsingleton hL e
      (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier hK5).2
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
