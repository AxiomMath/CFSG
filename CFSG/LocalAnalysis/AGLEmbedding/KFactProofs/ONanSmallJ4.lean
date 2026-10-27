module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape
public import CFSG.RankThree.PartTwo.Census.Sporadic.J4Bridge
public import CFSG.Sporadic.Schreier.J4SEleven

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier

theorem nonempty_equiv_j4
    {K : Type} [Group K] (hs : IsSimpleGroup K) (hK : IsSporadicGroup .J4 K) :
    Nonempty (K ≃* CFSG.Sporadic.J4.J) := by
  obtain ⟨e⟩ := hK
  have := hs
  have : IsSimpleGroup TauCeti.SporadicName.J4.Group := e.symm.isSimpleGroup
  obtain ⟨β⟩ := CFSG.RankThree.PartTwo.Census.nonempty_mulEquiv_carrier_J4
  exact ⟨((e.trans β).trans (seedEquiv j4Facts.mat))⟩

theorem exists_sylow_exp_j4 :
    ∃ S : Sylow 11 CFSG.Sporadic.J4.J, ∀ s ∈ (S : Subgroup CFSG.Sporadic.J4.J), s ^ 11 = 1 := by
  obtain ⟨x, y, z, h₁, h₂, c, ⟨S, hS⟩, -, -, hexp, -⟩ :=
    R3E_J4_eleven_normalizer_transitivity_and_fixed_dimensions
  refine ⟨S, fun s hs' => ?_⟩
  rw [hS] at hs'
  have h11 : (⟨s, hs'⟩ : Subgroup.closure ({x, y} : Set CFSG.Sporadic.J4.J)) ^ 11 = 1 := by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one _
  have h12 := congrArg Subtype.val h11
  rw [Subgroup.coe_pow, Subgroup.coe_one] at h12
  exact h12

theorem sylowCube_of_isJ4
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hK : IsSporadicGroup .J4 K) : SylowCube 11 K := by
  obtain ⟨e⟩ := nonempty_equiv_j4 hs hK
  have hfin : Finite CFSG.Sporadic.J4.J := Finite.of_equiv K e.toEquiv
  have hcard : Nat.card K = 11 ^ 3 * 65195770883604480 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (seedEquiv j4Facts.mat).symm.toEquiv]
    exact card_J4
  obtain ⟨S, hS⟩ := exists_sylow_exp_j4
  have h1 := @sylowCube_of_equiv K _ _ 11 CFSG.Sporadic.J4.J _ _ 65195770883604480
    (by norm_num) e hcard
  exact h1 (by omega) S hS

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
