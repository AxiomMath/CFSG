module

public import CFSG.Sporadic.SmallOddCore.McLWordBound
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.OneClass
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std

theorem isConj_of_involutions_mcl
    {u v : NativeSporadic.McL} (hu : orderOf u = 2) (hv : orderOf v = 2) : IsConj u v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ x : NativeSporadic.McL, orderOf x = 2 →
      orderOf (CFSG.Sporadic.Schreier.mclPermEquiv x) = 2 := by
    intro x hx
    have hx2 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have hx1 : x ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hx
      exact absurd hx (by decide)
    have hsq : (CFSG.Sporadic.Schreier.mclPermEquiv x) ^ 2 = 1 := by
      rw [← map_pow, hx2, map_one]
    have hne : CFSG.Sporadic.Schreier.mclPermEquiv x ≠ 1 := fun h' =>
      hx1 (CFSG.Sporadic.Schreier.mclPermEquiv.injective (by rw [h', map_one]))
    exact orderOf_eq_prime hsq hne
  obtain ⟨g, hg⟩ := CFSG.Sporadic.SmallOddCore.mcl_involution_conj_a (hord u hu)
  obtain ⟨h, hh⟩ := CFSG.Sporadic.SmallOddCore.mcl_involution_conj_a (hord v hv)
  refine isConj_iff.2 ⟨CFSG.Sporadic.Schreier.mclPermEquiv.symm (h * g⁻¹),
    CFSG.Sporadic.Schreier.mclPermEquiv.injective ?_⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [hg, hh]
  group

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end CFSG.EvenSporadicStandard.McLStd
