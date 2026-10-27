module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Transfer
public import CFSG.LieType.Steinberg.TwistedE6.Defs
import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.LeviBasic
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUModel
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedModel
import CFSG.LocalAnalysis.StandardType.SUCenterOdd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi

public section

namespace CFSG.GroupTheory.GomiLeviExc.TwistedE6

open Subgroup CFSG.Blueprint.Chevalley CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LocalAnalysis.ComponentInitial
  CFSG.SeitzReduction.F4Pilot CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

local instance twistedE6SU6NeZeroRank : NeZero (Tag.rank .F4) := ⟨by decide⟩

private theorem toUGroup6_injective {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (h : UnitaryFieldData 2 f F) : Function.Injective (toUGroup6 h) := by
  intro S S' hSS'
  have h1 : (((toUGroup6 h S : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      (((toUGroup6 h S' : uGroup6 h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) :=
    congrArg (fun g : uGroup6 h => ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hSS'
  rw [coe_toUGroup6, coe_toUGroup6] at h1
  have h2 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F =>
    M.submatrix graphSwapPerm graphSwapPerm) h1
  rw [submatrix_graphSwapPerm_submatrix, submatrix_graphSwapPerm_submatrix] at h2
  exact Subtype.ext (Units.ext h2)

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k} {q : ℕ}

omit [Finite k] [CharP k 2] in
private theorem twLevi_nodes_eq_leviM (θ : k →+* k) :
    twLevi k θ AmalgamNeighbour.X.nodes =
      leviM (twistedDatum k θ) (({1, 2, 3} : Finset (Fin (Tag.rank .F4))) :
        Set (Fin (Tag.rank .F4))) := by
  rw [show AmalgamNeighbour.X.nodes = ({1, 2, 3} : Finset (Fin (Tag.rank .F4))) from rfl]
  erw [leviM_coe_finset]
  rfl

theorem gomiLeviFactor_leviM_one_two_three (hk : Nat.card k = q ^ 2) (hθ : ∀ c, θ c = c ^ q) :
    GomiLeviFactor ↥(leviM (twistedDatum k θ) ({1, 2, 3} : Set (Fin (Tag.rank .F4)))) := by
  obtain ⟨f, hf, hqf⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hk
  have hFq : Nat.card k = (2 ^ f) ^ 2 := by rw [hk, hqf]
  have hUcard : Nat.card k = 2 ^ (2 * f) := by
    rw [hFq, ← pow_mul, mul_comm f 2]
  let hU : UnitaryFieldData 2 f k := ⟨Nat.prime_two, hf, hUcard⟩
  have hbar : hU.barEquiv.toRingHom = θ := by
    ext c
    change hU.barEquiv c = θ c
    rw [UnitaryFieldData.barEquiv_apply, UnitaryFieldData.bar_apply, ← hqf]
    exact (hθ c).symm
  obtain ⟨hq, hclass⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_su
      (F := k) (f := f) hFq (n' := 6) (by norm_num) (by simp)
  have hZ := CFSG.StandardType.odd_natCard_of_le_center_SU (unitaryInvolution k 2 f)
    (H := Subgroup.center (SU (unitaryInvolution k 2 f) 6)) le_rfl
  have hC :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isChevTwo_of_classicalTwoOrG2 hclass
  have hrange : ((twParamHom hU).comp (toUGroup6 hU)).range =
      twLevi k hU.barEquiv.toRingHom AmalgamNeighbour.X.nodes := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (toUGroup6_surjective hU),
      ← MonoidHom.range_eq_map, range_twParamHom hU]
  have hset : (({1, 2, 3} : Finset (Fin (Tag.rank .F4))) : Set (Fin (Tag.rank .F4))) =
      ({1, 2, 3} : Set (Fin (Tag.rank .F4))) := by
    ext i
    simp
  have hA : twLevi k hU.barEquiv.toRingHom AmalgamNeighbour.X.nodes =
      leviM (twistedDatum k hU.barEquiv.toRingHom) (({1, 2, 3} : Finset (Fin (Tag.rank .F4))) :
        Set (Fin (Tag.rank .F4))) :=
    twLevi_nodes_eq_leviM hU.barEquiv.toRingHom
  have hrange' : ((twParamHom hU).comp (toUGroup6 hU)).range =
      leviM (twistedDatum k hU.barEquiv.toRingHom) (({1, 2, 3} : Finset (Fin (Tag.rank .F4))) :
        Set (Fin (Tag.rank .F4))) :=
    hrange.trans hA
  have hinj : Function.Injective ((twParamHom hU).comp (toUGroup6 hU)) :=
    fun _ _ h => toUGroup6_injective hU (twParamHom_injective hU h)
  rw [← hbar, ← hset]
  exact gomiLeviFactor_of_injective hq hZ hC ((twParamHom hU).comp (toUGroup6 hU)) hinj hrange'

end CFSG.GroupTheory.GomiLeviExc.TwistedE6
