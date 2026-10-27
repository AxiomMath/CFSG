module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeSplit
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import Mathlib.FieldTheory.Finite.Extension
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup baseChangeGL finite_graph_field_parameter_fields
  map_baseChangeGL_graphFixedRootGroup_le baseChangeGL_injective)


theorem td4InnThreeCentLe_holds : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f := by
  intro f hf K _ _ σ hK hσ z hz3 hz1
  classical
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have hK' : Nat.card (FiniteField.Extension K 2 2) = (2 ^ (2 * f)) ^ 3 := by
    rw [FiniteField.natCard_extension, hK, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two
    (by omega : 1 ≤ 2 * f) (FiniteField.Extension K 2 2) hK'
  set Fr : FiniteField.Extension K 2 2 ≃+* FiniteField.Extension K 2 2 := σ'.trans σ' with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ (2 * f)) ^ 2 := fun c => by
    show σ' (σ' c) = _
    rw [hσ', hσ', ← pow_mul, sq]
  set ι : K →+* FiniteField.Extension K 2 2 := algebraMap K (FiniteField.Extension K 2 2) with hι
  have hcomm : ∀ c, Fr (ι c) = ι (σ c) := fun c => by
    rw [hFr, hσ, ← map_pow]
    have h4 : (2 ^ (2 * f)) ^ 2 = (2 ^ f) ^ 3 * 2 ^ f := by ring
    have h3 : ∀ d : K, d ^ (2 ^ f) ^ 3 = d := fun d => by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rw [h4, pow_mul, h3]
  have hstd : TD4Le.Std (2 * f) (FiniteField.Extension K 2 2) Fr := ⟨by omega, hK', Or.inr hFr⟩
  have hQ : 2 ^ (2 * f) % 3 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have hle : (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).map
      (baseChangeGL (τ := TwistTag.D4.tag) ι) ≤
      graphFixedRootGroup TwistTag.D4 (FiniteField.Extension K 2 2) Fr.toRingHom :=
    map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.D4) σ.surjective hcomm
  let ψ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      ↥(graphFixedRootGroup TwistTag.D4 (FiniteField.Extension K 2 2) Fr.toRingHom) :=
    ((baseChangeGL (τ := TwistTag.D4.tag) ι).comp
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype).codRestrict _
      (fun g => hle ⟨g, g.2, rfl⟩)
  have hψ : Function.Injective ψ := fun g g' h =>
    Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))
  have h1 := TD4Le.two_part_centralizer_le_of_injective ψ hψ z
  have hz3' : (ψ z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz1' : ψ z ≠ 1 := fun h => hz1 (hψ (by rw [h, map_one]))
  have h2 := TD4Le.two_part_centralizer_le_cube Fr hstd hQ (ψ z) hz3' hz1'
  show 2 ^ (Nat.card (Subgroup.centralizer ({z} : Set _))).factorization 2 ≤ (2 ^ f) ^ 6
  refine h1.trans (h2.trans ?_)
  rw [← pow_mul, ← pow_mul]
  exact le_of_eq (by congr 1; ring)

end CFSG.LocalAnalysis.GLTheoremA

end
