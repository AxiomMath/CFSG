module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem commutator_le_centMod_of_map {X Q : Type} [Group X] [Finite X] [Group Q] (φ : X →* Q)
    (hker : Nat.Coprime 3 (Nat.card φ.ker)) {K T B : Subgroup X}
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (h : ∀ z ∈ (⁅T, B⁆ : Subgroup X), ∀ l ∈ K, φ z * φ l = φ l * φ z) :
    (⁅T, B⁆ : Subgroup X) ≤ centModSubgroup 3 K := by
  intro z hz
  have hzN : z ∈ Subgroup.normalizer (K : Set X) := by
    have hle : (⁅T, B⁆ : Subgroup X) ≤ Subgroup.normalizer (K : Set X) := by
      rw [Subgroup.commutator_le]
      intro t ht b hb
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTN ht) (hBN hb))
        (Subgroup.inv_mem _ (hTN ht))) (Subgroup.inv_mem _ (hBN hb))
    exact hle hz
  refine ⟨hzN, fun l hl => ?_⟩
  have h1 : ⁅l, z⁆ ∈ K := by
    have hz' : z * l⁻¹ * z⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hzN l⁻¹).mp (K.inv_mem hl)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc z]
    exact K.mul_mem hl hz'
  have h2 : ⁅l, z⁆ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (h z hz l hl).symm
  set N : Subgroup ↥K := φ.ker.subgroupOf K with hNdef
  have hNn : N.Normal := (MonoidHom.normal_ker φ).subgroupOf K
  have hNc : Nat.Coprime 3 (Nat.card N) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hker
    let ι : ↥N →* ↥φ.ker :=
      { toFun := fun n => ⟨((n : ↥K) : X), Subgroup.mem_subgroupOf.mp n.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective ι fun a b hab => ?_
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hle : N ≤ GLAPPrimeCore 3 ↥K := le_sSup ⟨hNn, hNc⟩
  have hmem : (⟨⁅l, z⁆, h1⟩ : ↥K) ∈ N := Subgroup.mem_subgroupOf.mpr h2
  exact ⟨⟨⁅l, z⁆, h1⟩, hle hmem, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.T158

end
