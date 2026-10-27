module

public import CFSG.LieType.Chevalley.E7Three.CentralizerFixedField
public import CFSG.LieType.Chevalley.E7Three.CentralizerComponent
public import CFSG.LieType.SemisimpleCentralizers.LinearCentralizerSolvable
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.E7Three.CentralizerFour
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.SubgroupLists.CommutatorScalarBound
public import CFSG.RankThree.SubgroupLists.ExtraspecialNormal
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section
set_option autoImplicit false
namespace CFSG.LieType.Chevalley.E7Three.Centralizer
open Matrix CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KA5L
  CFSG.LieType.AlgebraicGroups CFSG.StandardType
open scoped MatrixGroups

theorem sl2_isSolvable_of_three_complement_derived
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator SL(2, K))) :
    Group.IsSolvable SL(2, K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨e, -, he⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (e : ℕ) := by simpa [Nat.card_eq_fintype_card] using he
  have hnot : ¬ 3 ∣ Nat.card K := by
    rw [hq]
    intro h
    exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hrem : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by
    have hlt := Nat.mod_lt (Nat.card K) (by decide : 0 < 3)
    have hn : Nat.card K % 3 ≠ 0 := fun hz => hnot (Nat.dvd_of_mod_eq_zero hz)
    omega
  have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by
    have hsquare : (Nat.card K ^ 2) % 3 = 1 := by
      rw [pow_two, Nat.mul_mod]
      rcases hrem with h | h <;> norm_num only [h]
    apply Nat.dvd_of_mod_eq_zero
    omega
  let T : Subgroup SL(2, K) := ⊤
  let eT : ↥T ≃* SL(2, K) := Subgroup.topEquiv
  have htriv : (MonoidHom.id SL(2, K)).range ⊓
      Subgroup.centralizer ((⊥ : Subgroup SL(2, K)) : Set SL(2, K)) = T := by
    apply le_antisymm le_top
    intro x hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    change x ∈ Subgroup.centralizer ((⊥ : Subgroup SL(2, K)) : Set SL(2, K))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = 1 := hy
    simp [hy']
  have hNPCtop : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥T) :=
    CFSG.hasNormalPComplement_of_equiv 3 eT.symm.commutatorCongr hNPC
  have hs : Group.IsSolvable ↥T := by
    have h := CFSG.LieType.SemisimpleCentralizers.isSolvable_centralizer_of_hasNormalPComplement_commutator
      (m := 1) (F := K) (G := SL(2, K)) (ψ := MonoidHom.id _) (by simp)
      Nat.prime_three (by decide) h3 (E := ⊥) IsPGroup.of_bot
      (by
        intro e he
        have he' : e = 1 := he
        subst e
        exact ⟨1, Subgroup.one_mem _⟩)
      (by
        change CFSG.HasNormalPComplement 3 ↥(_root_.commutator
          ↥((MonoidHom.id SL(2, K)).range ⊓
            Subgroup.centralizer ((⊥ : Subgroup SL(2, K)) : Set SL(2, K))))
        rw [htriv]
        exact hNPCtop)
    change Group.IsSolvable ↥((MonoidHom.id SL(2, K)).range ⊓
      Subgroup.centralizer ((⊥ : Subgroup SL(2, K)) : Set SL(2, K))) at h
    rw [htriv] at h
    exact h
  let : Group.IsSolvable ↥T := hs
  exact Group.isSolvable_of_surjective (f := eT.toMonoidHom) eT.surjective



theorem cubeCent_frobenius_isSolvable_of_three_complement
    {k : Type} [Field k] [CharP k 2] [IsAlgClosed k]
    {F : Type} [Field F] [Finite F] [Algebra F k]
    (f m : ℕ) (hf : 1 ≤ f) (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ f)
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3) (a : SL(2, k))
    (Ψ : ModGL .E7 k →* ModGL .E7 k)
    (hΔ : ∀ x : SL(2, k), Ψ (cubeSL2 k x) = cubeSL2 k
      (a * SpecialLinearGroup.map (iterateFrobenius k 2 (f * m)) x * a⁻¹))
    (hE : ∀ e ∈ cubeE ζ hζ.pow_eq_one, Ψ e = e)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _)))) :
    Group.IsSolvable ↥(cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _)) := by
  classical
  let K := (iterateFrobenius k 2 (f * m)).eqLocusField (RingHom.id k)
  let E := cubeE ζ hζ.pow_eq_one
  let D := cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _)
  obtain ⟨ρ, hρ, hcard, ⟨e⟩⟩ :=
    cubeCent_frobenius_fixed_field_extension_of_action f m hf hm hF hζ a Ψ hΔ hE
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcard, hF]
    positivity)
  have : CharP K 2 := inferInstance
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [card_cubeE hζ]; norm_num)
  have hNPCprod : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator (SL(2, K) × E)) :=
    CFSG.hasNormalPComplement_of_equiv 3 e.symm.commutatorCongr hNPC
  have hNPCsl : CFSG.HasNormalPComplement 3 ↥(_root_.commutator SL(2, K)) := by
    have h := CFSG.RankThree.Coprime.hasNormalPComplement_map
      (MonoidHom.fst SL(2, K) E) hNPCprod
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (fun x => ⟨(x, 1), rfl⟩)] at h
    exact h
  have : Group.IsSolvable SL(2, K) := sl2_isSolvable_of_three_complement_derived hNPCsl
  have : Group.IsSolvable E := Group.isSolvable_of_comm fun x y =>
    Subtype.ext (cubeE_commute x.2 y.2).eq
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

end CFSG.LieType.Chevalley.E7Three.Centralizer
