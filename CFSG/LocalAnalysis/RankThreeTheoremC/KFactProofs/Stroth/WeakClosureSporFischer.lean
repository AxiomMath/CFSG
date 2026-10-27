module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporModule
public import CFSG.Permutation.SymmetricCoxeter
public import Certificates.Certificate1005
public import Certificates.Certificate1012
public import Certificates.Certificate1016
public import Certificates.Certificate1018
public import Certificates.Certificate2070
public import Certificates.Certificate3037
public import Certificates.Certificate3039
public import Certificates.Certificate3147
public import Certificates.Certificate3152
public import Certificates.Certificate3153
public import Certificates.Certificate9107
public import Certificates.Certificate9108
public import Certificates.Certificate9109
public import Certificates.Certificate9110
public import Certificates.Certificate9205
public import Certificates.Certificate9486
public import Certificates.Certificate9507
public import Certificates.Certificate9550
public import Certificates.Certificate9551
public import Certificates.Certificate9552
public import Certificates.Certificate9595
public import Certificates.Certificate9602
public import Certificates.Certificate10087
import CFSG.HardMathSupport.Foote.E27.SporFi23
import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi22
import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMain
import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg
import CFSG.RankThree.PartOne.CTP.SporadicNoncommFi24
import CFSG.Sporadic.Bridge.Fi22Surj
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.Fi23.S12
import CFSG.Sporadic.Fi23.Simple
import CFSG.Sporadic.Fi24.ExtFi23
import CFSG.Sporadic.Fi24.Simple
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate1018Base
public import Certificates.Certificate3152Base
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.Monster.B.Fischer.Fi22Centralizer
import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open
open CFSG.HardMathSupport.Timmesfeld.SporadicRank
open scoped commutatorElement

set_option maxRecDepth 4000

theorem alt12_inj_of_ne {H : Type*} [Group H] (ψ : Equiv.Perm (Fin 12) →* H)
    {σ : Equiv.Perm (Fin 12)} (hσ : σ ∈ alternatingGroup (Fin 12)) (hne : ψ σ ≠ 1) :
    ∀ τ ∈ alternatingGroup (Fin 12), ψ τ = 1 → τ = 1 := by
  have : IsSimpleGroup (alternatingGroup (Fin 12)) :=
    alternatingGroup.isSimpleGroup (by simp)
  intro τ hτ hτ1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (ψ.comp (alternatingGroup (Fin 12)).subtype).ker with h | h
  · have : (⟨τ, hτ⟩ : alternatingGroup (Fin 12)) ∈
        (ψ.comp (alternatingGroup (Fin 12)).subtype).ker := hτ1
    rw [h] at this
    exact congrArg Subtype.val (Subgroup.mem_bot.1 this)
  · exfalso
    have h1 : (ψ.comp (alternatingGroup (Fin 12)).subtype) ⟨σ, hσ⟩ = 1 :=
      MonoidHom.mem_ker.1 (by rw [h]; exact Subgroup.mem_top _)
    exact hne h1

theorem wcOn_five_of_alt12 {K : Type} [Group K] [Finite K] (Φ : Equiv.Perm (Fin 12) →* K)
    (hinj : ∀ σ ∈ alternatingGroup (Fin 12), Φ σ = 1 → σ = 1) (h3 : ¬ 5 ^ 3 ∣ Nat.card K) :
    WCOn 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let x : Equiv.Perm (Fin 12) := List.formPerm [0, 1, 2, 3, 4]
  let y : Equiv.Perm (Fin 12) := List.formPerm [5, 6, 7, 8, 9]
  let h : Equiv.Perm (Fin 12) := List.formPerm [0, 5] * List.formPerm [1, 6, 2, 7, 4, 9, 3, 8]
  have hx5 : x ^ 5 = 1 := by decide +kernel
  have hxy : x * y = y * x := by decide +kernel
  have hhx : h * x * h⁻¹ = y := by decide +kernel
  have hhy : h * y * h⁻¹ = x ^ 2 * y ^ 0 := by decide +kernel
  have hx1 : x ≠ 1 := by decide +kernel
  have hxA : x ∈ alternatingGroup (Fin 12) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  refine WCOn.of_conj_pair (a := Φ x) (b := Φ y) (g := Φ h) ?_ ?_ ?_ ?_ (c := 2) (d := 0) ?_ h3
    (by decide +revert)
  · intro hc
    exact hx1 (hinj x hxA hc)
  · rw [← map_pow, hx5, map_one]
  · rw [← map_mul, ← map_mul, hxy]
  · rw [← map_mul, ← map_inv, ← map_mul, hhx]
  · rw [← map_mul, ← map_inv, ← map_mul, hhy, map_mul, map_pow, map_pow]

@[expose] def sigmaTwo : Equiv.Perm (Fin 12) :=
  CFSG.Permutation.SymmetricCoxeter.adjSwap 11 0 * CFSG.Permutation.SymmetricCoxeter.adjSwap 11 2

theorem sigmaTwo_mem : sigmaTwo ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold sigmaTwo
  rw [CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt (n := 11) (i := 0) (by norm_num),
    CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt (n := 11) (i := 2) (by norm_num)]
  decide

theorem wcOn_five_of_sym12 {K J : Type} [Group K] [Finite K] [Group J]
    (ψ : Equiv.Perm (Fin 12) →* J) (hne : ψ sigmaTwo ≠ 1) (e : J ≃* K)
    (h3 : ¬ 5 ^ 3 ∣ Nat.card K) : WCOn 5 K := by
  have hinj1 := alt12_inj_of_ne ψ sigmaTwo_mem hne
  exact wcOn_five_of_alt12 (e.toMonoidHom.comp ψ) (fun σ hσ h1 => hinj1 σ hσ
    ((map_eq_one_iff e.toMonoidHom e.injective).1 h1)) h3

theorem wcOn_five_of_sym12_sub {K J A G : Type} [Group K] [Finite K] [Group J] [Group A]
    [Group G] (ψ : Equiv.Perm (Fin 12) →* J) (hne : ψ sigmaTwo ≠ 1) (e₁ : J ≃* A)
    (M : Subgroup G) (e₂ : A ≃* M) (e₃ : G ≃* K) (h3 : ¬ 5 ^ 3 ∣ Nat.card K) : WCOn 5 K := by
  have hinj1 := alt12_inj_of_ne ψ sigmaTwo_mem hne
  refine wcOn_five_of_alt12
    (e₃.toMonoidHom.comp (M.subtype.comp (e₂.toMonoidHom.comp (e₁.toMonoidHom.comp ψ))))
    (fun σ hσ h1 => hinj1 σ hσ ?_) h3
  have h2 := (map_eq_one_iff e₃.toMonoidHom e₃.injective).1 h1
  have h3' := (map_eq_one_iff M.subtype M.subtype_injective).1 h2
  have h4 := (map_eq_one_iff e₂.toMonoidHom e₂.injective).1 h3'
  exact (map_eq_one_iff e₁.toMonoidHom e₁.injective).1 h4

theorem wcOn_Fi22_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.Fi22] : WCOn 3 CFSG.Blueprint.NativeSporadic.Fi22 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Nat.card CFSG.Blueprint.NativeSporadic.Fi22 = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  have hf : (Nat.card CFSG.Blueprint.NativeSporadic.Fi22).factorization 3 = 9 := by
    rw [hN]
    exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
  exact wcOn_of_sylowModuleData (X := CFSG.Blueprint.NativeSporadic.Fi22) sylowData_Fi22
    (by rw [hf]; norm_num)

theorem wcOn_Fi22_three
    [Finite (Carrier .Fi22)] : WCOn 3 (Carrier .Fi22) :=
  wcOn_Fi22_three_aux

theorem wcOn_Fi22_five_of_equiv
    {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) (hcard : Nat.card K = 64561751654400) :
    WCOn 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine WCOn.of_normalizer_invariant 24 (fun P => ?_) (fun P O hO hinv => ?_)
  · rw [card_sylow_eq_pow (a := 2) hcard Nat.prime_five (by norm_num) (by norm_num) P]
    norm_num
  · have := CFSG.AGLEmbedding.kFactFi22Orbits K ⟨e⟩ P O hO hinv
    simpa using this

theorem wcOn_Fi22_five
    [Finite (Carrier .Fi22)] : WCOn 5 (Carrier .Fi22) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact wcOn_Fi22_five_of_equiv e CFSG.Sporadic.Fi22.card_Fi22

theorem wcSporadicAt_Fi22
    [Finite (Carrier .Fi22)] :
    WCSporadicAt .Fi22 := by
  refine wcSporadicAt_of_card .Fi22 (N := 64561751654400) CFSG.Sporadic.Fi22.card_Fi22 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 64561751654400 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Fi22_three
  · exact wcOn_Fi22_five
  all_goals (exfalso; norm_num at hdvd)

theorem wcOn_Fi23_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.Fi23] : WCOn 3 CFSG.Blueprint.NativeSporadic.Fi23 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  open CFSG.HardMathSupport.Foote.E27.Fi23 in
  have hz : ⁅q 0, q 1⁆ = zq := by
    have h := conj_chain 0 1 (by decide)
    have hM : (MFi 0 1).val = 1 := by decide +kernel
    rw [hM, pow_one] at h
    rw [commutatorElement_def, h]
    exact conj_zq 1
  open CFSG.HardMathSupport.Foote.E27.Fi23 in
  exact WCOn.of_hasNoncommPair
    (CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_of_central_commutator Nat.prime_three
      (q_pow 0) (q_pow 1) (by rw [hz]; exact zq_ne_one) (by rw [hz]; exact (comm_zq 0).symm)
      (by rw [hz]; exact (comm_zq 1).symm))

theorem wcOn_Fi23_five_aux
    [Finite CFSG.Blueprint.NativeSporadic.Fi23] : WCOn 5 CFSG.Blueprint.NativeSporadic.Fi23 := by
  obtain ⟨ψ, hψ⟩ := CFSG.Sporadic.Fi23.exists_hom_s12
  have hψ2 : ψ sigmaTwo = CFSG.Sporadic.Fi23.sEl 0 * CFSG.Sporadic.Fi23.sEl 2 := by
    rw [sigmaTwo, map_mul, hψ 0 (by norm_num), hψ 2 (by norm_num)]
  have hne : ψ sigmaTwo ≠ 1 := by
    rw [hψ2]
    exact CFSG.Sporadic.Fi23.sEl_zero_mul_two_ne_one
  exact wcOn_five_of_sym12 ψ hne CFSG.Sporadic.Fi23.fi23EquivJ.symm
    (by rw [CFSG.Sporadic.Fi23.card_Fi23]; norm_num)

theorem wcSporadicAt_Fi23
    [Finite (Carrier .Fi23)] : WCSporadicAt .Fi23 := by
  refine wcSporadicAt_of_card .Fi23 (N := 4089470473293004800) CFSG.Sporadic.Fi23.card_Fi23 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 4089470473293004800 = {2, 3, 5, 7, 11, 13, 17, 23} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Fi23_three_aux
  · exact wcOn_Fi23_five_aux
  all_goals (exfalso; norm_num at hdvd)

theorem wcOn_Fi24_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.Fi24prime] :
    WCOn 3 CFSG.Blueprint.NativeSporadic.Fi24prime := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have hf : (Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime).factorization 3 = 16 := by
    rw [hN]
    exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
  exact wcOn_of_sylowModuleCover (X := CFSG.Blueprint.NativeSporadic.Fi24prime) sylowCover_Fi24
    (by rw [hf]; norm_num)

theorem wcOn_Fi24_five_aux
    [Finite CFSG.Blueprint.NativeSporadic.Fi24prime] :
    WCOn 5 CFSG.Blueprint.NativeSporadic.Fi24prime := by
  obtain ⟨ψ, hψ⟩ := CFSG.Sporadic.Fi23.exists_hom_s12
  have hψ2 : ψ sigmaTwo = CFSG.Sporadic.Fi23.sEl 0 * CFSG.Sporadic.Fi23.sEl 2 := by
    rw [sigmaTwo, map_mul, hψ 0 (by norm_num), hψ 2 (by norm_num)]
  have hne : ψ sigmaTwo ≠ 1 := by
    rw [hψ2]
    exact CFSG.Sporadic.Fi23.sEl_zero_mul_two_ne_one
  have h3 : ¬ 5 ^ 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime := by
    rw [CFSG.Sporadic.Fi24.card_Fi24prime]
    norm_num
  refine wcOn_five_of_sym12_sub (J := CFSG.Sporadic.Fi23.J)
    (A := CFSG.Blueprint.NativeSporadic.Fi23) (G := CFSG.Sporadic.Fi24.J) ψ hne ?_
    CFSG.Sporadic.Fi24.M ?_ ?_ h3
  · exact CFSG.Sporadic.Fi23.fi23EquivJ.symm
  · exact CFSG.Sporadic.Fi24.fi23Equiv.symm
  · exact CFSG.Sporadic.Fi24.fi24EquivJ.symm

theorem wcOn_Fi24_seven_aux
    [Finite CFSG.Blueprint.NativeSporadic.Fi24prime] :
    WCOn 7 CFSG.Blueprint.NativeSporadic.Fi24prime := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Fi24_seven

theorem wcSporadicAt_Fi24Prime
    [Finite (Carrier .Fi24Prime)] : WCSporadicAt .Fi24Prime := by
  refine wcSporadicAt_of_card .Fi24Prime (N := 1255205709190661721292800)
    CFSG.Sporadic.Fi24.card_Fi24prime ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 1255205709190661721292800 = {2, 3, 5, 7, 11, 13, 17, 23, 29} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Fi24_three_aux
  · exact wcOn_Fi24_five_aux
  · exact wcOn_Fi24_seven_aux
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
