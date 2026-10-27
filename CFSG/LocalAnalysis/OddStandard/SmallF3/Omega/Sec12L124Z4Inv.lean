module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121T
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Compat
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Mod
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameB0
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GH74.Defs
public import CFSG.Goldschmidt.BasicG
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

private theorem sec124_sq_mem_coord (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {x : G} (hx : x ∈ secV t S L E) : ∃ n, IsEvenVec n ∧ x * x = φ n := by
  have hsq : x * x ∈ secB S L :=
    sec124_z4_sq_mem hZ (sec121_B_le_V F hE) F.bdata.2.1
      (fun b hb => sec12E_B_sq F hb) x hx
  obtain ⟨n, hn, hnφ⟩ := (hperm.2.2.1 (x * x)).mp hsq
  exact ⟨n, hn, hnφ.symm⟩

private theorem sec124_coord_sq (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {n : Fin 5 → ZMod 2} (hn : IsEvenVec n) : ∃ x ∈ secV t S L E, x * x = φ n := by
  have hb : φ n ∈ secB S L := (hperm.2.2.1 (φ n)).mpr ⟨n, hn, rfl⟩
  exact sec124_z4_root hZ (sec121_B_le_V F hE) (fun b hb => sec12E_B_sq F hb) (φ n) hb

private theorem sec124_f_sq_eq (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {x x' : G} (hx : x ∈ secV t S L E) (hx' : x' ∈ secV t S L E) (hxx : x * x = x' * x') :
    sec12f t x = sec12f t x' := by
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hE
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => sec12E_B_sq F hb
  have hcomm := sec124_z4_comm hZ
  have hVP : secV t S L E ≤ secCMB t S L := (sec121_V_le_E F hE).trans hE.1
  have hx'inv : x'⁻¹ ∈ secV t S L E := (secV t S L E).inv_mem hx'
  have hd : x * x'⁻¹ ∈ secV t S L E := (secV t S L E).mul_mem hx hx'inv
  have hd2 : (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
    have h1 : (x * x'⁻¹) * (x * x'⁻¹) = (x * x) * (x' * x')⁻¹ := by
      calc (x * x'⁻¹) * (x * x'⁻¹) = x * (x'⁻¹ * x) * x'⁻¹ := by group
        _ = x * (x * x'⁻¹) * x'⁻¹ := by rw [hcomm x hx x'⁻¹ hx'inv]
        _ = (x * x) * (x' * x')⁻¹ := by group
    rw [h1, ← hxx]
    group
  have hdB : x * x'⁻¹ ∈ secB S L :=
    sec124_z4_mem_of_sq hZ hBV F.bdata.2.1 hB2 (x * x'⁻¹) hd hd2
  have hf1 : sec12f t (x * x'⁻¹) = 1 := (sec121_f_eq_one_iff_V F hE hd).mpr hdB
  have hmul : sec12f t (x * x'⁻¹) = sec12f t x * (sec12f t x')⁻¹ := by
    rw [sec12E_f_mul F (hVP hx) (hVP hx'inv), sec121_f_inv F (hVP hx')]
  exact mul_inv_eq_one.mp (hmul ▸ hf1)

private theorem sec124_delta (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5))) :
    ∃ δ : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2),
      (∀ n, IsEvenVec n → IsEvenVec (δ n)) ∧
        ∀ n, IsEvenVec n → ∀ x ∈ secV t S L E, x * x = φ n → sec12f t x = φ (δ n) := by
  have hVP : secV t S L E ≤ secCMB t S L := (sec121_V_le_E F hE).trans hE.1
  have hδ : ∀ n, ∃ m, IsEvenVec n → IsEvenVec m ∧
      ∀ x ∈ secV t S L E, x * x = φ n → sec12f t x = φ m := by
    intro n
    by_cases hn : IsEvenVec n
    · obtain ⟨x₀, hx₀, hx₀sq⟩ := sec124_coord_sq F hE hZ hperm hn
      obtain ⟨m, hm, hφm⟩ := (hperm.2.2.1 (sec12f t x₀)).mp (sec12E_f_mem F (hVP hx₀))
      refine ⟨m, fun _ => ⟨hm, fun x hx hxsq => ?_⟩⟩
      rw [hφm]
      exact sec124_f_sq_eq F hE hZ hperm hx hx₀ (hxsq.trans hx₀sq.symm)
    · exact ⟨0, fun h => absurd h hn⟩
  choose δ hδspec using hδ
  exact ⟨δ, fun n hn => (hδspec n hn).1, fun n hn x hx hxsq => (hδspec n hn).2 x hx hxsq⟩

private theorem sec124_delta_add (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {δ : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2)} (hδeven : ∀ n, IsEvenVec n → IsEvenVec (δ n))
    (hδprop : ∀ n, IsEvenVec n → ∀ x ∈ secV t S L E, x * x = φ n → sec12f t x = φ (δ n))
    {n m : Fin 5 → ZMod 2} (hn : IsEvenVec n) (hm : IsEvenVec m) :
    δ (n + m) = δ n + δ m := by
  have hVP : secV t S L E ≤ secCMB t S L := (sec121_V_le_E F hE).trans hE.1
  have hcomm := sec124_z4_comm hZ
  obtain ⟨x, hx, hxsq⟩ := sec124_coord_sq F hE hZ hperm hn
  obtain ⟨x', hx', hx'sq⟩ := sec124_coord_sq F hE hZ hperm hm
  have hxx'V : x * x' ∈ secV t S L E := (secV t S L E).mul_mem hx hx'
  have hsq : (x * x') * (x * x') = φ (n + m) := by
    have h1 : (x * x') * (x * x') = (x * x) * (x' * x') := by
      calc (x * x') * (x * x') = x * (x' * x) * x' := by group
        _ = x * (x * x') * x' := by rw [hcomm x' hx' x hx]
        _ = (x * x) * (x' * x') := by group
    rw [h1, hxsq, hx'sq]
    exact (hperm.1 n m hn hm).symm
  have h1 : sec12f t (x * x') = φ (δ n + δ m) := by
    rw [sec12E_f_mul F (hVP hx) (hVP hx'), hδprop n hn x hx hxsq, hδprop m hm x' hx' hx'sq]
    exact (hperm.1 (δ n) (δ m) (hδeven n hn) (hδeven m hm)).symm
  have h2 : sec12f t (x * x') = φ (δ (n + m)) :=
    hδprop (n + m) (isEvenVec_add_vec hn hm) (x * x') hxx'V hsq
  have hφeq : φ (δ (n + m)) = φ (δ n + δ m) := by rw [← h2, h1]
  exact hperm.2.1 (δ (n + m)) (δ n + δ m) (hδeven (n + m) (isEvenVec_add_vec hn hm))
    (isEvenVec_add_vec (hδeven n hn) (hδeven m hm)) hφeq

private theorem sec124_delta_comm (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {δ : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2)} (hδeven : ∀ n, IsEvenVec n → IsEvenVec (δ n))
    (hδprop : ∀ n, IsEvenVec n → ∀ x ∈ secV t S L E, x * x = φ n → sec12f t x = φ (δ n))
    {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ alternatingGroup (Fin 5)) {n : Fin 5 → ZMod 2}
    (hn : IsEvenVec n) : δ (permVec σ n) = permVec σ (δ n) := by
  obtain ⟨y, hy, hyact⟩ := hperm.2.2.2.2 σ hσ
  have hyY : y ∈ secM t S L ⊓ L := hy
  have hyt : y * t = t * y := (Subgroup.mem_centralizer_iff.mp F.htC) y hy.2
  obtain ⟨x, hx, hxsq⟩ := sec124_coord_sq F hE hZ hperm hn
  have hnx : y * x * y⁻¹ ∈ secV t S L E :=
    (Subgroup.mem_normalizer_iff.mp (sec121_Y_le_normalizer_V F hE hyY) x).mp hx
  have hsq : (y * x * y⁻¹) * (y * x * y⁻¹) = φ (permVec σ n) := by
    have h1 : (y * x * y⁻¹) * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
    rw [h1, hxsq, hyact n hn]
  have hleft : sec12f t (y * x * y⁻¹) = φ (δ (permVec σ n)) :=
    hδprop (permVec σ n) (isEvenVec_permVec σ hn) (y * x * y⁻¹) hnx hsq
  have hright : sec12f t (y * x * y⁻¹) = φ (permVec σ (δ n)) := by
    rw [sec12E_f_conj hyt x, hδprop n hn x hx hxsq, hyact (δ n) (hδeven n hn)]
  have hφeq : φ (δ (permVec σ n)) = φ (permVec σ (δ n)) := hleft.symm.trans hright
  exact hperm.2.1 (δ (permVec σ n)) (permVec σ (δ n))
    (hδeven (permVec σ n) (isEvenVec_permVec σ hn)) (isEvenVec_permVec σ (hδeven n hn)) hφeq

private theorem sec124_delta_id (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {δ : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2)} (hδeven : ∀ n, IsEvenVec n → IsEvenVec (δ n))
    (hδprop : ∀ n, IsEvenVec n → ∀ x ∈ secV t S L E, x * x = φ n → sec12f t x = φ (δ n)) :
    ∀ n, IsEvenVec n → δ n = n := by
  rcases sec122_schur δ hδeven
      (fun n m hn hm => sec124_delta_add F hE hZ hperm hδeven hδprop hn hm)
      (fun σ hσ n hn => sec124_delta_comm F hE hZ hperm hδeven hδprop hσ hn) with h0 | hid
  · exfalso
    have hz : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have hφ0 : φ 0 = 1 := by
      have h := hperm.1 0 0 hz hz
      rw [add_zero] at h
      exact mul_eq_left.1 h.symm
    have hn0 : IsEvenVec (wvec 0) := wvec_even 0
    have hwne : wvec (0 : Fin 5) ≠ 0 := by
      intro h
      have h1 : wvec (0 : Fin 5) 1 = (0 : Fin 5 → ZMod 2) 1 := congrFun h 1
      simp [wvec] at h1
    have hb : φ (wvec 0) ∈ secB S L := (hperm.2.2.1 (φ (wvec 0))).mpr ⟨wvec 0, hn0, rfl⟩
    obtain ⟨v, hv, hfv⟩ := sec121_f_surj_V F hE hb
    obtain ⟨n, hn, hnsq⟩ := sec124_sq_mem_coord F hE hZ hperm hv
    have h1 : sec12f t v = φ 0 := by rw [hδprop n hn v hv hnsq, h0 n hn]
    have h2 : φ (wvec 0) = φ 0 := by rw [← hfv, h1]
    exact hwne (hperm.2.1 (wvec 0) 0 hn0 hz h2)
  · exact hid

theorem sec124_t_inv (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hZ : IsZ4Pow4 (secV t S L E)) : ∀ v ∈ secV t S L E, t * v * t⁻¹ = v⁻¹ := by
  obtain ⟨φ, hperm, -⟩ := F.bdata.2.2.2.2.2
  have hpermY : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)) := by
    rw [F.bdata.2.2.2.2.1]
    exact hperm
  obtain ⟨δ, hδeven, hδprop⟩ := sec124_delta F hE hZ hpermY
  have hδid : ∀ n, IsEvenVec n → δ n = n := sec124_delta_id F hE hZ hpermY hδeven hδprop
  intro v hv
  obtain ⟨n, hn, hnsq⟩ := sec124_sq_mem_coord F hE hZ hpermY hv
  have hf : sec12f t v = v * v := by rw [hδprop n hn v hv hnsq, hδid n hn, hnsq]
  rw [sec122_t_conj t v, hf]
  group

end CFSG.OddStandard.SmallF3.Omega
