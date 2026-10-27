module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwDefs
public import CFSG.Quasithin.H13.GoldschmidtU43ModCert
public import CFSG.Quasithin.H13.GoldschmidtU43NoL3Chk
public import CFSG.GH74.KGroups.NativeChecks
public import Certificates.Data.Asc82SwapCheck
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwKer
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate9130

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Quasithin.H13.U43 CFSG.KGroups.U43 Certificates.Asc82Swap

private lemma getElem!_mem {L : Array (Array ℕ)} {j : ℕ} (hj : j < L.size) : L[j]! ∈ L := by
  rw [getElem!_pos L j hj]
  exact Array.getElem_mem hj

private lemma exists_index_of_mem_filter {L : Array (Array ℕ)} {p : Array ℕ → Bool}
    {t : Array ℕ} (ht : t ∈ L.filter p) :
    ∃ j < L.size, L[j]! = t ∧ p t = true := by
  obtain ⟨htL, hp⟩ := Array.mem_filter.mp ht
  obtain ⟨j, hj, hje⟩ := Array.mem_iff_getElem.mp htL
  exact ⟨j, hj, by rw [getElem!_pos L j hj, hje], hp⟩

private lemma filter_index_of_mem {L : Array (Array ℕ)} {p : Array ℕ → Bool} {a : Array ℕ}
    (ha : a ∈ L) (hp : p a = true) :
    ∃ i < (L.filter p).size, (L.filter p)[i]! = a := by
  have hm : a ∈ L.filter p := Array.mem_filter.mpr ⟨ha, hp⟩
  obtain ⟨i, hi, hie⟩ := Array.mem_iff_getElem.mp hm
  exact ⟨i, hi, by rw [getElem!_pos _ i hi]; exact hie⟩

private lemma isOddA_iff_odd {t : Array ℕ} {s : X₀} (hC : Stage2HCard) (hs : s ∈ SwC)
    (hrep : Rep 820 t (psi s)) : isOddA 820 t = true ↔ Odd (orderOf s) := by
  unfold isOddA
  rw [eqA_iff (CFSG.GH74.KGroups.NativeChecks.rep_powA hrep 9) (rep_idA (n := 820))]
  rw [show (psi s) ^ 9 = 1 ↔ s ^ 9 = 1 from by
    constructor
    · intro h
      exact psi_inj (by simpa [map_pow] using h)
    · intro h
      simpa [map_pow] using congrArg psi h]
  exact (sw_odd_iff_pow9 hC hs).symm

theorem sw_elemList_enum :
    SwEnum (elemList 820 tabA tabB) (SwC : Set X₀) := by
  have hh := Certificates.certificate4158.2.1
  unfold h4Check at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨⟨h1, hE⟩, hc⟩, hr⟩, hd⟩, hk⟩ := hh
  have hcomm := comm_md h1 hc
  have hmul : ∀ j < 4, ∀ x ∈ (SwC : Set X₀), gen5 mdA mdS mdU mdV 1 j * x ∈ SwC := by
    intro j hj x hx
    have hx' : x * xElt = xElt * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc
      gen5 mdA mdS mdU mdV 1 j * x * xElt = gen5 mdA mdS mdU mdV 1 j * (x * xElt) := by
        group
      _ = gen5 mdA mdS mdU mdV 1 j * (xElt * x) := by rw [hx']
      _ = gen5 mdA mdS mdU mdV 1 j * xElt * x := by group
      _ = xElt * gen5 mdA mdS mdU mdV 1 j * x := by rw [hcomm j hj]
      _ = xElt * (gen5 mdA mdS mdU mdV 1 j * x) := by group
  obtain ⟨hsz, -⟩ := derivOK_size hd
  have hsz' : (elemList 820 tabA tabB).size = 1152 := hsz
  have hk' : keysNodup (elemList 820 tabA tabB) = true := hk
  have hex := deriv_sound psi (SwC : Set X₀) (leftStep 820 (hGens 820 tabA tabB))
    (fun j x => gen5 mdA mdS mdU mdV 1 j * x) (one_mem _) (by rw [map_one]; exact rep_idA)
    (fun j hj x hx => hmul j hj x hx)
    (fun j hj t x hx => by
      unfold leftStep
      simpa [map_mul] using rep_compA (rep_hGens h1 j (by omega)) hx) hd
  choose! f hfT hf using hex
  have hinj : Set.InjOn f (Set.Iio (elemList 820 tabA tabB).size) := by
    intro i hi j hj hij
    exact rep_index_injective hsz' hk' hf i (hsz' ▸ hi) j (hsz' ▸ hj) hij
  refine ⟨f, ?_, hinj, ?_⟩
  · intro i hi
    exact hf i (hsz' ▸ hi)
  · have hsub : f '' Set.Iio (elemList 820 tabA tabB).size ⊆ (SwC : Set X₀) := by
      rintro _ ⟨i, hi, rfl⟩
      exact hfT i (hsz' ▸ hi)
    have hcard : (SwC : Set X₀).ncard = 1152 := by
      have h : Nat.card (SwC : Set X₀) = 1152 := (stage2HModel_card).2
      rwa [Nat.card_coe_set_eq] at h
    have hIio : (Set.Iio (elemList 820 tabA tabB).size).ncard =
        (elemList 820 tabA tabB).size := by
      simpa using Nat.card_Iio (elemList 820 tabA tabB).size
    have h1 : (f '' Set.Iio (elemList 820 tabA tabB).size).ncard = 1152 := by
      rw [Set.InjOn.ncard_image (s := Set.Iio (elemList 820 tabA tabB).size) (f := f) hinj,
        hIio, hsz']
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [h1, hcard])
      (Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num))

theorem sw_oddList_cover :
    SwCover (oddList 820 (elemList 820 tabA tabB)) {o | o ∈ SwC ∧ Odd (orderOf o)} := by
  change SwCover ((elemList 820 tabA tabB).filter (isOddA 820))
    {o | o ∈ SwC ∧ Odd (orderOf o)}
  have hC : Stage2HCard := (stage2HModel_card).2
  obtain ⟨f, hf, -, himg⟩ := sw_elemList_enum
  constructor
  · intro i hi
    have hmem : ((elemList 820 tabA tabB).filter (isOddA 820))[i]! ∈
        (elemList 820 tabA tabB).filter (isOddA 820) := by
      rw [getElem!_pos ((elemList 820 tabA tabB).filter (isOddA 820)) i hi]
      exact Array.getElem_mem hi
    obtain ⟨j, hj, hje, hjp⟩ := exists_index_of_mem_filter (p := isOddA 820) hmem
    have hjp' : isOddA 820 (elemList 820 tabA tabB)[j]! = true := by
      rwa [← hje] at hjp
    have hfj : f j ∈ (SwC : Set X₀) := by
      rw [← himg]
      exact ⟨j, hj, rfl⟩
    refine ⟨f j, ⟨hfj, (isOddA_iff_odd hC hfj (hf j hj)).1 hjp'⟩, ?_⟩
    rw [← hje]
    exact hf j hj
  · intro s hs
    obtain ⟨hsC, hsOdd⟩ := hs
    have hmem : s ∈ f '' Set.Iio (elemList 820 tabA tabB).size := by
      rw [himg]
      exact hsC
    obtain ⟨j, hj, rfl⟩ := hmem
    have hrep : Rep 820 (elemList 820 tabA tabB)[j]! (psi (f j)) := hf j hj
    have hodd : isOddA 820 (elemList 820 tabA tabB)[j]! = true :=
      (isOddA_iff_odd hC hsC hrep).2 hsOdd
    obtain ⟨i, hi, hie⟩ := filter_index_of_mem (p := isOddA 820)
      (getElem!_mem (L := elemList 820 tabA tabB) hj) hodd
    exact ⟨i, hi, by rw [hie]; exact hrep⟩

theorem sw_oddNe_cover :
    SwCover (oddNe 820 (oddList 820 (elemList 820 tabA tabB)) (idA 820))
      {o | o ∈ SwC ∧ Odd (orderOf o) ∧ o ≠ 1} := by
  change SwCover (((elemList 820 tabA tabB).filter (isOddA 820)).filter
    (fun t => !eqA 820 t (idA 820))) {o | o ∈ SwC ∧ Odd (orderOf o) ∧ o ≠ 1}
  have hC : Stage2HCard := (stage2HModel_card).2
  have hodd : SwCover ((elemList 820 tabA tabB).filter (isOddA 820))
      {o | o ∈ SwC ∧ Odd (orderOf o)} := sw_oddList_cover
  constructor
  · intro i hi
    have hmem : (((elemList 820 tabA tabB).filter (isOddA 820)).filter
        (fun t => !eqA 820 t (idA 820)))[i]! ∈
        ((elemList 820 tabA tabB).filter (isOddA 820)).filter
          (fun t => !eqA 820 t (idA 820)) := by
      rw [getElem!_pos (((elemList 820 tabA tabB).filter (isOddA 820)).filter
        (fun t => !eqA 820 t (idA 820))) i hi]
      exact Array.getElem_mem hi
    obtain ⟨htO, hne⟩ := Array.mem_filter.mp hmem
    obtain ⟨htE, htOdd⟩ := Array.mem_filter.mp htO
    obtain ⟨j, hj, hje, -⟩ := exists_index_of_mem_filter (p := isOddA 820) htO
    obtain ⟨f, hf, -, himg⟩ := sw_elemList_enum
    have hfj : f j ∈ (SwC : Set X₀) := by
      rw [← himg]
      exact ⟨j, hj, rfl⟩
    have hrep : Rep 820 (elemList 820 tabA tabB)[j]! (psi (f j)) := hf j hj
    have hoddT : isOddA 820 (elemList 820 tabA tabB)[j]! = true := by
      rwa [← hje] at htOdd
    have hsOdd : Odd (orderOf (f j)) := (isOddA_iff_odd hC hfj hrep).1 hoddT
    have hne' : eqA 820 (elemList 820 tabA tabB)[j]! (idA 820) = false := by
      have h : eqA 820 (((elemList 820 tabA tabB).filter (isOddA 820)).filter
          (fun t => !eqA 820 t (idA 820)))[i]! (idA 820) = false := by
        simpa using hne
      rwa [← hje] at h
    have hsne : f j ≠ 1 := by
      intro hs1
      have heq : eqA 820 (elemList 820 tabA tabB)[j]! (idA 820) = true :=
        (eqA_iff hrep (rep_idA (n := 820))).2 (by rw [hs1, map_one])
      rw [hne'] at heq
      exact Bool.noConfusion heq
    exact ⟨f j, ⟨hfj, hsOdd, hsne⟩, by rw [← hje]; exact hrep⟩
  · intro s hs
    obtain ⟨hsC, hsOdd, hsne⟩ := hs
    obtain ⟨j, hj, hrep⟩ := hodd.2 s ⟨hsC, hsOdd⟩
    have hnot : eqA 820 ((elemList 820 tabA tabB).filter (isOddA 820))[j]! (idA 820) ≠ true := by
      intro h
      have h1 : psi s = (1 : Equiv.Perm (Fin 820)) :=
        (eqA_iff hrep (rep_idA (n := 820))).1 h
      exact hsne (psi_inj (by simpa [map_one] using h1))
    have hfalse : eqA 820 ((elemList 820 tabA tabB).filter (isOddA 820))[j]! (idA 820) =
        false := Bool.eq_false_iff.2 hnot
    have hp : (!eqA 820 ((elemList 820 tabA tabB).filter (isOddA 820))[j]! (idA 820)) = true := by
      simpa using hfalse
    obtain ⟨i, hi, hie⟩ := filter_index_of_mem
      (p := fun t => !eqA 820 t (idA 820))
      (getElem!_mem (L := (elemList 820 tabA tabB).filter (isOddA 820)) hj) hp
    exact ⟨i, hi, by rw [hie]; exact hrep⟩

theorem sw_rep_inv {L Li : Array (Array ℕ)} (h : invsOK 820 L Li = true) {i : ℕ}
    (hi : i < L.size) {s : X₀} (hs : Rep 820 L[i]! (psi s)) : Rep 820 Li[i]! (psi s⁻¹) := by
  simpa [map_inv] using rep_inv_of_isInvA hs (invsOK_spec h i hi)

end CFSG.OddStandard.SmallF3.Omega
