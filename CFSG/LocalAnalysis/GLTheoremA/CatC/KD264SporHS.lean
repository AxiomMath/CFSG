module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.ClassSpec
public import CFSG.Sporadic.SchreierLemmas.MoorePresentation
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.RankThree.Native.HSMcLSmall
public import Certificates.Certificate10139

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.KD264HS

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.RankThree.Native


theorem rep_imgArr (g : Equiv.Perm (Fin 100)) : CFSG.Monster.B.Co2.Rep 100 (imgArr g) g := by
  intro x
  rw [imgArr, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ x.2]

theorem hsA_mem_hsB_mem : hsA ∈ hs100P ∧ hsB ∈ hs100P := by
  have h := Certificates.certificate10139
  unfold hsThreeOK hsGensOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨mem_hs100P_of_sift (rep_imgArr hsA) h.1.1.1, mem_hs100P_of_sift (rep_imgArr hsB) h.1.1.2⟩

theorem evalCodes_mem_HS (w : List ℤ) : evalCodes hsS w ∈ hs100P := by
  refine evalCodes_mem _ (fun g hg => ?_) w
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact hsA_mem_hsB_mem.1
  · exact hsA_mem_hsB_mem.2

@[expose] noncomputable def mooreHS (j : ℕ) : Equiv.Perm (Fin 100) :=
  if j = 1 then evalCodes hsS m1W else if j = 2 then evalCodes hsS m2W
  else if j = 3 then evalCodes hsS m3W else 1

theorem mooreHS_mem (j : ℕ) : mooreHS j ∈ hs100P := by
  unfold mooreHS
  split_ifs
  · exact evalCodes_mem_HS _
  · exact evalCodes_mem_HS _
  · exact evalCodes_mem_HS _
  · exact Subgroup.one_mem _

theorem hs_three_facts :
    orderOf (evalCodes hsS zW) = 3 ∧
      CFSG.Sporadic.SchreierLemmas.IsMooreFamily 3 mooreHS ∧ mooreHS 1 ≠ 1 ∧
      (∀ j, mooreHS j * evalCodes hsS zW = evalCodes hsS zW * mooreHS j) ∧
      123200 ≤ (conjClass hs100P (evalCodes hsS zW)).ncard := by
  have hn : (100 : ℕ) < 2 ^ 32 := by norm_num
  have h := Certificates.certificate10139
  unfold hsThreeOK hsMooreOK hsClassOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hz3, hz1⟩, h13⟩, h22⟩, h32⟩, h123⟩, h233⟩, h132⟩, hm1⟩, hc1⟩, hc2⟩, hc3⟩⟩,
    ⟨⟨htree, hdist⟩, hsize⟩⟩ := h
  set z := evalCodes hsS zW with hzdef
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨orderOf_eq_prime hz3 hz1, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [mooreHS] using h13
  · intro j hj2 hj3
    interval_cases j
    · simpa [mooreHS] using h22
    · simpa [mooreHS] using h32
  · intro j hj2 hj3
    interval_cases j
    · simpa [mooreHS] using h123
    · simpa [mooreHS] using h233
  · intro i j hi hij hj3
    obtain rfl : i = 1 := by omega
    obtain rfl : j = 3 := by omega
    simpa [mooreHS] using h132
  · simpa [mooreHS] using hm1
  · intro j
    unfold mooreHS
    split_ifs
    · exact hc1
    · exact hc2
    · exact hc3
    · rw [one_mul, mul_one]
  ·
    set «gens» := pairTables hsA hsB
    set gensInv := pairTables hsA⁻¹ hsB⁻¹
    set C := conjClosure 100 «gens» gensInv (toTable z) 130000 with hC
    have hA : hsA ∈ hs100P := hsA_mem_hsB_mem.1
    have hB : hsB ∈ hs100P := hsA_mem_hsB_mem.2
    have hg := pairTables_spec hn hA hB
    have hent := conjTreeOK_spec hs100P hg (rep_toTable hn z) htree
    set L : List (Equiv.Perm (Fin 100)) := C.1.toList.map (tablePerm 100) with hL
    have hrepL : ∀ T ∈ C.1.toList, Rep 100 T (tablePerm 100 T) := by
      intro T hT
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
      rw [Array.length_toList] at hk
      obtain ⟨d, -, hd⟩ := hent k hk
      rw [Array.getElem_toList, ← getElem!_pos C.1 k hk, tablePerm_eq hd]
      exact hd
    have hF : List.Forall₂ (Rep 100) C.1.toList L := by
      rw [hL, List.forall₂_map_right_iff]
      exact List.forall₂_same.2 hrepL
    have hnd : L.Nodup := nodup_of_keysDistinct hF hdist
    have hsub : ∀ y ∈ L, y ∈ conjClass hs100P z := by
      intro y hy
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
      rw [Array.length_toList] at hk
      obtain ⟨d, hd, hrep⟩ := hent k hk
      rw [Array.getElem_toList, ← getElem!_pos C.1 k hk, tablePerm_eq hrep]
      exact ⟨d, hd, rfl⟩
    have hlen := CFSG.OddStandard.length_le_ncard_conjClass hsub hnd
    rw [hL, List.length_map, Array.length_toList, hsize] at hlen
    exact hlen

theorem card_centralizer_z_le :
    Nat.card ↥(Subgroup.centralizer ({evalCodes hsS zW} : Set (Equiv.Perm (Fin 100))) ⊓
      hs100P) ≤ 360 := by
  obtain ⟨-, -, -, -, hcl⟩ := hs_three_facts
  have h := ncard_conjClass_mul_card hs100P (evalCodes hsS zW)
  rw [card_hs100P] at h
  have hc : Nat.card ↥(Subgroup.centralizer ({evalCodes hsS zW} : Set (Equiv.Perm (Fin 100))) ⊓
      hs100P) = Nat.card (centralizerIn hs100P
        (evalCodes hsS zW)) := by
    rw [centralizerIn, inf_comm]
  rw [hc]
  by_contra hgt
  push Not at hgt
  have : 123200 * 361 ≤ (conjClass hs100P (evalCodes hsS zW)).ncard *
      Nat.card (centralizerIn hs100P (evalCodes hsS zW)) :=
    Nat.mul_le_mul hcl hgt
  omega

theorem kd264RowData_HS_three : KD264Gen.KD264RowData 3 ↥hs100P := by
  obtain ⟨hzo, hmoore, hm1, hcomm, -⟩ := hs_three_facts
  obtain ⟨-, ⟨eL⟩⟩ := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 5)
    (by norm_num) mooreHS hmoore).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hm1⟩
  set D : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure (mooreHS '' Set.Icc 1 (5 - 2))
  have hDP : D ≤ hs100P := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, -, rfl⟩
    exact mooreHS_mem j
  have hxD : evalCodes hsS zW ∈ Subgroup.centralizer (D : Set (Equiv.Perm (Fin 100))) := by
    show evalCodes hsS zW ∈ Subgroup.centralizer
      ((Subgroup.closure (mooreHS '' Set.Icc 1 (5 - 2)) : Subgroup _) : Set (Equiv.Perm (Fin 100)))
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, -, rfl⟩
    exact hcomm j
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥D := eL.symm.isSimpleGroup
  have hDcard : Nat.card ↥D = 60 := by
    rw [← Nat.card_congr eL.toEquiv, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g := by
    have hx : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.2 (by decide)
    have hy : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.2 (by decide)
    refine ⟨eL ⟨_, hx⟩, (eL ⟨_, hx⟩).2, eL ⟨_, hy⟩, (eL ⟨_, hy⟩).2, fun h => ?_⟩
    have h1 : eL (⟨_, hx⟩ * ⟨_, hy⟩) = eL (⟨_, hy⟩ * ⟨_, hx⟩) := by
      rw [map_mul, map_mul]; exact Subtype.ext h
    have h2 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) * (Equiv.swap (0 : Fin 5) 1 *
        Equiv.swap 2 3) = (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) *
        (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) := congrArg Subtype.val (eL.injective h1)
    exact absurd h2 (by decide)
  have hcard : Nat.card ↥hs100P = 44352000 := card_hs100P
  exact KD264Gen.kd264RowData_of_record_sq Nat.prime_three (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num) (evalCodes_mem_HS zW) hzo hDP hs hnab (by rw [hDcard]; norm_num)
    hxD le_rfl card_centralizer_z_le (by rw [hDcard])

theorem kd264SporAt_HS_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hfs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .HS)) :
    KD264Gen.KD264SporAt 3 .HS := by
  have e : CFSG.Blueprint.NativeSporadic.HS ≃* ↥hs100P := hs100Equiv
  have hfin : Finite ↥hs100P := inferInstance
  have hs : IsSimpleGroup ↥hs100P := @MulEquiv.isSimpleGroup _ _ _ _ hfs e.symm
  have hnp : ¬ (Nat.card ↥hs100P).Prime := by
    rw [card_hs100P]; norm_num
  have hnc := CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_not_comm_of_simple_not_prime hnp
  have b : ↥hs100P ≃* (TauCeti.CFSGIndex.sporadic .HS).Group := e.symm.trans (hbr .HS).some
  exact @KD264Gen.kd264SporAt_of_model hOut 3 Nat.prime_three (by norm_num) .HS ↥hs100P _ hfin hs
    hnc b fun _ _ _ => kd264RowData_HS_three

end CFSG.LocalAnalysis.GLTheoremA.KD264HS
