module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma44Suz
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzFacts
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.GroupTheory.InvolutionPair
public import CFSG.GF2Type.Widths1112.Core
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import Certificates.Certificate10740
public import Certificates.Certificate26990
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma44SuzL34

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.Certificates.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.EvenSporadicStandard.Induction

private noncomputable def suzA : Equiv.Perm (Fin 1782) := suzWord suzWordA

private noncomputable def suzB : Equiv.Perm (Fin 1782) := suzWord suzWordB

private def suzK : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure {suzA, suzB}

private def Sol78FourGroupAt {G : Type*} [Group G] (E H : Subgroup G) (n : G) : Prop :=
  Nat.card E = 4 ∧ (∀ e ∈ E, e ^ 2 = 1) ∧
    (∀ e ∈ E, e ≠ 1 → Nat.card (Subgroup.centralizer ({e} : Set G)) = 161280) ∧
    Subgroup.centralizer (E : Set G) = H ⊔ E ∧ H ⊓ E = ⊥ ∧
    H ≤ Subgroup.centralizer (E : Set G) ∧
    ⁅Subgroup.centralizer (E : Set G), Subgroup.centralizer (E : Set G)⁆ = H ∧
    ⁅H, H⁆ = H ∧ Nat.card H = 20160 ∧
    orderOf n = 3 ∧ n ∈ Subgroup.centralizer (H : Set G) ∧
    n ∈ Subgroup.normalizer (E : Set G) ∧
    ∀ e ∈ E, e ≠ 1 → n * e * n⁻¹ ≠ e

private theorem suzAB_facts :
    Rep 1782 suzArrA (suzWord suzWordA) ∧ Rep 1782 suzArrB (suzWord suzWordB) ∧
    Rep 1782 suzArrAi (suzWord suzWordA)⁻¹ ∧ Rep 1782 suzArrBi (suzWord suzWordB)⁻¹ ∧
    suzWord suzWordA ∈ suzM ∧ suzWord suzWordB ∈ suzM ∧
    suzWord suzWordA * suzInv 0 = suzInv 0 * suzWord suzWordA ∧
    suzWord suzWordB * suzInv 0 = suzInv 0 * suzWord suzWordB := by
  have h := Certificates.certificate26680
  simp only [suzRowCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hlet, hinv⟩, hrel⟩, _⟩, _⟩, _⟩, _⟩ := h
  simp only [suzLettersOK, Bool.and_eq_true] at hlet
  obtain ⟨⟨⟨⟨⟨hlA, hlB⟩, _⟩, _⟩, _⟩, _⟩ := hlet
  simp only [suzInvOK, Bool.and_eq_true] at hinv
  obtain ⟨⟨⟨⟨hiA, hiB⟩, _⟩, _⟩, _⟩ := hinv
  simp only [suzRelOK, Bool.and_eq_true] at hrel
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hcA⟩, hcB⟩, _⟩, _⟩, _⟩, _⟩ := hrel
  have hRA : Rep 1782 suzArrA (suzWord suzWordA) := by
    unfold suzArrA
    exact rep_suzArr (lettersOK_mono (by norm_num) hlA)
  have hRB : Rep 1782 suzArrB (suzWord suzWordB) := by
    unfold suzArrB
    exact rep_suzArr (lettersOK_mono (by norm_num) hlB)
  have hRAi : Rep 1782 suzArrAi (suzWord suzWordA)⁻¹ := rep_inv_of_isInvA hRA hiA
  have hRBi : Rep 1782 suzArrBi (suzWord suzWordB)⁻¹ := rep_inv_of_isInvA hRB hiB
  have hR0 : Rep 1782 (tArr 0) (suzInv 0) := rep_suzInv (by norm_num)
  have hAc : suzWord suzWordA * suzInv 0 = suzInv 0 * suzWord suzWordA :=
    (eqA_iff (rep_compA hRA hR0) (rep_compA hR0 hRA)).1 hcA
  have hBc : suzWord suzWordB * suzInv 0 = suzInv 0 * suzWord suzWordB :=
    (eqA_iff (rep_compA hRB hR0) (rep_compA hR0 hRB)).1 hcB
  exact ⟨hRA, hRB, hRAi, hRBi, suzWord_mem hlA, suzWord_mem hlB, hAc, hBc⟩

private theorem suzE0_facts :
    let n : Equiv.Perm (Fin 1782) := suzWord suzWordN
    let t : Equiv.Perm (Fin 1782) := suzInv 0
    let e1 : Equiv.Perm (Fin 1782) := n * t * n⁻¹
    n ^ 3 = 1 ∧ n ≠ 1 ∧ n * suzWord suzWordA = suzWord suzWordA * n ∧
    n * suzWord suzWordB = suzWord suzWordB * n ∧ e1 * e1 = 1 ∧
    t * e1 = e1 * t ∧ e1 ≠ t ∧ n * e1 * n⁻¹ = t * e1 ∧
    e1 * suzWord suzWordA = suzWord suzWordA * e1 ∧
    e1 * suzWord suzWordB = suzWord suzWordB * e1 ∧
    suzWord suzWordD * t = t * suzWord suzWordD ∧
    suzWord suzWordD * e1 ≠ e1 * suzWord suzWordD := by
  have h := Certificates.certificate10740
  simp only [suzE0Check, suzCommutes, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlN, hlD⟩, hiN⟩, hn3raw⟩, hn1raw⟩, hcNA⟩, hcNB⟩, he12raw⟩,
    hcte⟩, he1tne⟩, hnconj⟩, hce1A⟩, hce1B⟩, hctD⟩, hncD⟩ := h
  obtain ⟨hRA, hRB, _, _, _, _, _, _⟩ := suzAB_facts
  let n : Equiv.Perm (Fin 1782) := suzWord suzWordN
  let t : Equiv.Perm (Fin 1782) := suzInv 0
  let e1 : Equiv.Perm (Fin 1782) := n * t * n⁻¹
  have hRN : Rep 1782 suzArrN n := by
    unfold n suzArrN
    exact rep_suzArr (lettersOK_mono (by norm_num) hlN)
  have hRNi : Rep 1782 suzArrNi n⁻¹ := rep_inv_of_isInvA hRN hiN
  have hR0 : Rep 1782 (tArr 0) t := by
    unfold t
    exact rep_suzInv (by norm_num)
  have hRE1 : Rep 1782 suzArrE1 e1 := by
    unfold e1 suzArrE1
    exact rep_compA (rep_compA hRN hR0) hRNi
  have hRσ : Rep 1782 suzArrSigma (suzWord suzWordD) := by
    unfold suzArrSigma
    exact rep_suzArr (lettersOK_mono (by norm_num) hlD)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h' : n * (n * n) = 1 :=
      (eqA_iff (rep_compA hRN (rep_compA hRN hRN)) rep_idA).1 hn3raw
    simpa [pow_succ, pow_two, mul_assoc] using h'
  · intro h1
    have he : eqA 1782 suzArrN (idA 1782) = true := (eqA_iff hRN rep_idA).2 h1
    rw [he] at hn1raw
    exact Bool.noConfusion hn1raw
  · exact (eqA_iff (rep_compA hRN hRA) (rep_compA hRA hRN)).1 hcNA
  · exact (eqA_iff (rep_compA hRN hRB) (rep_compA hRB hRN)).1 hcNB
  · exact (eqA_iff (rep_compA hRE1 hRE1) rep_idA).1 he12raw
  · exact (eqA_iff (rep_compA hR0 hRE1) (rep_compA hRE1 hR0)).1 hcte
  · intro h1
    have he : eqA 1782 suzArrE1 (tArr 0) = true := (eqA_iff hRE1 hR0).2 h1
    rw [he] at he1tne
    exact Bool.noConfusion he1tne
  · exact (eqA_iff (rep_compA (rep_compA hRN hRE1) hRNi) (rep_compA hR0 hRE1)).1 hnconj
  · exact (eqA_iff (rep_compA hRE1 hRA) (rep_compA hRA hRE1)).1 hce1A
  · exact (eqA_iff (rep_compA hRE1 hRB) (rep_compA hRB hRE1)).1 hce1B
  · exact (eqA_iff (rep_compA hRσ hR0) (rep_compA hR0 hRσ)).1 hctD
  · intro h1
    have he : eqA 1782 (compA 1782 suzArrSigma suzArrE1) (compA 1782 suzArrE1 suzArrSigma) =
        true := (eqA_iff (rep_compA hRσ hRE1) (rep_compA hRE1 hRσ)).2 h1
    rw [he] at hncD
    exact Bool.noConfusion hncD

private theorem suzK_facts :
    suzK ≤ suzM ∧ (∀ k ∈ suzK, k * suzInv 0 = suzInv 0 * k) ∧ ⁅suzK, suzK⁆ = suzK ∧
      Nat.card suzK = 20160 := by
  obtain ⟨hRA, hRB, hRAi, hRBi, hAM, hBM, hAc, hBc⟩ := suzAB_facts
  let gs2 : ℕ → Equiv.Perm (Fin 1782) := fun h => if h = 0 then suzA else suzB
  have hS2 : ∀ h < 2, Rep 1782 suzArrAB[h]! (gs2 h) := by
    intro h hh
    interval_cases h
    · exact hRA
    · exact hRB
  have hS2i : ∀ h < 2, Rep 1782 suzArrABi[h]! (gs2 h)⁻¹ := by
    intro h hh
    interval_cases h
    · exact hRAi
    · exact hRBi
  obtain ⟨ev, hev, hevK⟩ : ∃ ev : List ℤ → Equiv.Perm (Fin 1782),
      (∀ w, lettersOK 2 w = true → Rep 1782 (suzArrWord w) (ev w)) ∧
        ∀ w, ev w ∈ suzK := by
    refine ⟨fun w => Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gs2 h) (toLetters 2 w),
      fun w hw => rep_wordA hS2 hS2i w hw, fun w => ?_⟩
    have := evalWord_mem_closure (fun h : Fin 2 => gs2 h) (toLetters 2 w)
    have e : Set.range (fun h : Fin 2 => gs2 h) = {suzA, suzB} := by
      simpa [gs2] using range_fun_two suzA suzB
    rw [e] at this
    exact this
  have h2 := Certificates.certificate26990
  simp only [suzPinCheck, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨hpl, _⟩, hperf⟩, _⟩, hK⟩ := h2
  simp only [suzPinLetters, Bool.and_eq_true, beq_iff_eq] at hpl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlE1, hlE2⟩, hlE3⟩, hlU1⟩, hlV1⟩, hlU2⟩, hlV2⟩, hlC⟩, hlD⟩, hsA⟩,
    hsB⟩ := hpl
  have hKcl : ⁅suzK, suzK⁆ = suzK := by
    refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => ?_) ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · simp only [suzPerfCheck, suzCommOK, Bool.and_eq_true] at hperf
      obtain ⟨⟨⟨hiU1, hiV1⟩, hcA'⟩, ⟨⟨hiU2, hiV2⟩, hcB'⟩⟩ := hperf
      have h1 := (eqA_iff
        (rep_compA (rep_compA (rep_compA (hev _ hlU1) (hev _ hlV1))
          (rep_inv_of_isInvA (hev _ hlU1) hiU1))
          (rep_inv_of_isInvA (hev _ hlV1) hiV1)) hRA).1 hcA'
      have h2 := (eqA_iff
        (rep_compA (rep_compA (rep_compA (hev _ hlU2) (hev _ hlV2))
          (rep_inv_of_isInvA (hev _ hlU2) hiU2))
          (rep_inv_of_isInvA (hev _ hlV2) hiV2)) hRB).1 hcB'
      have hAK : suzWord suzWordA ∈ ⁅suzK, suzK⁆ := by
        have hm := Subgroup.commutator_mem_commutator (hevK suzWordU1) (hevK suzWordV1)
        rwa [commutatorElement_def, h1] at hm
      have hBK : suzWord suzWordB ∈ ⁅suzK, suzK⁆ := by
        have hm := Subgroup.commutator_mem_commutator (hevK suzWordU2) (hevK suzWordV2)
        rwa [commutatorElement_def, h2] at hm
      unfold suzK
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hAK
      · exact hBK
  refine ⟨?_, ?_, hKcl, ?_⟩
  · unfold suzK
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hAM
    · exact hBM
  · have hle : suzK ≤ Subgroup.centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) := by
      unfold suzK
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hAc
      · exact Subgroup.mem_centralizer_singleton_iff.2 hBc
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)
  · simp only [suzKCheck, Bool.and_eq_true, beq_iff_eq] at hK
    obtain ⟨hgenK, hsize⟩ := hK
    have hTA : TabRep suzArrA (suzWord suzWordA) := ⟨hsA, hRA⟩
    have hTB : TabRep suzArrB (suzWord suzWordB) := ⟨hsB, hRB⟩
    have hE : Enumerates suzK (enumOf 1782 suzArrAB 20160).tabs.toList := by
      refine enumerates_closure ?_ ?_ hgenK
      · rintro a (rfl | rfl)
        · exact ⟨0, by simp [suzArrAB], hTA⟩
        · exact ⟨1, by simp [suzArrAB], hTB⟩
      · intro j hj
        have hj2 : j < 2 := by simpa [suzArrAB] using hj
        interval_cases j
        · exact ⟨suzWord suzWordA, Or.inl rfl, hTA⟩
        · exact ⟨suzWord suzWordB, Or.inr rfl, hTB⟩
    rw [hE.card, Array.length_toList, hsize]


private theorem suzFourGroup_data :
    ∃ (E : Subgroup ↥suzM) (n : ↥suzM), Sol78FourGroupAt E (suzK.subgroupOf suzM) n := by
  obtain ⟨hRA, hRB, _, _, _, _, _, _⟩ := suzAB_facts
  obtain ⟨hn3_amb, hn1_amb, hcNA, hcNB, he12_amb, hcte_amb, he1t_amb, hnconj_amb, hce1A,
    hce1B, hctD, hncD⟩ := suzE0_facts
  obtain ⟨hKsuzM, hKcent0, hKperf, hKcard⟩ := suzK_facts
  have h10740 := Certificates.certificate10740
  simp only [suzE0Check, suzCommutes, Bool.and_eq_true, Bool.not_eq_true'] at h10740
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlN, hlD⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ :=
    h10740
  obtain ⟨-, -, -, -, -, ht0M, -, -, -, -, hDcent, -, -, -, -, hinvE, -, -, -, -⟩ :=
    CFSG.Sporadic.SuzOddCore.CTUC_Suz_four_exact_involution_centralizers
  have hcentM0 : CFSG.Sporadic.SuzOddCore.invE 0 =
      CFSG.Sporadic.SuzOddCore.centM (suzInv 0) := (hDcent 0 (by norm_num)).2
  have hcardCentM : Nat.card (CFSG.Sporadic.SuzOddCore.centM (suzInv 0)) = 161280 := by
    rw [← hcentM0]
    exact hinvE
  let t : ↥suzM := ⟨suzInv 0, ht0M⟩
  let n : ↥suzM := ⟨suzWord suzWordN, suzWord_mem (lettersOK_mono (by norm_num) hlN)⟩
  let e1 : ↥suzM := n * t * n⁻¹
  let Et : Subgroup ↥suzM := Subgroup.closure ({t, e1} : Set ↥suzM)
  let Kt : Subgroup ↥suzM := suzK.subgroupOf suzM
  let σ : ↥suzM := ⟨suzWord suzWordD, suzWord_mem (lettersOK_mono (by norm_num) hlD)⟩
  have ht2 : t * t = 1 := by
    apply Subtype.ext
    simpa [t] using CFSG.Sporadic.SuzOddCore.suzInv_sq (i := 0) (by norm_num)
  have ht1 : t ≠ 1 := by
    intro h
    exact CFSG.Sporadic.SuzOddCore.suzInv_ne_one (i := 0) (by norm_num)
      (by simpa [t] using congrArg Subtype.val h)
  have hn3 : n ^ 3 = 1 := Subtype.ext (by simpa [n] using hn3_amb)
  have hn1 : n ≠ 1 := fun h => hn1_amb (by simpa [n] using congrArg Subtype.val h)
  have hordn : orderOf n = 3 := orderOf_eq_prime hn3 hn1
  have hcomm : t * e1 = e1 * t := Subtype.ext (by simpa [t, e1, n] using hcte_amb)
  have he12 : e1 * e1 = 1 := Subtype.ext (by simpa [e1, n, t] using he12_amb)
  have he1ne : e1 ≠ 1 := by
    intro h
    have ht_eq : t = 1 := by
      have hh := congrArg (fun x : ↥suzM => n⁻¹ * x * n) h
      simpa [e1, mul_assoc] using hh
    exact ht1 ht_eq
  have he1t : e1 ≠ t := fun h =>
    he1t_amb (by simpa [t, e1, n] using congrArg Subtype.val h)
  have hconj_t : n * t * n⁻¹ = e1 := rfl
  have hconj_e1 : n * e1 * n⁻¹ = t * e1 :=
    Subtype.ext (by simpa [t, e1, n] using hnconj_amb)
  have hconj_te1 : n * (t * e1) * n⁻¹ = t := by
    calc n * (t * e1) * n⁻¹ = (n * t * n⁻¹) * (n * e1 * n⁻¹) := by group
      _ = e1 * (t * e1) := by rw [hconj_t, hconj_e1]
      _ = t * (e1 * e1) := by rw [← mul_assoc, hcomm.symm, mul_assoc]
      _ = t := by rw [he12, mul_one]
  have hEset : (Et : Set ↥suzM) = {1, t, e1, t * e1} := by
    change (Subgroup.closure ({t, e1} : Set ↥suzM) : Set ↥suzM) = {1, t, e1, t * e1}
    exact CFSG.GroupTheory.coe_closure_pair_eq ht2 he12 hcomm ht1 he1ne he1t.symm
  have hEcard : Nat.card Et = 4 := by
    change Nat.card (Subgroup.closure ({t, e1} : Set ↥suzM)) = 4
    exact CFSG.GroupTheory.card_closure_pair_eq_four ht2 he12 hcomm ht1 he1ne he1t.symm
  have hsq : ∀ e ∈ Et, e ^ 2 = 1 := by
    intro e he
    change e ∈ (Et : Set ↥suzM) at he
    rw [hEset] at he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · simp
    · simpa [pow_two] using ht2
    · simpa [pow_two] using he12
    · rw [pow_two]
      calc (t * e1) * (t * e1) = t * (e1 * t) * e1 := by group
        _ = t * (t * e1) * e1 := by rw [hcomm]
        _ = (t * t) * (e1 * e1) := by group
        _ = 1 := by rw [ht2, he12, one_mul]
  have hcard_t : Nat.card (Subgroup.centralizer ({t} : Set ↥suzM)) = 161280 := by
    have hsub : Subgroup.centralizer ({t} : Set ↥suzM) =
        (Subgroup.centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782)))).subgroupOf suzM := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (by
          simpa [t] using congrArg Subtype.val
            (Subgroup.mem_centralizer_singleton_iff.mp hx))
      · intro hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (by
          apply Subtype.ext
          simpa [t] using Subgroup.mem_centralizer_singleton_iff.mp hx)
    calc Nat.card (Subgroup.centralizer ({t} : Set ↥suzM))
        = Nat.card ((Subgroup.centralizer ({t} : Set ↥suzM)).map suzM.subtype) :=
          (Subgroup.card_map_of_injective suzM.subtype_injective).symm
      _ = Nat.card ((Subgroup.centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
            Subgroup (Equiv.Perm (Fin 1782)))) := by
          rw [hsub, Subgroup.subgroupOf_map_subtype]
      _ = 161280 := by
          simpa [CFSG.Sporadic.SuzOddCore.centM] using hcardCentM
  have hcardE1 : Nat.card (Subgroup.centralizer ({e1} : Set ↥suzM)) = 161280 := by
    have hmap := CFSG.centralizer_singleton_map (MulAut.conj n) t
    rw [MulAut.conj_apply, hconj_t] at hmap
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj n).injective, hcard_t]
  have hcardTe1 : Nat.card (Subgroup.centralizer ({t * e1} : Set ↥suzM)) = 161280 := by
    have hconj_eq : t * e1 = n ^ 2 * t * (n ^ 2)⁻¹ := by
      calc t * e1 = n * e1 * n⁻¹ := hconj_e1.symm
        _ = n * (n * t * n⁻¹) * n⁻¹ := by rw [hconj_t]
        _ = n ^ 2 * t * (n ^ 2)⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
    have hmap := CFSG.centralizer_singleton_map (MulAut.conj (n ^ 2)) t
    rw [MulAut.conj_apply, ← hconj_eq] at hmap
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj (n ^ 2)).injective, hcard_t]
  have hcent_card : ∀ e ∈ Et, e ≠ 1 →
      Nat.card (Subgroup.centralizer ({e} : Set ↥suzM)) = 161280 := by
    intro e he he1
    change e ∈ (Et : Set ↥suzM) at he
    rw [hEset] at he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · exact hcard_t
    · exact hcardE1
    · exact hcardTe1
  have hncentK_amb : suzK ≤
      Subgroup.centralizer ({suzWord suzWordN} : Set (Equiv.Perm (Fin 1782))) := by
    unfold suzK
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcNA.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcNB.symm
  have he1centK_amb : suzK ≤
      Subgroup.centralizer ({(e1 : ↥suzM).val} : Set (Equiv.Perm (Fin 1782))) := by
    unfold suzK
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (by simpa [suzA, e1, n, t] using hce1A.symm)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (by simpa [suzB, e1, n, t] using hce1B.symm)
  have hncentKt : n ∈ Subgroup.centralizer (Kt : Set ↥suzM) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hncentK_amb (Subgroup.mem_subgroupOf.mp hk))
  have hKcentT : ∀ k ∈ Kt, k * t = t * k := by
    intro k hk
    apply Subtype.ext
    exact hKcent0 k.val (Subgroup.mem_subgroupOf.mp hk)
  have hKcentE1 : ∀ k ∈ Kt, k * e1 = e1 * k := by
    intro k hk
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (he1centK_amb (Subgroup.mem_subgroupOf.mp hk))
  have hfixfree : ∀ e ∈ Et, e ≠ 1 → n * e * n⁻¹ ≠ e := by
    intro e he he1
    change e ∈ (Et : Set ↥suzM) at he
    rw [hEset] at he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · rw [hconj_t]
      exact he1t
    · rw [hconj_e1]
      intro h
      exact ht1 (mul_right_cancel (by rw [h, one_mul]))
    · rw [hconj_te1]
      intro h
      have h1 : t * 1 = t * e1 := by
        calc t * 1 = t := mul_one t
          _ = t * e1 := h
      exact he1ne (mul_left_cancel h1).symm
  have hKinfE : Kt ⊓ Et = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxE⟩ := Subgroup.mem_inf.mp hx
    by_contra hx1
    have hxn : x * n = n * x := Subgroup.mem_centralizer_iff.mp hncentKt x hxK
    have hfix : n * x * n⁻¹ = x := by
      rw [← hxn]
      group
    exact hfixfree x hxE hx1 hfix
  have hKleCentE : Kt ≤ Subgroup.centralizer (Et : Set ↥suzM) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    change e ∈ (Et : Set ↥suzM) at he
    rw [hEset] at he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · rw [mul_one, one_mul]
    · exact (hKcentT x hx).symm
    · exact (hKcentE1 x hx).symm
    · calc (t * e1) * x = t * (e1 * x) := by rw [mul_assoc]
        _ = t * (x * e1) := by rw [← hKcentE1 x hx]
        _ = (t * x) * e1 := by rw [mul_assoc]
        _ = (x * t) * e1 := by rw [← hKcentT x hx]
        _ = x * (t * e1) := by rw [mul_assoc]
  have hEcent : Et ≤ Subgroup.centralizer (Et : Set ↥suzM) := by
    have hpair : ({t, e1} : Set ↥suzM).Pairwise Commute := by
      intro x hx y hy _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Commute.refl t
      · exact hcomm
      · exact hcomm.symm
      · exact Commute.refl e1
    have hcommE : IsMulCommutative Et := by
      change IsMulCommutative (Subgroup.closure ({t, e1} : Set ↥suzM))
      exact Subgroup.isMulCommutative_closure hpair
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hcommE
  have hsup_le_centE : Kt ⊔ Et ≤ Subgroup.centralizer (Et : Set ↥suzM) :=
    sup_le hKleCentE hEcent
  have hKtcard : Nat.card Kt = 20160 := by
    change Nat.card (suzK.subgroupOf suzM) = 20160
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKsuzM).toEquiv, hKcard]
  have hdisj : Disjoint Kt Et := disjoint_iff_inf_le.mpr (le_of_eq hKinfE)
  have hnormal : Et ≤ Subgroup.normalizer (Kt : Set ↥suzM) := by
    have hEcentK : Et ≤ Subgroup.centralizer (Kt : Set ↥suzM) :=
      Subgroup.le_centralizer_iff.mpr hKleCentE
    exact hEcentK.trans (Subgroup.centralizer_le_normalizer (Kt : Set ↥suzM))
  have hcard_sup : Nat.card (Kt ⊔ Et : Subgroup ↥suzM) = 20160 * 4 := by
    have hmain := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (G := ↥suzM) Kt Et hnormal hdisj
    rw [hmain, hKtcard, hEcard]
  have hσcent_t : σ ∈ Subgroup.centralizer ({t} : Set ↥suzM) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hctD
  have hσnotcent_E : σ ∉ Subgroup.centralizer (Et : Set ↥suzM) := by
    intro hσc
    have he1E : e1 ∈ Et := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hcomm' : e1 * σ = σ * e1 := Subgroup.mem_centralizer_iff.mp hσc e1 he1E
    have hval : (e1 : ↥suzM).val * (σ : ↥suzM).val =
        (σ : ↥suzM).val * (e1 : ↥suzM).val := congrArg Subtype.val hcomm'
    exact hncD hval.symm
  have hcent_le : Subgroup.centralizer (Et : Set ↥suzM) ≤
      Subgroup.centralizer ({t} : Set ↥suzM) := by
    refine Subgroup.centralizer_le ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hcent_ne : Subgroup.centralizer (Et : Set ↥suzM) ≠
      Subgroup.centralizer ({t} : Set ↥suzM) := by
    intro hEq
    exact hσnotcent_E (hEq ▸ hσcent_t)
  have hcardCent_le : Nat.card (Subgroup.centralizer (Et : Set ↥suzM)) ≤ 80640 := by
    let C := Subgroup.centralizer (Et : Set ↥suzM)
    let Ct := Subgroup.centralizer ({t} : Set ↥suzM)
    let H : Subgroup Ct := C.subgroupOf Ct
    have hHne : H ≠ ⊤ := by
      intro htop
      change C.subgroupOf Ct = ⊤ at htop
      exact hcent_ne (le_antisymm hcent_le (Subgroup.subgroupOf_eq_top.mp htop))
    have hidx : 2 ≤ H.index := by
      have h1 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : H.index ≠ 1 := fun h => hHne ((Subgroup.index_eq_one).mp h)
      omega
    have hmul : Nat.card H * H.index = Nat.card Ct := Subgroup.card_mul_index H
    have hcardH : Nat.card H = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcent_le).toEquiv
    have hcardCt : Nat.card Ct = 161280 := hcard_t
    rw [hcardH, hcardCt] at hmul
    have h2 : 2 * Nat.card C ≤ 161280 := by
      calc 2 * Nat.card C = Nat.card C * 2 := by ring
        _ ≤ Nat.card C * H.index := Nat.mul_le_mul_left _ hidx
        _ = 161280 := hmul
    change Nat.card C ≤ 80640
    omega
  have hcentE : Subgroup.centralizer (Et : Set ↥suzM) = Kt ⊔ Et := by
    refine (Subgroup.eq_of_le_of_card_ge hsup_le_centE ?_).symm
    rw [hcard_sup]
    norm_num
    exact hcardCent_le
  have hKtmap : Kt.map suzM.subtype = suzK := by
    change (suzK.subgroupOf suzM).map suzM.subtype = suzK
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKsuzM]
  have hKtperf : ⁅Kt, Kt⁆ = Kt := by
    apply Subgroup.map_injective suzM.subtype_injective
    rw [Subgroup.map_commutator, hKtmap, hKperf]
  have hT : ∀ t' ∈ Et, ∀ q ∈ Kt ⊔ Et, t' * q = q * t' := by
    intro t' ht' q hq
    exact Subgroup.mem_centralizer_iff.mp (hsup_le_centE hq) t' ht'
  have hQnorm : Kt ⊔ Et ≤ Subgroup.normalizer (Kt : Set ↥suzM) :=
    sup_le Subgroup.le_normalizer hnormal
  have hYn : ∀ q ∈ Kt ⊔ Et, ∀ y ∈ Kt, q * y * q⁻¹ ∈ Kt := by
    intro q hq y hy
    exact (Subgroup.mem_normalizer_iff.mp (hQnorm hq) y).1 hy
  have hderC : ⁅Subgroup.centralizer (Et : Set ↥suzM),
      Subgroup.centralizer (Et : Set ↥suzM)⁆ = Kt := by
    rw [hcentE]
    refine le_antisymm ?_ ?_
    · exact CFSG.GF2Type.Widths1112.commutator_le_of_sup_central
        (G := ↥suzM) (Q := Kt ⊔ Et) (Y := Kt) (T := Et) le_sup_left hYn rfl hT
    · calc Kt = ⁅Kt, Kt⁆ := hKtperf.symm
        _ ≤ ⁅Kt ⊔ Et, Kt ⊔ Et⁆ := Subgroup.commutator_mono (H₁ := Kt) (H₂ := Kt)
          (K₁ := Kt ⊔ Et) (K₂ := Kt ⊔ Et) le_sup_left le_sup_left
  have hnnormal : n ∈ Subgroup.normalizer (Et : Set ↥suzM) := by
    have hmap_le : Et.map (MulAut.conj n).toMonoidHom ≤ Et := by
      change (Subgroup.closure ({t, e1} : Set ↥suzM)).map
        (MulAut.conj n).toMonoidHom ≤ Et
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro x ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · change (MulAut.conj n) t ∈ Et
        rw [MulAut.conj_apply, hconj_t]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · change (MulAut.conj n) e1 ∈ Et
        rw [MulAut.conj_apply, hconj_e1]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    have hcard_map : Nat.card (Et.map (MulAut.conj n).toMonoidHom) = Nat.card Et :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hmap : Et.map (MulAut.conj n).toMonoidHom = Et :=
      Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard_map.symm)
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap
  exact ⟨Et, n, hEcard, hsq, hcent_card, hcentE, hKinfE, hKleCentE, hderC, hKtperf,
    hKtcard, hordn, hncentKt, hnnormal, hfixfree⟩


private theorem fourGroupAt_transport {S T : Type*} [Group S] [Group T] (f : S ≃* T)
    {E H : Subgroup T} {n : T} (h : Sol78FourGroupAt E H n) :
    Sol78FourGroupAt (E.map f.symm.toMonoidHom) (H.map f.symm.toMonoidHom) (f.symm n) := by
  obtain ⟨hEcard, hsq, hcent, hcentE, hHE, hHle, hderC, hderH, hHcard,
    hordn, hnCH, hnNE, hfix⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective f.symm.injective, hEcard]
  · rintro e ⟨x, hx, rfl⟩
    rw [← map_pow, hsq x hx, map_one]
  · rintro e ⟨x, hx, rfl⟩ hne
    have hxne : x ≠ 1 := fun hx1 => hne (by rw [hx1, map_one])
    change Nat.card (Subgroup.centralizer ({f.symm x} : Set S)) = 161280
    rw [← CFSG.centralizer_singleton_map f.symm x,
      Subgroup.card_map_of_injective f.symm.injective, hcent x hx hxne]
  · rw [← CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq f.symm E, hcentE,
      Subgroup.map_sup]
  · rw [← Subgroup.map_inf_eq H E f.symm.toMonoidHom f.symm.injective, hHE,
      Subgroup.map_bot]
  · rw [← CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq f.symm E]
    exact Subgroup.map_mono hHle
  · rw [← CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq f.symm E,
      ← Subgroup.map_commutator, hderC]
  · rw [← Subgroup.map_commutator, hderH]
  · rw [Subgroup.card_map_of_injective f.symm.injective, hHcard]
  · rw [MulEquiv.orderOf_eq, hordn]
  · rw [← CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq f.symm H]
    exact Subgroup.mem_map_of_mem f.symm.toMonoidHom hnCH
  · rw [← Subgroup.map_equiv_normalizer_eq E f.symm]
    exact Subgroup.mem_map_of_mem f.symm.toMonoidHom hnNE
  · rintro e ⟨x, hx, rfl⟩ hne hconj
    exact hfix x hx (fun hx1 => hne (by rw [hx1, map_one])) (by
      have := congrArg f hconj
      simpa using this)

theorem sol78Lemma44SuzFourGroup_holds :
    Sol78Lemma44SuzFourGroup := by
  intro S _ hS
  obtain ⟨eS⟩ := hS
  obtain ⟨E, n, h⟩ := suzFourGroup_data
  exact ⟨_, _, _, fourGroupAt_transport (eS.trans CFSG.Sporadic.SuzOddCore.suzEquivM) h⟩

theorem sol78Lemma44SuzFourGroup_l34_holds :
    ∀ (S : Type) [Group S], CFSG.Blueprint.NativeSporadic.IsSporadic S .Suz →
      ∃ (E₀ H₀ : Subgroup S) (n : S),
        (Nat.card E₀ = 4 ∧ (∀ e ∈ E₀, e ^ 2 = 1) ∧
          (∀ e ∈ E₀, e ≠ 1 → Nat.card (Subgroup.centralizer ({e} : Set S)) = 161280) ∧
          Subgroup.centralizer (E₀ : Set S) = H₀ ⊔ E₀ ∧ H₀ ⊓ E₀ = ⊥ ∧
          H₀ ≤ Subgroup.centralizer (E₀ : Set S) ∧
          ⁅Subgroup.centralizer (E₀ : Set S), Subgroup.centralizer (E₀ : Set S)⁆ = H₀ ∧
          ⁅H₀, H₀⁆ = H₀ ∧ Nat.card H₀ = 20160 ∧
          orderOf n = 3 ∧ n ∈ Subgroup.centralizer (H₀ : Set S) ∧
          n ∈ Subgroup.normalizer (E₀ : Set S) ∧
          ∀ e ∈ E₀, e ≠ 1 → n * e * n⁻¹ ≠ e) ∧
        CFSG.Blueprint.LieModel ↥H₀ .PSL 3 2 2 := by
  intro S _ hS
  obtain ⟨eS⟩ := hS
  obtain ⟨hRA, hRB, _, _, _, _, _, _⟩ := suzAB_facts
  obtain ⟨hKsuzM, -, -, hKcard⟩ := suzK_facts
  obtain ⟨E, n, h⟩ := suzFourGroup_data
  let f : S ≃* ↥suzM := eS.trans CFSG.Sporadic.SuzOddCore.suzEquivM
  have hK : CFSG.Blueprint.LieModel ↥suzK .PSL 3 2 2 :=
    lieModel_closure_of_rep (a := suzA) (b := suzB) hRA hRB hKcard
  refine ⟨E.map f.symm.toMonoidHom, (suzK.subgroupOf suzM).map f.symm.toMonoidHom, f.symm n,
    fourGroupAt_transport f h, ?_⟩
  exact hK.of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hKsuzM).symm.trans
    (Subgroup.equivMapOfInjective _ f.symm.toMonoidHom f.symm.injective))

end CFSG.EvenSporadicStandard.Solomon78
