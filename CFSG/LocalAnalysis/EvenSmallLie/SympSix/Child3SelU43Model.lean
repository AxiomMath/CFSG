module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Check
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Gen
public import CFSG.LieType.Multipliers.U43
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.StronglyEmbedded.ParityCriterion

public noncomputable section

namespace CFSG.EvenSmallLie.Child3.SelU43

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf size_pushWords pushWords_getElem!
  chain_strong_spec chain_word_mem getElem!_rawInvs')

theorem autGens_size : autGens.size = 4 := rfl

theorem autS_size : autS.size = 10 := by
  rw [autS, size_pushWords, autGens_size]
  rfl

theorem sylowGens_size : sylowGens.size = 4 := by simp [sylowGens, sylowGenWords]

theorem sylowS_size : sylowS.size = 6 := by
  rw [sylowS, size_pushWords, sylowGens_size]
  rfl

theorem chainS_size : chainS.size = 7 := rfl

@[expose] def autQ : RawSchreierDatum 820 :=
  RawSchreierDatum.ofArrays 820 (by norm_num) autS 4 (by rw [autS_size]; norm_num) autBase
    (by decide) (wordsOf 4 autWords)

@[expose] def sylowQ : RawSchreierDatum 820 :=
  RawSchreierDatum.ofArrays 820 (by norm_num) sylowS 4 (by rw [sylowS_size]; norm_num) sylowBase
    (by decide) (wordsOf 4 sylowWords)

@[expose] def tQ : RawSchreierDatum 820 :=
  RawSchreierDatum.ofArrays 820 (by norm_num) chainS 2 (by rw [chainS_size]; norm_num) chainBase
    (by decide) chainW

@[expose] def tT : Subgroup (Equiv.Perm (Fin 820)) := tQ.originalSubgroup

@[expose] def autT : Subgroup (Equiv.Perm (Fin 820)) := autQ.originalSubgroup

@[expose] def sylowT : Subgroup (Equiv.Perm (Fin 820)) := sylowQ.originalSubgroup

theorem autChain_ok :
    rawChainOK 820 (autS.extract 0 4) autS (autBase.map Fin.val).toArray
        (wordsOf 4 autWords) 4 = true ∧
      rawOrbitSizes 820 autS (autBase.map Fin.val).toArray = [540, 252, 2, 24, 4] := by
  have h := autChain_check
  simp only [autChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem sylowChain_ok :
    sylowGenWords.all (lettersOK autS.size) = true ∧
      rawChainOK 820 (sylowS.extract 0 4) sylowS (sylowBase.map Fin.val).toArray
        (wordsOf 4 sylowWords) 4 = true ∧
      rawOrbitSizes 820 sylowS (sylowBase.map Fin.val).toArray = [256, 4] := by
  have h := sylowChain_check
  simp only [sylowChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_autT : Nat.card autT = 26127360 := by
  rw [autT, autQ, ofArrays_card (by norm_num) autChain_ok.1, autChain_ok.2]
  rfl

theorem card_sylowT : Nat.card sylowT = 1024 := by
  rw [sylowT, sylowQ, ofArrays_card (by norm_num) sylowChain_ok.2.1, sylowChain_ok.2.2]
  rfl

theorem tChain_ok :
    rawChainOK 820 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW 4 = true ∧
      rawOrbitSizes 820 chainS (chainBase.map Fin.val).toArray = [540, 252, 24] := by
  have h := tChain_check
  simp only [tChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem card_tT : Nat.card tT = 3265920 := by
  rw [tT, tQ, ofArrays_card (by norm_num) tChain_ok.1, tChain_ok.2]
  rfl

theorem autS_spec :
    ∀ j < autS.size, Rep 820 autS[j]! (permOfArr 820 autS[j]!) ∧
      Rep 820 (rawInvs 820 autS)[j]! (permOfArr 820 autS[j]!)⁻¹ ∧ permOfArr 820 autS[j]! ∈ autT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [autS_size]; norm_num) (hb := by decide)
    autChain_ok.1

theorem sylowS_spec :
    ∀ j < sylowS.size, Rep 820 sylowS[j]! (permOfArr 820 sylowS[j]!) ∧
      Rep 820 (rawInvs 820 sylowS)[j]! (permOfArr 820 sylowS[j]!)⁻¹ ∧
        permOfArr 820 sylowS[j]! ∈ sylowT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [sylowS_size]; norm_num) (hb := by decide)
    sylowChain_ok.2.1

theorem chainS_spec :
    ∀ j < chainS.size, Rep 820 chainS[j]! (permOfArr 820 chainS[j]!) ∧
      Rep 820 (rawInvs 820 chainS)[j]! (permOfArr 820 chainS[j]!)⁻¹ ∧
        permOfArr 820 chainS[j]! ∈ tT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [chainS_size]; norm_num) (hb := by decide)
    tChain_ok.1

theorem autS_getElem! {i : ℕ} (hi : i < 4) : autS[i]! = autGens[i]! := by
  rw [autS, pushWords_getElem! _ _ (by rw [autGens_size]; omega)]

theorem sylowS_getElem! {i : ℕ} (hi : i < 4) : sylowS[i]! = sylowGens[i]! := by
  rw [sylowS, pushWords_getElem! _ _ (by rw [sylowGens_size]; omega)]

theorem autT_eq : autT = Subgroup.closure {g | ∃ i < 4, permOfArr 820 autS[i]! = g} := by
  rw [autT, autQ, ofArrays_originalSubgroup]

theorem tT_eq : tT = Subgroup.closure {g | ∃ i < 2, permOfArr 820 chainS[i]! = g} := by
  rw [tT, tQ, ofArrays_originalSubgroup]

theorem sylowT_eq : sylowT = Subgroup.closure {g | ∃ i < 4, permOfArr 820 sylowS[i]! = g} := by
  rw [sylowT, sylowQ, ofArrays_originalSubgroup]

theorem sylowGens_mem {i : ℕ} (hi : i < 4) :
    permOfArr 820 sylowGens[i]! ∈ autT := by
  have hw : lettersOK autS.size (sylowGenWords.getD i []) = true :=
    List.all_eq_true.1 sylowChain_ok.1 (sylowGenWords.getD i []) (by
      rw [List.getD_eq_getElem _ _ (by simpa [sylowGenWords] using hi)]
      exact List.getElem_mem _)
  have h := (chain_word_mem (hn := by norm_num) (hk := by rw [autS_size]; norm_num)
    (hb := by decide) autChain_ok.1 _ hw).2
  have hi' : i < sylowGenWords.length := by simpa [sylowGenWords] using hi
  have e : sylowGens[i]! = autW (sylowGenWords.getD i []) := by
    rw [sylowGens, getElem!_pos _ i (by simpa using hi'), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hi']
  rw [e]
  exact h

theorem sylowT_le_autT : sylowT ≤ autT := by
  rw [sylowT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [sylowS_getElem! hi]
  exact sylowGens_mem hi

theorem norm_ok : ∀ g ∈ [deltaArr, sigmaArr],
    isInvA 820 g (invCand 820 g) = true ∧ ∀ x ∈ [tabA, tabB],
      siftA 820 (rawLevels 820 chainS (chainBase.map Fin.val).toArray)
        (chainBase.map Fin.val).toArray 0 (conjA 820 g x) = true := by
  have h := norm_check
  simp only [normCheck, List.all_eq_true, Bool.and_eq_true] at h
  exact h

theorem conj_mem_of_norm
    {g x : Array ℕ} {G X : Equiv.Perm (Fin 820)} (hg : Rep 820 g G) (hx : Rep 820 x X)
    (hgm : g ∈ [deltaArr, sigmaArr]) (hxm : x ∈ [tabA, tabB]) : G * X * G⁻¹ ∈ tT := by
  obtain ⟨hinv, hs⟩ := norm_ok g hgm
  exact (ofArrays_mem_iff (by norm_num) tChain_ok.1 (rep_conjA hg hx hinv)).1 (hs x hxm)

theorem chainS_mem_list {j : ℕ} (hj : j < 2) : chainS[j]! ∈ [tabA, tabB] := by
  interval_cases j
  · exact (show chainS[0]! = tabA from rfl) ▸ List.mem_cons_self
  · exact (show chainS[1]! = tabB from rfl) ▸ List.mem_cons_of_mem _ List.mem_cons_self

theorem autS_perm_eq {i : ℕ} (hi : i < 2) : permOfArr 820 autS[i]! = permOfArr 820 chainS[i]! := by
  rw [autS_getElem! (by omega)]
  interval_cases i
  · exact congrArg (permOfArr 820)
      ((show autGens[0]! = tabA from rfl).trans (show chainS[0]! = tabA from rfl).symm)
  · exact congrArg (permOfArr 820)
      ((show autGens[1]! = tabB from rfl).trans (show chainS[1]! = tabB from rfl).symm)

theorem autT_le_normalizer :
    autT ≤ Subgroup.normalizer (tT : Set (Equiv.Perm (Fin 820))) := by
  refine le_normalizer_of_conj_gens tT_eq autT_eq ?_
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  have hx := chainS_spec j (by rw [chainS_size]; omega)
  by_cases hi2 : i < 2
  · rw [autS_perm_eq hi2]
    have hg := (chainS_spec i (by rw [chainS_size]; omega)).2.2
    exact tT.mul_mem (tT.mul_mem hg hx.2.2) (tT.inv_mem hg)
  · have hg := (autS_spec i (by rw [autS_size]; omega)).1
    refine conj_mem_of_norm hg hx.1 ?_ (chainS_mem_list hj)
    rw [autS_getElem! hi]
    interval_cases i
    · rw [show autGens[2]! = deltaArr by simp [autGens]]
      exact List.mem_cons_self
    · rw [show autGens[3]! = sigmaArr by simp [autGens]]
      exact List.mem_cons_of_mem _ List.mem_cons_self

theorem eq_one_of_comm_tT
    {c : Equiv.Perm (Fin 820)} (hc : ∀ g ∈ tT, g * c = c * g) : c = 1 :=
  eq_one_of_centOK chainS_spec cent_check hc

theorem tT_eq_psi :
    tT = Subgroup.closure {psi xElt, psi yElt} := by
  rw [tT_eq]
  congr 1
  have h0 := (chainS_spec 0 (by rw [chainS_size]; norm_num)).1
  have h1 := (chainS_spec 1 (by rw [chainS_size]; norm_num)).1
  rw [show chainS[0]! = tabA from rfl] at h0
  rw [show chainS[1]! = tabB from rfl] at h1
  have e0 : permOfArr 820 chainS[0]! = psi xElt := h0.unique rep_tabA
  have e1 : permOfArr 820 chainS[1]! = psi yElt := h1.unique rep_tabB
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem closure_xy' :
    Subgroup.closure ({xElt, yElt} : Set X₀) = ⊤ := by
  have : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  apply Subgroup.eq_top_of_le_card
  have hmap : (Subgroup.closure ({xElt, yElt} : Set X₀)).map psi =
      Subgroup.closure {psi xElt, psi yElt} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  rw [card_X₀, ← card_tT, tT_eq_psi, ← hmap]
  exact Nat.card_le_card_of_surjective _ (psi.subgroupMap_surjective _)

theorem psi_injective' : Function.Injective psi := by
  have : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  have hle : Nat.card X₀ ≤ Nat.card psi.range := by
    rw [card_X₀, ← card_tT, tT_eq_psi]
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨xElt, rfl⟩
    · exact ⟨yElt, rfl⟩
  have hb := psi.rangeRestrict_surjective.bijective_of_nat_card_le hle
  exact fun g h hgh => hb.1 (Subtype.ext hgh)

theorem psi_range : psi.range = tT := by
  rw [tT_eq_psi, MonoidHom.range_eq_map, ← closure_xy', MonoidHom.map_closure, Set.image_pair]

@[expose] def tEquiv : X₀ ≃* tT :=
  (MonoidHom.ofInjective psi_injective').trans (MulEquiv.subgroupCongr psi_range)

@[expose] def projSUEquiv :
    CFSG.Assembly.RankThreeEven.projSU 4 3 1 ≃* tT :=
  have : Fintype (GaloisField 3 (2 * 1)) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 3 (2 * 1)) = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 (2 * 1) (by norm_num), F9.card_eq]
    norm_num
  ((CFSG.RankThree.PartTwo.Sec4.projSUEquivStatedProj 4 3 1).trans
    (CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 4 (3 ^ 1))).trans tEquiv

theorem card_mulAut_tT_le :
    Nat.card (MulAut tT) ≤ 8 * Nat.card tT := by
  open CFSG.ComponentClassification.OuterAutomorphisms in
  have h8 : Nat.card (Outer tT) ∣ 8 := by
    rw [← Nat.card_congr (equivalence projSUEquiv).toEquiv]
    have := CFSG.RankThree.PartTwo.Sec4.card_outer_projSU_dvd 4 3 1 le_rfl (by norm_num)
      (by norm_num)
    simpa using this
  open CFSG.ComponentClassification.OuterAutomorphisms in
  rw [(inner tT).card_eq_card_quotient_mul_card_subgroup]
  refine Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) h8) ?_
  exact Nat.card_le_card_of_surjective _ (MulAut.conj : tT →* MulAut tT).rangeRestrict_surjective

theorem exists_autModel
    {D : Type} [Group D] (e : D ≃* X₀) :
    ∃ M : CFSG.GH74.KGroups.AutModel D (Equiv.Perm (Fin 820)), M.P = tT ∧ M.A = autT := by
  have hcard : Nat.card (MulAut tT) ≤ Nat.card autT := by
    rw [card_autT]
    have := card_mulAut_tT_le
    rw [card_tT] at this
    omega
  obtain ⟨Φ, hΦ⟩ := CFSG.GH74.KGroups.exists_mulEquiv_of_squeeze tT autT autT_le_normalizer
    (fun σ _ hσ => eq_one_of_comm_tT fun g hg => (hσ g hg).symm) hcard
  exact ⟨CFSG.GH74.KGroups.AutModel.ofRealization tT autT (e.trans tEquiv) Φ hΦ, rfl, rfl⟩

end CFSG.EvenSmallLie.Child3.SelU43
