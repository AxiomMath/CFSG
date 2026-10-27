module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Check
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Gen
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public noncomputable section

namespace CFSG.EvenSmallLie.Child3.SelL39

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.J2Cover
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf size_pushWords pushWords_getElem!
  chain_strong_spec chain_word_mem getElem!_rawInvs')

theorem card_F9 : Nat.card F9 = 9 := by rw [Nat.card_eq_fintype_card, F9.card_eq]

theorem cube_eq_one_F9 : ∀ x : F9, x * x * x = 1 → x = 1 := by decide

theorem scalars_F9 : scalars 3 F9 = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc3, hA⟩
  rw [Subgroup.mem_bot]
  have h1 : (c : F9) = 1 := cube_eq_one_F9 _ (by
    have := congrArg (fun u : F9ˣ => (u : F9)) hc3
    simpa [pow_succ, mul_assoc] using this)
  apply Subtype.ext
  rw [hA, h1]
  simp

theorem card_projectiveSL_F9 : Nat.card (projectiveSL 3 F9) = 42456960 := by
  rw [card_projectiveSL, card_SL_eq (by norm_num), scalars_F9, Subgroup.card_bot, card_F9]
  decide

theorem mulVec_eq_mv3 (M : Matrix (Fin 3) (Fin 3) F9) (v : V3) : M *ᵥ v = mv3 M v := by
  funext i
  simp [mulVec, dotProduct, Fin.sum_univ_three, mv3]

theorem det_MA : MA.det = 1 := by decide +kernel

theorem det_MB : MB.det = 1 := by decide +kernel

@[expose] def slA : SpecialLinearGroup (Fin 3) F9 := ⟨MA, det_MA⟩

@[expose] def slB : SpecialLinearGroup (Fin 3) F9 := ⟨MB, det_MB⟩

@[expose] def xL : projectiveSL 3 F9 := proj 3 F9 slA

@[expose] def yL : projectiveSL 3 F9 := proj 3 F9 slB

theorem rep_ptArr (A : SpecialLinearGroup (Fin 3) F9) :
    Rep 91 (ptArr (A : Matrix (Fin 3) (Fin 3) F9)) (psiL (proj 3 F9 A)) := fun i => by
  rw [ptArr, getElem!_ofFn_nat _ i.2, psiL_proj_apply, ← mulVec_eq_mv3]
  rfl

theorem rep_pA : Rep 91 pA (psiL xL) := rep_ptArr slA

theorem rep_pB : Rep 91 pB (psiL yL) := rep_ptArr slB

theorem t1S_size : t1S.size = 7 := by
  rw [t1S, size_pushWords]
  rfl

theorem tS_size : tS.size = 7 := by
  rw [tS, size_pushWords]
  rfl

@[expose] def t1Q : RawSchreierDatum 91 :=
  RawSchreierDatum.ofArrays 91 (by norm_num) t1S 2 (by rw [t1S_size]; norm_num) t1Base
    (by decide) (wordsOf 2 tWords)

@[expose] def tQ : RawSchreierDatum 182 :=
  RawSchreierDatum.ofArrays 182 (by norm_num) tS 2 (by rw [tS_size]; norm_num) tBase
    (by decide) (wordsOf 2 tWords)

@[expose] def t1T : Subgroup (Equiv.Perm (Fin 91)) := t1Q.originalSubgroup

@[expose] def tT : Subgroup (Equiv.Perm (Fin 182)) := tQ.originalSubgroup

theorem tChain_ok :
    (rawChainOK 91 (t1S.extract 0 2) t1S (t1Base.map Fin.val).toArray (wordsOf 2 tWords) 4 =
        true ∧
      rawOrbitSizes 91 t1S (t1Base.map Fin.val).toArray = [91, 90, 8, 81, 8]) ∧
    (rawChainOK 182 (tS.extract 0 2) tS (tBase.map Fin.val).toArray (wordsOf 2 tWords) 4 =
        true ∧
      rawOrbitSizes 182 tS (tBase.map Fin.val).toArray = [91, 90, 8, 81, 8]) ∧
    isInvA 91 lA (invCand 91 lA) = true ∧ isInvA 91 lB (invCand 91 lB) = true := by
  have h := tChain_check
  simp only [tChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, ⟨h.1.1.1.2, h.1.1.2⟩, h.1.2, h.2⟩

theorem card_t1T : Nat.card t1T = 42456960 := by
  rw [t1T, t1Q, ofArrays_card (by norm_num) tChain_ok.1.1, tChain_ok.1.2]
  rfl

theorem card_tT : Nat.card tT = 42456960 := by
  rw [tT, tQ, ofArrays_card (by norm_num) tChain_ok.2.1.1, tChain_ok.2.1.2]
  rfl

theorem t1S_spec :
    ∀ j < t1S.size, Rep 91 t1S[j]! (permOfArr 91 t1S[j]!) ∧
      Rep 91 (rawInvs 91 t1S)[j]! (permOfArr 91 t1S[j]!)⁻¹ ∧ permOfArr 91 t1S[j]! ∈ t1T :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [t1S_size]; norm_num) (hb := by decide)
    tChain_ok.1.1

theorem tS_spec :
    ∀ j < tS.size, Rep 182 tS[j]! (permOfArr 182 tS[j]!) ∧
      Rep 182 (rawInvs 182 tS)[j]! (permOfArr 182 tS[j]!)⁻¹ ∧ permOfArr 182 tS[j]! ∈ tT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [tS_size]; norm_num) (hb := by decide)
    tChain_ok.2.1.1

theorem t1S_getElem_zero : t1S[0]! = pA := by
  rw [t1S, pushWords_getElem! _ _ (by norm_num)]
  simp

theorem t1S_getElem_one : t1S[1]! = pB := by
  rw [t1S, pushWords_getElem! _ _ (by norm_num)]
  simp

theorem tS_getElem_zero : tS[0]! = qA := by
  rw [tS, pushWords_getElem! _ _ (by norm_num)]
  simp

theorem tS_getElem_one : tS[1]! = qB := by
  rw [tS, pushWords_getElem! _ _ (by norm_num)]
  simp

theorem t1T_eq : t1T = Subgroup.closure {g | ∃ i < 2, permOfArr 91 t1S[i]! = g} := by
  rw [t1T, t1Q, ofArrays_originalSubgroup]

theorem tT_eq : tT = Subgroup.closure {g | ∃ i < 2, permOfArr 182 tS[i]! = g} := by
  rw [tT, tQ, ofArrays_originalSubgroup]

theorem closure_two {n : ℕ} (S : Array (Array ℕ)) :
    Subgroup.closure {g | ∃ i < 2, permOfArr n S[i]! = g} =
      Subgroup.closure {permOfArr n S[0]!, permOfArr n S[1]!} := by
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem perm_pA : permOfArr 91 pA = psiL xL := by
  have h := (t1S_spec 0 (by rw [t1S_size]; norm_num)).1
  rw [t1S_getElem_zero] at h
  exact h.unique rep_pA

theorem perm_pB : permOfArr 91 pB = psiL yL := by
  have h := (t1S_spec 1 (by rw [t1S_size]; norm_num)).1
  rw [t1S_getElem_one] at h
  exact h.unique rep_pB

theorem t1T_eq_psi :
    t1T = Subgroup.closure {psiL xL, psiL yL} := by
  rw [t1T_eq, closure_two, t1S_getElem_zero, t1S_getElem_one, perm_pA, perm_pB]

theorem closure_xyL :
    Subgroup.closure ({xL, yL} : Set (projectiveSL 3 F9)) = ⊤ := by
  have : Finite (projectiveSL 3 F9) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL_F9]; norm_num)
  apply Subgroup.eq_top_of_le_card
  have hmap : (Subgroup.closure ({xL, yL} : Set (projectiveSL 3 F9))).map psiL =
      Subgroup.closure {psiL xL, psiL yL} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  rw [card_projectiveSL_F9, ← card_t1T, t1T_eq_psi, ← hmap]
  exact Nat.card_le_card_of_surjective _ (psiL.subgroupMap_surjective _)

theorem psiL_injective : Function.Injective psiL := by
  have : Finite (projectiveSL 3 F9) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL_F9]; norm_num)
  have hle : Nat.card (projectiveSL 3 F9) ≤ Nat.card psiL.range := by
    rw [card_projectiveSL_F9, ← card_t1T, t1T_eq_psi]
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨xL, rfl⟩
    · exact ⟨yL, rfl⟩
  have hb := psiL.rangeRestrict_surjective.bijective_of_nat_card_le hle
  exact fun g h hgh => hb.1 (Subtype.ext hgh)

theorem psiL_range : psiL.range = t1T := by
  rw [t1T_eq_psi, MonoidHom.range_eq_map, ← closure_xyL, MonoidHom.map_closure, Set.image_pair]

@[expose] def t1Equiv : projectiveSL 3 F9 ≃* t1T :=
  (MonoidHom.ofInjective psiL_injective).trans (MulEquiv.subgroupCongr psiL_range)

theorem blockHom_castAdd {n m : ℕ} (a : Equiv.Perm (Fin n)) (b : Equiv.Perm (Fin m))
    (i : Fin n) :
    CFSG.GH74.KGroups.blockHom n m (a, b) (Fin.castAdd m i) = Fin.castAdd m (a i) := by
  simp [CFSG.GH74.KGroups.blockHom, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem blockHom_natAdd {n m : ℕ} (a : Equiv.Perm (Fin n)) (b : Equiv.Perm (Fin m))
    (j : Fin m) :
    CFSG.GH74.KGroups.blockHom n m (a, b) (Fin.natAdd n j) = Fin.natAdd n (b j) := by
  simp [CFSG.GH74.KGroups.blockHom, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem blockHom_apply_lt {n m : ℕ} (a : Equiv.Perm (Fin n)) (b : Equiv.Perm (Fin m))
    (x : Fin (n + m)) (hx : (x : ℕ) < n) :
    ((CFSG.GH74.KGroups.blockHom n m (a, b) x : Fin (n + m)) : ℕ) = a ⟨x, hx⟩ := by
  have h := blockHom_castAdd a b ⟨x, hx⟩
  rw [show Fin.castAdd m ⟨(x : ℕ), hx⟩ = x from Fin.ext rfl] at h
  rw [h]
  rfl

theorem blockHom_apply_ge {n m : ℕ} (a : Equiv.Perm (Fin n)) (b : Equiv.Perm (Fin m))
    (x : Fin (n + m)) (hx : n ≤ (x : ℕ)) :
    ((CFSG.GH74.KGroups.blockHom n m (a, b) x : Fin (n + m)) : ℕ) =
      n + b ⟨x - n, by have := x.2; omega⟩ := by
  have h := blockHom_natAdd a b ⟨x - n, by have := x.2; omega⟩
  rw [show Fin.natAdd n ⟨(x : ℕ) - n, _⟩ = x from Fin.ext (by simp; omega)] at h
  rw [h]
  rfl

theorem rep_blockArr {p l : Array ℕ} {a b : Equiv.Perm (Fin 91)} (hp : Rep 91 p a)
    (hl : Rep 91 l b) : Rep 182 (blockArr p l) (CFSG.GH74.KGroups.blockHom 91 91 (a, b)) := by
  intro x
  rw [blockArr, getElem!_ofFn_nat _ x.2]
  by_cases hx : (x : ℕ) < 91
  · rw [ite_eq_left hx, blockHom_apply_lt a b x hx, hp.apply hx]
  · rw [ite_eq_right hx, blockHom_apply_ge a b x (by omega), hl.apply (by have := x.2; omega)]

theorem blockHom_qA :
    CFSG.GH74.KGroups.blockHom 91 91 (permOfArr 91 pA, permOfArr 91 lA) = permOfArr 182 qA := by
  have h1 : Rep 91 pA (permOfArr 91 pA) := by
    have h := (t1S_spec 0 (by rw [t1S_size]; norm_num)).1
    rwa [t1S_getElem_zero] at h
  have h2 : Rep 91 lA (permOfArr 91 lA) := (rep_permOfArr tChain_ok.2.2.1).1
  have h3 : Rep 182 qA (permOfArr 182 qA) := by
    have h := (tS_spec 0 (by rw [tS_size]; norm_num)).1
    rwa [tS_getElem_zero] at h
  exact (rep_blockArr h1 h2).unique h3

theorem blockHom_qB :
    CFSG.GH74.KGroups.blockHom 91 91 (permOfArr 91 pB, permOfArr 91 lB) = permOfArr 182 qB := by
  have h1 : Rep 91 pB (permOfArr 91 pB) := by
    have h := (t1S_spec 1 (by rw [t1S_size]; norm_num)).1
    rwa [t1S_getElem_one] at h
  have h2 : Rep 91 lB (permOfArr 91 lB) := (rep_permOfArr tChain_ok.2.2.2).1
  have h3 : Rep 182 qB (permOfArr 182 qB) := by
    have h := (tS_spec 1 (by rw [tS_size]; norm_num)).1
    rwa [tS_getElem_one] at h
  exact (rep_blockArr h1 h2).unique h3

theorem exists_t1T_equiv_tT : Nonempty (t1T ≃* tT) := by
  have hP : t1T = Subgroup.closure {permOfArr 91 pA, permOfArr 91 pB} := by
    rw [t1T_eq, closure_two, t1S_getElem_zero, t1S_getElem_one]
  have hQ : tT = Subgroup.closure {permOfArr 182 qA, permOfArr 182 qB} := by
    rw [tT_eq, closure_two, tS_getElem_zero, tS_getElem_one]
  have ha : permOfArr 91 pA ∈ t1T := hP ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : permOfArr 91 pB ∈ t1T :=
    hP ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨φ, -, -⟩ := CFSG.GH74.KGroups.blockIso (permOfArr 91 pA) (permOfArr 91 pB)
    (permOfArr 91 lA) (permOfArr 91 lB) (permOfArr 182 qA) (permOfArr 182 qB) blockHom_qA
    blockHom_qB t1T tT hP hQ ha hb (by rw [card_tT, card_t1T])
  exact ⟨φ⟩

@[expose] def tEquiv : projectiveSL 3 F9 ≃* tT :=
  t1Equiv.trans exists_t1T_equiv_tT.some

theorem autGens_size : autGens.size = 4 := rfl

theorem autS_size : autS.size = 15 := by
  rw [autS, size_pushWords, autGens_size]
  rfl

theorem sylowGens_size : sylowGens.size = 4 := by simp [sylowGens, sylowGenWords]

theorem sylowS_size : sylowS.size = 8 := by
  rw [sylowS, size_pushWords, sylowGens_size]
  rfl

@[expose] def autQ : RawSchreierDatum 182 :=
  RawSchreierDatum.ofArrays 182 (by norm_num) autS 4 (by rw [autS_size]; norm_num) autBase
    (by decide) (wordsOf 4 autWords)

@[expose] def sylowQ : RawSchreierDatum 182 :=
  RawSchreierDatum.ofArrays 182 (by norm_num) sylowS 4 (by rw [sylowS_size]; norm_num) sylowBase
    (by decide) (wordsOf 4 sylowWords)

@[expose] def autT : Subgroup (Equiv.Perm (Fin 182)) := autQ.originalSubgroup

@[expose] def sylowT : Subgroup (Equiv.Perm (Fin 182)) := sylowQ.originalSubgroup

theorem autChain_ok :
    rawChainOK 182 (autS.extract 0 4) autS (autBase.map Fin.val).toArray
        (wordsOf 4 autWords) 4 = true ∧
      rawOrbitSizes 182 autS (autBase.map Fin.val).toArray = [182, 90, 8, 81, 8, 2] := by
  have h := autChain_check
  simp only [autChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem sylowChain_ok :
    sylowGenWords.all (lettersOK autS.size) = true ∧
      rawChainOK 182 (sylowS.extract 0 4) sylowS (sylowBase.map Fin.val).toArray
        (wordsOf 4 sylowWords) 4 = true ∧
      rawOrbitSizes 182 sylowS (sylowBase.map Fin.val).toArray = [32, 16] := by
  have h := sylowChain_check
  simp only [sylowChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_autT : Nat.card autT = 169827840 := by
  rw [autT, autQ, ofArrays_card (by norm_num) autChain_ok.1, autChain_ok.2]
  rfl

theorem card_sylowT : Nat.card sylowT = 512 := by
  rw [sylowT, sylowQ, ofArrays_card (by norm_num) sylowChain_ok.2.1, sylowChain_ok.2.2]
  rfl

theorem autS_spec :
    ∀ j < autS.size, Rep 182 autS[j]! (permOfArr 182 autS[j]!) ∧
      Rep 182 (rawInvs 182 autS)[j]! (permOfArr 182 autS[j]!)⁻¹ ∧ permOfArr 182 autS[j]! ∈ autT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [autS_size]; norm_num) (hb := by decide)
    autChain_ok.1

theorem sylowS_spec :
    ∀ j < sylowS.size, Rep 182 sylowS[j]! (permOfArr 182 sylowS[j]!) ∧
      Rep 182 (rawInvs 182 sylowS)[j]! (permOfArr 182 sylowS[j]!)⁻¹ ∧
        permOfArr 182 sylowS[j]! ∈ sylowT :=
  chain_strong_spec (hn := by norm_num) (hk := by rw [sylowS_size]; norm_num) (hb := by decide)
    sylowChain_ok.2.1

theorem autS_getElem! {i : ℕ} (hi : i < 4) : autS[i]! = autGens[i]! := by
  rw [autS, pushWords_getElem! _ _ (by rw [autGens_size]; omega)]

theorem sylowS_getElem! {i : ℕ} (hi : i < 4) : sylowS[i]! = sylowGens[i]! := by
  rw [sylowS, pushWords_getElem! _ _ (by rw [sylowGens_size]; omega)]

theorem autT_eq : autT = Subgroup.closure {g | ∃ i < 4, permOfArr 182 autS[i]! = g} := by
  rw [autT, autQ, ofArrays_originalSubgroup]

theorem sylowT_eq : sylowT = Subgroup.closure {g | ∃ i < 4, permOfArr 182 sylowS[i]! = g} := by
  rw [sylowT, sylowQ, ofArrays_originalSubgroup]

theorem autS_perm_eq {i : ℕ} (hi : i < 2) :
    permOfArr 182 autS[i]! = permOfArr 182 tS[i]! := by
  rw [autS_getElem! (by omega)]
  interval_cases i
  · rw [tS_getElem_zero, show autGens[0]! = qA by simp [autGens]]
  · rw [tS_getElem_one, show autGens[1]! = qB by simp [autGens]]

theorem tT_le_autT : tT ≤ autT := by
  rw [tT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [autT_eq, ← autS_perm_eq hi]
  exact Subgroup.subset_closure ⟨i, by omega, rfl⟩

theorem sylowGens_mem {i : ℕ} (hi : i < 4) :
    permOfArr 182 sylowGens[i]! ∈ autT := by
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

theorem norm_ok : ∀ g ∈ [sig182, gam182],
    isInvA 182 g (invCand 182 g) = true ∧ ∀ x ∈ [qA, qB],
      siftA 182 (rawLevels 182 tS (tBase.map Fin.val).toArray) (tBase.map Fin.val).toArray 0
        (conjA 182 g x) = true := by
  have h := norm_check
  simp only [normCheck, List.all_eq_true, Bool.and_eq_true] at h
  exact h

theorem conj_mem_of_norm {g x : Array ℕ}
    {G X : Equiv.Perm (Fin 182)} (hg : Rep 182 g G) (hx : Rep 182 x X)
    (hgm : g ∈ [sig182, gam182]) (hxm : x ∈ [qA, qB]) : G * X * G⁻¹ ∈ tT := by
  obtain ⟨hinv, hs⟩ := norm_ok g hgm
  exact (ofArrays_mem_iff (by norm_num) tChain_ok.2.1.1 (rep_conjA hg hx hinv)).1 (hs x hxm)

theorem tS_mem_list {j : ℕ} (hj : j < 2) : tS[j]! ∈ [qA, qB] := by
  interval_cases j
  · rw [tS_getElem_zero]
    exact List.mem_cons_self
  · rw [tS_getElem_one]
    exact List.mem_cons_of_mem _ List.mem_cons_self

theorem autT_le_normalizer :
    autT ≤ Subgroup.normalizer (tT : Set (Equiv.Perm (Fin 182))) := by
  refine le_normalizer_of_conj_gens tT_eq autT_eq ?_
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  have hx := tS_spec j (by rw [tS_size]; omega)
  by_cases hi2 : i < 2
  · rw [autS_perm_eq hi2]
    have hg := (tS_spec i (by rw [tS_size]; omega)).2.2
    exact tT.mul_mem (tT.mul_mem hg hx.2.2) (tT.inv_mem hg)
  · have hg := (autS_spec i (by rw [autS_size]; omega)).1
    refine conj_mem_of_norm hg hx.1 ?_ (tS_mem_list hj)
    rw [autS_getElem! hi]
    interval_cases i
    · rw [show autGens[2]! = sig182 by simp [autGens]]
      exact List.mem_cons_self
    · rw [show autGens[3]! = gam182 by simp [autGens]]
      exact List.mem_cons_of_mem _ List.mem_cons_self

theorem eq_one_of_comm_tT {c : Equiv.Perm (Fin 182)}
    (hc : ∀ g ∈ tT, g * c = c * g) : c = 1 :=
  eq_one_of_centOK tS_spec cent_check hc

theorem card_mulAut_tT_le :
    Nat.card (MulAut tT) ≤ 4 * Nat.card tT := by
  rw [← Nat.card_congr (MulAut.congr tEquiv).toEquiv, ← Nat.card_congr tEquiv.toEquiv]
  exact card_mulAut_projectiveSL_le card_F9

theorem exists_autModel {D : Type} [Group D]
    (e : D ≃* projectiveSL 3 F9) :
    ∃ M : CFSG.GH74.KGroups.AutModel D (Equiv.Perm (Fin 182)), M.P = tT ∧ M.A = autT := by
  have hcard : Nat.card (MulAut tT) ≤ Nat.card autT := by
    rw [card_autT]
    have := card_mulAut_tT_le
    rw [card_tT] at this
    omega
  obtain ⟨Φ, hΦ⟩ := CFSG.GH74.KGroups.exists_mulEquiv_of_squeeze tT autT autT_le_normalizer
    (fun σ _ hσ => eq_one_of_comm_tT fun g hg => (hσ g hg).symm) hcard
  exact ⟨CFSG.GH74.KGroups.AutModel.ofRealization tT autT (e.trans tEquiv) Φ hΦ, rfl, rfl⟩

end CFSG.EvenSmallLie.Child3.SelL39
