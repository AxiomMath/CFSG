module

public import CFSG.Sporadic.SuzOddCore.CTIFirst
public import CFSG.Sporadic.SuzOddCore.ThreeLocalD
public import Certificates.Certificate26680

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem rep_two_getElem! {n : ℕ} {a b : Array ℕ} {f : ℕ → Equiv.Perm (Fin n)}
    (ha : Rep n a (f 0)) (hb : Rep n b (f 1)) :
    ∀ h < 2, Rep n (#[a, b] : Array (Array ℕ))[h]! (f h) := by
  intro h hh
  interval_cases h
  · exact ha
  · exact hb

theorem rep_four_getElem! {n : ℕ} {a b c d : Array ℕ} {f : ℕ → Equiv.Perm (Fin n)}
    (ha : Rep n a (f 0)) (hb : Rep n b (f 1)) (hc : Rep n c (f 2)) (hd : Rep n d (f 3)) :
    ∀ h < 4, Rep n (#[a, b, c, d] : Array (Array ℕ))[h]! (f h) := by
  intro h hh
  interval_cases h
  · exact ha
  · exact hb
  · exact hc
  · exact hd

section Facts


theorem evalWord_mem_suzM : ∀ L : List (Fin 3 × Bool), (∀ p ∈ L, p.1.val < 2) →
    Quiver.SchreierGraph.evalWord (fun h : Fin 3 => bPerm h) L ∈ suzM
  | [], _ => by simp [Quiver.SchreierGraph.evalWord_nil, suzM.one_mem]
  | (s, b) :: L, hL => by
    have hs : bPerm s ∈ suzM := by
      have h2 : s.val < 2 := hL (s, b) (List.mem_cons_self)
      have : s = 0 ∨ s = 1 := by omega
      rcases this with rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have ih := evalWord_mem_suzM L fun p hp => hL p (List.mem_cons_of_mem _ hp)
    cases b
    · rw [Quiver.SchreierGraph.evalWord_cons_false]
      exact suzM.mul_mem (suzM.inv_mem hs) ih
    · rw [Quiver.SchreierGraph.evalWord_cons_true]
      exact suzM.mul_mem hs ih

theorem suzWord_mem {w : List ℤ} (hw : lettersOK 2 w = true) : suzWord w ∈ suzM := by
  unfold suzWord
  refine evalWord_mem_suzM _ fun p hp => ?_
  unfold toLetters at hp
  obtain ⟨l, hl, hlp⟩ := List.mem_filterMap.1 hp
  have hl' : l ≠ 0 ∧ l.natAbs ≤ 2 := by
    have := List.all_eq_true.1 hw l hl
    simpa [bne_iff_ne, ne_eq, decide_eq_true_eq] using this
  have hl3 : l ≠ 0 ∧ l.natAbs ≤ 3 := ⟨hl'.1, by omega⟩
  rw [dite_eq_left_of_eq_true (eq_true hl3)] at hlp
  have := Option.some.inj hlp
  rw [← this]
  show l.natAbs - 1 < 2
  omega

theorem lettersOK_mono {j k : ℕ} (h : j ≤ k) {w : List ℤ} (hw : lettersOK j w = true) :
    lettersOK k w = true := by
  rw [lettersOK, List.all_eq_true] at hw ⊢
  intro l hl
  have := hw l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this ⊢
  exact ⟨this.1, this.2.trans h⟩

theorem evalWord_mem_closure {M : Type*} [Group M] {j : ℕ} (ι : Fin j → M)
    (L : List (Fin j × Bool)) :
    Quiver.SchreierGraph.evalWord ι L ∈ Subgroup.closure (Set.range ι) := by
  unfold Quiver.SchreierGraph.evalWord
  have : FreeGroup.lift ι (FreeGroup.mk L) ∈ (FreeGroup.lift ι).range := ⟨_, rfl⟩
  rwa [FreeGroup.range_lift_eq_closure] at this

theorem ncard_fixed_conj_aux {n : ℕ} (x t : Equiv.Perm (Fin n)) :
    {y : Fin n | (x * t * x⁻¹) y = y}.ncard = {y : Fin n | t y = y}.ncard := by
  have h : {y : Fin n | (x * t * x⁻¹) y = y} = (fun y => x y) '' {y : Fin n | t y = y} := by
    ext y
    constructor
    · intro hy
      refine ⟨x⁻¹ y, ?_, by simp⟩
      have h1 : x (t (x⁻¹ y)) = y := hy
      have h2 : t (x⁻¹ y) = x⁻¹ y := by
        have := congrArg (fun w => x⁻¹ w) h1
        simpa using this
      exact h2
    · rintro ⟨w, hw, rfl⟩
      simp only [Set.mem_ofPred_eq] at hw ⊢
      simp [Equiv.Perm.mul_apply, hw]
  rw [h, Set.ncard_image_of_injective _ x.injective]

theorem rep_suzArr {w : List ℤ} (hw : lettersOK 3 w = true) :
    Rep 1782 (suzArr w) (suzWord w) := by
  unfold suzArr
  exact rep_suzWord hw

theorem range_fun_two {M : Type*} (a b : M) :
    Set.range (fun h : Fin 2 => if (h : ℕ) = 0 then a else b) = {a, b} := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    fin_cases h <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem suz_row_facts :
    ∃ (A B Z l : Equiv.Perm (Fin 1782)), ∃ (hA : A ∈ invE 0) (hB : B ∈ invE 0),
      A ∈ suzM ∧ B ∈ suzM ∧ l ∈ suzM ∧ A ^ 3 = 1 ∧ B ^ 3 = 1 ∧
      Z ∈ Subgroup.closure {A, B} ∧ Z * Z = 1 ∧
      l * suzInv 0 * l⁻¹ = suzInv 0 * Z ∧
      suzM ≤ Subgroup.closure {A, B, l * A * l⁻¹, l * B * l⁻¹} ∧
      {x : Fin 1782 | Z x = x}.ncard = 54 ∧ {x : Fin 1782 | suzInv 0 x = x}.ncard = 42 ∧
      Nat.card ↥(Subgroup.closure {cRho (i := 0) (by norm_num) hm0 ⟨A, hA⟩,
        cRho (i := 0) (by norm_num) hm0 ⟨B, hB⟩}) = 20160 ∧
      suzInv 0 ∈ suzM ∧ Z ≠ 1 ∧
      (∃ hZ : Z ∈ invE 0, cRho (i := 0) (by norm_num) hm0 ⟨Z, hZ⟩ ≠ 1) ∧
      (∀ x ∈ suzM, x * suzInv 0 * x⁻¹ ≠ Z) := by
  have h := Certificates.certificate26680
  simp only [suzRowCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hlet, hinv⟩, hrel⟩, hfix⟩, hgen⟩, hcls⟩, hzc⟩ := h
  simp only [suzLettersOK, Bool.and_eq_true] at hlet
  obtain ⟨⟨⟨⟨⟨hlA, hlB⟩, hlL⟩, hlZ⟩, hlG0⟩, hlG1⟩ := hlet
  simp only [suzInvOK, Bool.and_eq_true] at hinv
  obtain ⟨⟨⟨⟨hiA, hiB⟩, hiL⟩, hiAl⟩, hiBl⟩ := hinv
  simp only [suzRelOK, Bool.and_eq_true] at hrel
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpA, hpB⟩, ht0⟩, hcA⟩, hcB⟩, hlz⟩, hg0⟩, hg1⟩, hzz⟩ := hrel
  simp only [suzFixOK, Bool.and_eq_true, beq_iff_eq] at hfix
  simp only [suzZCheck, bne_iff_ne, ne_eq] at hzc
  obtain ⟨hfZ, hf0⟩ := hfix
  set A : Equiv.Perm (Fin 1782) := suzWord suzWordA with hAdef
  set B : Equiv.Perm (Fin 1782) := suzWord suzWordB with hBdef
  set l : Equiv.Perm (Fin 1782) := suzWord suzWordL with hLdef
  have hRA : Rep 1782 suzArrA A := by
    unfold suzArrA
    exact rep_suzArr (lettersOK_mono (by norm_num) hlA)
  have hRB : Rep 1782 suzArrB B := by
    unfold suzArrB
    exact rep_suzArr (lettersOK_mono (by norm_num) hlB)
  have hRL : Rep 1782 suzArrL l := by
    unfold suzArrL
    exact rep_suzArr (lettersOK_mono (by norm_num) hlL)
  have hRAi : Rep 1782 suzArrAi A⁻¹ := rep_inv_of_isInvA hRA hiA
  have hRBi : Rep 1782 suzArrBi B⁻¹ := rep_inv_of_isInvA hRB hiB
  have hRLi : Rep 1782 suzArrLi l⁻¹ := rep_inv_of_isInvA hRL hiL
  have hRLi' : Rep 1782 (invCand 1782 suzArrL) l⁻¹ := by
    unfold suzArrLi at hRLi
    exact hRLi
  have hRAl : Rep 1782 suzArrAl (l * A * l⁻¹) := by
    unfold suzArrAl suzConj
    exact rep_compA (rep_compA hRL hRA) hRLi'
  have hRBl : Rep 1782 suzArrBl (l * B * l⁻¹) := by
    unfold suzArrBl suzConj
    exact rep_compA (rep_compA hRL hRB) hRLi'
  have hRAli : Rep 1782 suzArrAli (l * A * l⁻¹)⁻¹ := rep_inv_of_isInvA hRAl hiAl
  have hRBli : Rep 1782 suzArrBli (l * B * l⁻¹)⁻¹ := rep_inv_of_isInvA hRBl hiBl
  have hR0 : Rep 1782 (tArr 0) (suzInv 0) := rep_suzInv (by norm_num)
  have hRb0 : Rep 1782 b0Arr suzB0 := rep_b0
  have hRb1 : Rep 1782 b1Arr suzB1 := rep_b1
  have ht0eq : suzInv 0 = suzB0 := (eqA_iff hR0 hRb0).1 ht0
  have hAM : A ∈ suzM := suzWord_mem hlA
  have hBM : B ∈ suzM := suzWord_mem hlB
  have hLM : l ∈ suzM := suzWord_mem hlL
  have hA3 : A ^ 3 = 1 := (eqA_iff (rep_powA hRA 3) rep_idA).1 hpA
  have hB3 : B ^ 3 = 1 := (eqA_iff (rep_powA hRB 3) rep_idA).1 hpB
  have hAc : A * suzInv 0 = suzInv 0 * A :=
    (eqA_iff (rep_compA hRA hR0) (rep_compA hR0 hRA)).1 hcA
  have hBc : B * suzInv 0 = suzInv 0 * B :=
    (eqA_iff (rep_compA hRB hR0) (rep_compA hR0 hRB)).1 hcB
  have hAE : A ∈ invE 0 := by
    rw [invE_eq_centM (by norm_num : 0 < 4)]
    exact ⟨mem_centralizer_singleton_iff.2 hAc, hAM⟩
  have hBE : B ∈ invE 0 := by
    rw [invE_eq_centM (by norm_num : 0 < 4)]
    exact ⟨mem_centralizer_singleton_iff.2 hBc, hBM⟩
  let gs2 : ℕ → Equiv.Perm (Fin 1782) := fun h => if h = 0 then A else B
  have hS2 : ∀ h < 2, Rep 1782 suzArrAB[h]! (gs2 h) := rep_two_getElem! (f := gs2) hRA hRB
  have hS2i : ∀ h < 2, Rep 1782 suzArrABi[h]! (gs2 h)⁻¹ :=
    rep_two_getElem! (f := fun h => (gs2 h)⁻¹) hRAi hRBi
  let Z : Equiv.Perm (Fin 1782) :=
    Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gs2 h) (toLetters 2 suzWordZ)
  have hRZ : Rep 1782 suzArrZ Z := by
    unfold suzArrZ
    exact rep_wordA hS2 hS2i suzWordZ hlZ
  have hZmem : Z ∈ Subgroup.closure {A, B} := by
    have := evalWord_mem_closure (fun h : Fin 2 => gs2 h) (toLetters 2 suzWordZ)
    have e : Set.range (fun h : Fin 2 => gs2 h) = {A, B} := range_fun_two A B
    rwa [e] at this
  have hZZ : Z * Z = 1 := (eqA_iff (rep_compA hRZ hRZ) rep_idA).1 hzz
  have hRc0 : Rep 1782 (suzConj suzArrL (tArr 0)) (l * suzInv 0 * l⁻¹) := by
    unfold suzConj
    exact rep_compA (rep_compA hRL hR0) hRLi'
  have hl0 : l * suzInv 0 * l⁻¹ = suzInv 0 * Z :=
    (eqA_iff hRc0 (rep_compA hR0 hRZ)).1 hlz
  let gs4 : ℕ → Equiv.Perm (Fin 1782) := fun h =>
    if h = 0 then A else if h = 1 then B else if h = 2 then l * A * l⁻¹ else l * B * l⁻¹
  have hS4 : ∀ h < 4, Rep 1782 suzArr4[h]! (gs4 h) :=
    rep_four_getElem! (f := gs4) hRA hRB hRAl hRBl
  have hS4i : ∀ h < 4, Rep 1782 suzArr4i[h]! (gs4 h)⁻¹ :=
    rep_four_getElem! (f := fun h => (gs4 h)⁻¹) hRAi hRBi hRAli hRBli
  have hRG0 := rep_wordA hS4 hS4i suzWordG0 hlG0
  have hRG1 := rep_wordA hS4 hS4i suzWordG1 hlG1
  have hG0 := (eqA_iff hRG0 hRb0).1 hg0
  have hG1 := (eqA_iff hRG1 hRb1).1 hg1
  have hrange4 : Set.range (fun h : Fin 4 => gs4 h) = {A, B, l * A * l⁻¹, l * B * l⁻¹} := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      fin_cases h <;> simp [gs4]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by simp [gs4]⟩
      · exact ⟨1, by simp [gs4]⟩
      · exact ⟨2, by simp [gs4]⟩
      · exact ⟨3, by simp [gs4]⟩
  have hM : suzM ≤ Subgroup.closure {A, B, l * A * l⁻¹, l * B * l⁻¹} := by
    rw [suzM, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [← hG0]
      have := evalWord_mem_closure (fun h : Fin 4 => gs4 h) (toLetters 4 suzWordG0)
      rwa [hrange4] at this
    · rw [← hG1]
      have := evalWord_mem_closure (fun h : Fin 4 => gs4 h) (toLetters 4 suzWordG1)
      rwa [hrange4] at this
  have hfixZ : {x : Fin 1782 | Z x = x}.ncard = 54 := by rw [ncard_fixed_eq hRZ]; exact hfZ
  have hfix0 : {x : Fin 1782 | suzInv 0 x = x}.ncard = 42 := by
    rw [ncard_fixed_eq hR0]; exact hf0
  refine ⟨A, B, Z, l, hAE, hBE, hAM, hBM, hLM, hA3, hB3, hZmem, hZZ, hl0, hM, hfixZ, hfix0, ?_⟩
  have hnc : ∀ x ∈ suzM, x * suzInv 0 * x⁻¹ ≠ Z := by
    intro x _ hx
    have h1 : {y : Fin 1782 | Z y = y}.ncard = {y : Fin 1782 | suzInv 0 y = y}.ncard := by
      rw [← hx]
      exact ncard_fixed_conj_aux x (suzInv 0)
    rw [hfixZ, hfix0] at h1
    omega
  have hZE : Z ∈ invE 0 := by
    have hcle : Subgroup.closure {A, B} ≤ invE 0 := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hAE
      · exact hBE
    exact hcle hZmem
  have hρA : TabRep suzTabA (cRho (i := 0) (by norm_num) hm0 ⟨A, hAE⟩) := by
    unfold suzTabA
    exact (fixList_points hm0).tabRep_restrHom (invE 0) (invE_preserves (by norm_num)) ⟨A, hAE⟩ hRA
  have hρB : TabRep suzTabB (cRho (i := 0) (by norm_num) hm0 ⟨B, hBE⟩) := by
    unfold suzTabB
    exact (fixList_points hm0).tabRep_restrHom (invE 0) (invE_preserves (by norm_num)) ⟨B, hBE⟩ hRB
  simp only [suzGenCheck, Bool.and_eq_true, beq_iff_eq] at hgen
  have hE : Enumerates (Subgroup.closure {cRho (i := 0) (by norm_num) hm0 ⟨A, hAE⟩,
      cRho (i := 0) (by norm_num) hm0 ⟨B, hBE⟩}) (enumOf 42 suzTabs 20160).tabs.toList := by
    refine enumerates_closure ?_ ?_ hgen.1
    · rintro a (rfl | rfl)
      · exact ⟨0, by simp [suzTabs], hρA⟩
      · exact ⟨1, by simp [suzTabs], hρB⟩
    · intro j hj
      have hj2 : j < 2 := by simpa [suzTabs] using hj
      interval_cases j
      · exact ⟨_, Or.inl rfl, hρA⟩
      · exact ⟨_, Or.inr rfl, hρB⟩
  refine ⟨?_, ?_, ?_, ?_, hnc⟩
  · rw [hE.card, Array.length_toList, hgen.2]
  · rw [ht0eq]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · intro h1
    have : {y : Fin 1782 | Z y = y}.ncard = 1782 := by
      rw [h1]
      simp [Set.ncard_univ]
    omega
  · refine ⟨hZE, ?_⟩
    have hρZ : TabRep suzTabZ (cRho (i := 0) (by norm_num) hm0 ⟨Z, hZE⟩) := by
      unfold suzTabZ
      exact (fixList_points hm0).tabRep_restrHom (invE 0) (invE_preserves (by norm_num))
        ⟨Z, hZE⟩ hRZ
    intro h1
    rw [h1] at hρZ
    exact hzc (hρZ.tab_eq TabRep.idTab)

theorem suz_classCheck : suzClassCheck = true := by
  have h := Certificates.certificate26680
  simp only [suzRowCheck, Bool.and_eq_true] at h
  exact h.1.2

end Facts

end CFSG.EvenSporadicStandard.Solomon78
