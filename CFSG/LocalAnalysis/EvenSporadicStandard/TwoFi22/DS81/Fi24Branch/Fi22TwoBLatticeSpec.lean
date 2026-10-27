module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeCode
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeSpin
public import Certificates.Certificate450108

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open scoped commutatorElement
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates (SchreierLetter)
open CFSG.Certificates.ExtraspecialNF
open CFSG.ComponentClassification.CatFactsSmall.PSp43
  (x45 y45 f45 QA45 QP45 QP45_closure QA45_closure QP45_ok QA45_ok QP45_valid QA45_valid)

@[expose] def Ybar : Subgroup (Equiv.Perm (Fin 3510)) := Subgroup.closure {cGen 1, cGen 2}

@[expose] def gY (h : ℕ) : Equiv.Perm (Fin 3510) := if h = 0 then cGen 1 else cGen 2

theorem gY_zero : gY 0 = cGen 1 := if_pos rfl

theorem gY_one : gY 1 = cGen 2 := if_neg (by decide)

theorem cGen_one_mem_Ybar : cGen 1 ∈ Ybar := Subgroup.subset_closure (Set.mem_insert _ _)

theorem cGen_two_mem_Ybar : cGen 2 ∈ Ybar :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem evalWord_gY_mem (w : List (SchreierLetter 2)) :
    Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gY h) w ∈ Ybar := by
  refine Subgroup.closure_mono ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ w)
  rintro _ ⟨⟨h, hh⟩, rfl⟩
  interval_cases h
  · show gY 0 ∈ ({cGen 1, cGen 2} : Set (Equiv.Perm (Fin 3510)))
    rw [gY_zero]
    exact Set.mem_insert _ _
  · show gY 1 ∈ ({cGen 1, cGen 2} : Set (Equiv.Perm (Fin 3510)))
    rw [gY_one]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

theorem Ybar_le_Cbar :
    Ybar ≤ Cbar := by
  rw [Ybar, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact cGen_mem_Cbar 1
  · exact cGen_mem_Cbar 2

theorem checkPerf_spec (h : checkPerf () = true) :
    cGen 1 ∈ ⁅Ybar, Ybar⁆ ∧ cGen 2 ∈ ⁅Ybar, Ybar⁆ := by
  unfold checkPerf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hAl⟩, hBl⟩, hS⟩, hab⟩, h1⟩, h2⟩ := h
  set S : Array (Array ℕ) := Array.ofFn (n := 2) fun j => genArr (j.val + 1) with hSdef
  set Si : Array (Array ℕ) := Array.ofFn (n := 2) fun j => invCand 3510 S[j.val]! with hSidef
  set a : Array (Array ℕ) :=
    Array.ofFn (n := 4) fun s => wordA 3510 S Si (commA.getD s.val []) with hadef
  set b : Array (Array ℕ) :=
    Array.ofFn (n := 4) fun s => wordA 3510 S Si (commB.getD s.val []) with hbdef
  set ai : Array (Array ℕ) := Array.ofFn (n := 4) fun s => invCand 3510 a[s.val]! with haidef
  set bi : Array (Array ℕ) := Array.ofFn (n := 4) fun s => invCand 3510 b[s.val]! with hbidef
  set u : Array (Array ℕ) := Array.ofFn (n := 4) fun s =>
    compA 3510 (compA 3510 a[s.val]! b[s.val]!) (compA 3510 ai[s.val]! bi[s.val]!) with hudef
  have hSrep : ∀ h < 2, Rep 3510 S[h]! (gY h) := by
    intro h hh
    rw [hSdef, getElem!_ofFn_arr _ hh]
    interval_cases h
    · rw [gY_zero]
      exact rep_genArr 1
    · rw [gY_one]
      exact rep_genArr 2
  have hSirep : ∀ h < 2, Rep 3510 Si[h]! (gY h)⁻¹ := fun h hh =>
    rep_inv_of_isInvA (hSrep h hh) (allLt_spec hS hh)
  have hword : ∀ w : List ℤ, lettersOK 2 w = true →
      Rep 3510 (wordA 3510 S Si w)
        (Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gY h) (toLetters 2 w)) := fun w hw =>
    rep_wordA (gs := gY) (j := 2) hSrep hSirep w hw
  have hAget : ∀ s : Fin 4, lettersOK 2 (commA.getD s []) = true := by
    intro s
    simp only [List.all_eq_true] at hAl
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hAl _ (List.getElem_mem _)
  have hBget : ∀ s : Fin 4, lettersOK 2 (commB.getD s []) = true := by
    intro s
    simp only [List.all_eq_true] at hBl
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hBl _ (List.getElem_mem _)
  set aE : Fin 4 → Equiv.Perm (Fin 3510) := fun s =>
    Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gY h) (toLetters 2 (commA.getD s [])) with haE
  set bE : Fin 4 → Equiv.Perm (Fin 3510) := fun s =>
    Quiver.SchreierGraph.evalWord (fun h : Fin 2 => gY h) (toLetters 2 (commB.getD s [])) with hbE
  have harep : ∀ s : Fin 4, Rep 3510 a[(s : ℕ)]! (aE s) := by
    intro s
    rw [hadef, getElem!_ofFn_arr _ s.2]
    exact hword _ (hAget s)
  have hbrep : ∀ s : Fin 4, Rep 3510 b[(s : ℕ)]! (bE s) := by
    intro s
    rw [hbdef, getElem!_ofFn_arr _ s.2]
    exact hword _ (hBget s)
  have hairep : ∀ s : Fin 4, Rep 3510 ai[(s : ℕ)]! (aE s)⁻¹ := by
    intro s
    refine rep_inv_of_isInvA (harep s) ?_
    have := allLt_spec hab s.2
    simp only [Bool.and_eq_true] at this
    exact this.1
  have hbirep : ∀ s : Fin 4, Rep 3510 bi[(s : ℕ)]! (bE s)⁻¹ := by
    intro s
    refine rep_inv_of_isInvA (hbrep s) ?_
    have := allLt_spec hab s.2
    simp only [Bool.and_eq_true] at this
    exact this.2
  have hurep : ∀ s : Fin 4, Rep 3510 u[(s : ℕ)]! ⁅aE s, bE s⁆ := by
    intro s
    have e : ⁅aE s, bE s⁆ = (aE s * bE s) * ((aE s)⁻¹ * (bE s)⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    rw [hudef, getElem!_ofFn_arr _ s.2, e]
    exact rep_compA (rep_compA (harep s) (hbrep s)) (rep_compA (hairep s) (hbirep s))
  have hu_mem : ∀ s : Fin 4, ⁅aE s, bE s⁆ ∈ ⁅Ybar, Ybar⁆ := fun s =>
    Subgroup.commutator_mem_commutator (evalWord_gY_mem _) (evalWord_gY_mem _)
  have e1 : ⁅aE 0, bE 0⁆ * ⁅aE 1, bE 1⁆ = cGen 1 := by
    rw [← gY_zero]
    exact eq_of_eqA (rep_compA (hurep 0) (hurep 1)) (hSrep 0 (by norm_num)) h1
  have e2 : ⁅aE 2, bE 2⁆ * ⁅aE 3, bE 3⁆ = cGen 2 := by
    rw [← gY_one]
    exact eq_of_eqA (rep_compA (hurep 2) (hurep 3)) (hSrep 1 (by norm_num)) h2
  exact ⟨e1 ▸ mul_mem (hu_mem 0) (hu_mem 1), e2 ▸ mul_mem (hu_mem 2) (hu_mem 3)⟩

theorem checkRho_spec
    (hblocks : checkBlocks () = true) (h : checkRho () = true) :
    blockTau 1 ∈ Subgroup.closure {x45, y45} ∧ blockTau 2 ∈ Subgroup.closure {x45, y45} ∧
      x45 ∈ Subgroup.closure {blockTau 1, blockTau 2} ∧
      y45 ∈ Subgroup.closure {blockTau 1, blockTau 2} := by
  have hTrep0 := (checkBlocks_spec hblocks).2.2.2.2.2
  unfold checkRho at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hAl⟩, hBl⟩, hXi⟩, hTi⟩, h1⟩, h2⟩ := h
  set X : Array (Array ℕ) := Array.ofFn (n := 2) fun j => xyfArr[j.val]! with hXdef
  set Xi : Array (Array ℕ) := Array.ofFn (n := 2) fun j => invCand 45 X[j.val]! with hXidef
  set T0 : Array (Array ℕ) := tauArrs () with hT0
  set T : Array (Array ℕ) := Array.ofFn (n := 2) fun j => T0[j.val + 1]! with hTdef
  set Ti : Array (Array ℕ) := Array.ofFn (n := 2) fun j => invCand 45 T[j.val]! with hTidef
  have hXrep : ∀ h < 2, Rep 45 X[h]! (xyfN h) := by
    intro h hh
    rw [hXdef, getElem!_ofFn_arr _ hh]
    exact rep_xyfArr h (by omega)
  have hXirep : ∀ h < 2, Rep 45 Xi[h]! (xyfN h)⁻¹ := fun h hh =>
    rep_inv_of_isInvA (hXrep h hh) (allLt_spec hXi hh)
  have hTrep : ∀ h < 2, Rep 45 T[h]! (blockTau (h + 1)) := by
    intro h hh
    rw [hTdef, getElem!_ofFn_arr _ hh]
    exact hTrep0 ⟨h + 1, by omega⟩
  have hTirep : ∀ h < 2, Rep 45 Ti[h]! (blockTau (h + 1))⁻¹ := fun h hh =>
    rep_inv_of_isInvA (hTrep h hh) (allLt_spec hTi hh)
  have hletA : ∀ j : Fin 2, lettersOK 2 (rhoXY.getD j []) = true := by
    intro j
    simp only [List.all_eq_true] at hAl
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hAl _ (List.getElem_mem _)
  have hletB : ∀ j : Fin 2, lettersOK 2 (rhoTau.getD j []) = true := by
    intro j
    simp only [List.all_eq_true] at hBl
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hBl _ (List.getElem_mem _)
  have hXY : ∀ j : Fin 2, Quiver.SchreierGraph.evalWord (fun h : Fin 2 => xyfN h)
      (toLetters 2 (rhoXY.getD j [])) = blockTau (j + 1) := by
    intro j
    have hrep := rep_wordA (gs := xyfN) (j := 2) hXrep hXirep _ (hletA j)
    exact eq_of_eqA hrep (hTrep j j.2) (allLt_spec h1 j.2)
  have hTau : ∀ j : Fin 2, Quiver.SchreierGraph.evalWord (fun h : Fin 2 => blockTau (h + 1))
      (toLetters 2 (rhoTau.getD j [])) = xyfN j := by
    intro j
    have hrep := rep_wordA (gs := fun h => blockTau (h + 1)) (j := 2) hTrep hTirep _ (hletB j)
    exact eq_of_eqA hrep (hXrep j j.2) (allLt_spec h2 j.2)
  have hX2 : Subgroup.closure (Set.range fun h : Fin 2 => xyfN h) ≤
      Subgroup.closure {x45, y45} := by
    refine Subgroup.closure_mono ?_
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    interval_cases h
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hT2 : Subgroup.closure (Set.range fun h : Fin 2 => blockTau (h + 1)) ≤
      Subgroup.closure {blockTau 1, blockTau 2} := by
    refine Subgroup.closure_mono ?_
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    interval_cases h
    · exact Or.inl rfl
    · exact Or.inr rfl
  have m1 : ∀ j : Fin 2, blockTau (j + 1) ∈ Subgroup.closure {x45, y45} := fun j => by
    rw [← hXY j]
    exact hX2 (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  have m2 : ∀ j : Fin 2, xyfN j ∈ Subgroup.closure {blockTau 1, blockTau 2} := fun j => by
    rw [← hTau j]
    exact hT2 (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  exact ⟨m1 0, m1 1, m2 0, m2 1⟩

theorem checkLattice_parts (h : checkLattice () = true) :
    checkPerf () = true ∧ checkRho () = true ∧
      spinCheck (applyCols (actCols 1)) (applyCols (actCols 2)) eMask mMask = true := by
  simp only [checkLattice, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem commutator_Ybar :
    ⁅Ybar, Ybar⁆ = Ybar := by
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  · obtain ⟨h1, h2⟩ := checkPerf_spec (checkLattice_parts Certificates.certificate450108).1
    rw [Ybar, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact h1
    · exact h2

theorem map_subgroupOf_closure_pair {G H : Type*} [Group G] [Group H] {C : Subgroup G}
    (ρ : ↥C →* H) {a b : G} (ha : a ∈ C) (hb : b ∈ C) :
    ((Subgroup.closure {a, b}).subgroupOf C).map ρ =
      Subgroup.closure {ρ ⟨a, ha⟩, ρ ⟨b, hb⟩} := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    have hle : Subgroup.closure {a, b} ≤
        ((Subgroup.closure {ρ ⟨a, ha⟩, ρ ⟨b, hb⟩}).comap ρ).map C.subtype := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact ⟨⟨_, ha⟩, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨⟨_, hb⟩,
          Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)), rfl⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_subgroupOf.1 hx)
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨a, ha⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (Set.mem_insert _ _)), rfl⟩
    · exact ⟨⟨b, hb⟩, Subgroup.mem_subgroupOf.2
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))), rfl⟩

theorem closure_pair_eq_of_mem {G : Type*} [Group G] {a b c d : G}
    (hc : c ∈ Subgroup.closure {a, b}) (hd : d ∈ Subgroup.closure {a, b})
    (ha : a ∈ Subgroup.closure {c, d}) (hb : b ∈ Subgroup.closure {c, d}) :
    Subgroup.closure {a, b} = Subgroup.closure {c, d} := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hc
    · exact hd

private theorem QP45_le_QA45_aux : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  rw [QP45_closure, QA45_closure]
  refine Subgroup.closure_mono ?_
  rintro g (rfl | rfl)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem relIndex_Ybar_sup_Qbar :
    (Ybar ⊔ Qbar).relIndex Cbar = 2 := by
  obtain ⟨ρ, hrange, hker, hρ⟩ := exists_rho
  obtain ⟨t1P, t2P, xT, yT⟩ := checkRho_spec Certificates.certificate450107
    (checkLattice_parts Certificates.certificate450108).2.1
  have h1 : cGen 1 ∈ Cbar := cGen_mem_Cbar 1
  have h2 : cGen 2 ∈ Cbar := cGen_mem_Cbar 2
  have hτ1 : ρ ⟨cGen 1, h1⟩ = blockTau 1 := hρ 1 h1
  have hτ2 : ρ ⟨cGen 2, h2⟩ = blockTau 2 := hρ 2 h2
  have hmap : (Ybar.subgroupOf Cbar).map ρ = QP45.originalSubgroup := by
    have e := map_subgroupOf_closure_pair ρ h1 h2
    rw [hτ1, hτ2] at e
    rw [QP45_closure]
    exact e.trans (closure_pair_eq_of_mem t1P t2P xT yT).symm
  unfold Subgroup.relIndex
  rw [Subgroup.subgroupOf_sup Ybar_le_Cbar Qbar_le_Cbar, ← hker, ← Subgroup.comap_map_eq, hmap,
    Subgroup.index_comap, hrange]
  have h := Subgroup.relIndex_mul_card (H := QP45.originalSubgroup) (K := QA45.originalSubgroup)
  rw [inf_eq_left.2 QP45_le_QA45_aux, CFSG.GH74.KGroups.card_group QP45 QP45_ok,
    CFSG.GH74.KGroups.card_group QA45 QA45_ok, QP45_valid.2, QA45_valid.2] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 25920) (h.trans (by norm_num))

theorem codeVec_applyCols_nat (k : Fin 10) (n : ℕ) (hn : (k : ℕ) = n) (c : ℕ) :
    codeVec (applyCols (actCols n) c) = (actMat k).mulVec (codeVec c) := by
  subst hn
  exact codeVec_applyCols k c

theorem finrank_invariant
    (hspin : spinCheck (applyCols (actCols 1)) (applyCols (actCols 2)) eMask mMask = true)
    (W : Submodule (ZMod 2) (Fin 10 → ZMod 2)) (h1 : ∀ v ∈ W, (actMat 1).mulVec v ∈ W)
    (h2 : ∀ v ∈ W, (actMat 2).mulVec v ∈ W) :
    Module.finrank (ZMod 2) W = 0 ∨ Module.finrank (ZMod 2) W = 1 ∨
      Module.finrank (ZMod 2) W = 9 ∨ Module.finrank (ZMod 2) W = 10 := by
  obtain ⟨he0, he1, hem, hall⟩ := spinCheck_spec hspin
  set P : ℕ → Prop := fun c => codeVec c ∈ W with hP
  have h0 : P 0 := by
    simp only [hP, codeVec_zero]
    exact W.zero_mem
  have hx : ∀ a b, P a → P b → P (a ^^^ b) := by
    intro a b ha hb
    simp only [hP, codeVec_xor]
    exact W.add_mem ha hb
  have hf : ∀ c, P c → P (applyCols (actCols 1) c) := by
    intro c hc
    show codeVec _ ∈ W
    rw [codeVec_applyCols_nat 1 1 rfl]
    exact h1 _ hc
  have hg : ∀ c, P c → P (applyCols (actCols 2) c) := by
    intro c hc
    show codeVec _ ∈ W
    rw [codeVec_applyCols_nat 2 2 rfl]
    exact h2 _ hc
  have claim : ∀ v ∈ W, v ≠ 0 → v ≠ codeVec eMask → ∀ w : Fin 10 → ZMod 2,
      (dotForm mMask v = 1 ∨ dotForm mMask w = 0) → w ∈ W := by
    intro v hv hv0 hve w hw
    obtain ⟨x, hx1024, rfl⟩ := exists_codeVec v
    obtain ⟨y, hy1024, rfl⟩ := exists_codeVec w
    have hx0 : x ≠ 0 := fun h => hv0 (by rw [h, codeVec_zero])
    have hxe : x ≠ eMask := fun h => hve (by rw [h])
    refine spin_sound (P := P) h0 hx hf hg hv (hall x hx1024 hx0 hxe y hy1024 ?_)
    rcases hw with hw | hw
    · left
      rw [dotForm_codeVec] at hw
      by_contra hcon
      simp only [Bool.not_eq_true] at hcon
      simp [hcon] at hw
    · right
      rw [dotForm_codeVec] at hw
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      simp [hcon] at hw
  have heW : codeVec eMask ≠ 0 := by
    intro h
    have := codeVec_injOn (Set.mem_Iio.2 he1) (Set.mem_Iio.2 (by norm_num : 0 < 1024))
      (h.trans codeVec_zero.symm)
    omega
  have hℓe : dotForm mMask (codeVec eMask) = 0 := by
    rw [dotForm_codeVec, hem]
    rfl
  have hm2 : dotM mMask 2 = true := by decide
  have hℓne : ∃ v, dotForm mMask v = 1 := ⟨codeVec 2, by rw [dotForm_codeVec, hm2]; rfl⟩
  by_cases hbig : ∃ v ∈ W, v ≠ 0 ∧ v ≠ codeVec eMask
  · obtain ⟨v, hvW, hv0, hve⟩ := hbig
    by_cases hℓW : ∃ w ∈ W, dotForm mMask w = 1
    · obtain ⟨w, hwW, hw1⟩ := hℓW
      have hw0 : w ≠ 0 := fun h => by
        rw [h, map_zero] at hw1
        exact zero_ne_one hw1
      have hwe : w ≠ codeVec eMask := fun h => by
        rw [h, hℓe] at hw1
        exact zero_ne_one hw1
      have hTop : W = ⊤ := eq_top_iff.2 fun u _ => claim w hwW hw0 hwe u (Or.inl hw1)
      right
      right
      right
      rw [hTop, finrank_top, Module.finrank_fin_fun]
    · push Not at hℓW
      have hker : W = LinearMap.ker (dotForm mMask) := by
        apply le_antisymm
        · intro w hw
          rw [LinearMap.mem_ker]
          rcases zmod_two_cases (dotForm mMask w) with h | h
          · exact h
          · exact absurd h (hℓW w hw)
        · intro w hw
          rw [LinearMap.mem_ker] at hw
          exact claim v hvW hv0 hve w (Or.inr hw)
      right
      right
      left
      have hrank := LinearMap.finrank_range_add_finrank_ker (dotForm mMask)
      have hrange : LinearMap.range (dotForm mMask) = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro c
        rcases zmod_two_cases c with rfl | rfl
        · exact ⟨0, map_zero _⟩
        · exact hℓne
      rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrank
      rw [hker]
      omega
  · push Not at hbig
    by_cases heW' : codeVec eMask ∈ W
    · have hspan : W = Submodule.span (ZMod 2) {codeVec eMask} := by
        apply le_antisymm
        · intro v hv
          by_cases hv0 : v = 0
          · rw [hv0]
            exact zero_mem _
          · rw [hbig v hv hv0]
            exact Submodule.mem_span_singleton_self _
        · rw [Submodule.span_le, Set.singleton_subset_iff]
          exact heW'
      right
      left
      rw [hspan]
      exact finrank_span_singleton heW
    · have hbot : W = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        by_cases hv0 : v = 0
        · rw [hv0]
          exact zero_mem _
        · rw [hbig v hv hv0] at hv
          exact absurd hv heW'
      left
      rw [hbot, finrank_bot]

@[expose] def vecSub (hrel : Rel t1 qGen cMat) (U : Subgroup (Equiv.Perm (Fin 3510))) :
    Submodule (ZMod 2) (Fin 10 → ZMod 2) where
  carrier := {v | ∃ s, nf t1 qGen s v ∈ U}
  add_mem' := by
    rintro v w ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t + collect cMat v w, by rw [← nf_mul_nf hrel]; exact U.mul_mem hs ht⟩
  zero_mem' := ⟨0, by rw [nf_zero_zero]; exact U.one_mem⟩
  smul_mem' := by
    rintro a v ⟨s, hs⟩
    rcases zmod_two_cases a with rfl | rfl
    · exact ⟨0, by rw [zero_smul, nf_zero_zero]; exact U.one_mem⟩
    · exact ⟨s, by rwa [one_smul]⟩

theorem card_eq_two_mul_vecSub
    {U : Subgroup (Equiv.Perm (Fin 3510))}
    (ht : Subgroup.zpowers t1 ≤ U) (hUQ : U ≤ Qbar) :
    Nat.card U = 2 * Nat.card (vecSub rel_qGen U) := by
  have hrel := rel_qGen
  have ht1 : t1 ∈ U := ht (Subgroup.mem_zpowers t1)
  have hnfU : ∀ (s : ZMod 2) (v : vecSub rel_qGen U), nf t1 qGen s v ∈ U := by
    rintro s ⟨v, t, hv⟩
    have e : t + (s - t) = s := by ring
    have h : nf t1 qGen s v = nf t1 qGen t v * t1 ^ (s - t).val := by
      rw [nf_mul_zpow hrel, e]
    rw [h]
    exact U.mul_mem hv (U.pow_mem ht1 _)
  let f : ZMod 2 × vecSub rel_qGen U → U := fun p => ⟨nf t1 qGen p.1 p.2, hnfU p.1 p.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨s, v, hv⟩ ⟨s', v', hv'⟩ h
      have h' : nf t1 qGen s v = nf t1 qGen s' v' := congrArg Subtype.val h
      have := injective_nf_qGen (a₁ := (s, v)) (a₂ := (s', v')) h'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨s, v, rfl⟩ := exists_nf_of_mem_Qbar (hUQ hx)
      exact ⟨(s, ⟨v, s, hx⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, Nat.card_zmod]

theorem mulVec_mem_vecSub
    {U : Subgroup (Equiv.Perm (Fin 3510))} (k : Fin 10)
    (hk : ∀ u ∈ U, cGen k * u * (cGen k)⁻¹ ∈ U) {v : Fin 10 → ZMod 2}
    (hv : v ∈ vecSub rel_qGen U) : (actMat k).mulVec v ∈ vecSub rel_qGen U := by
  obtain ⟨s, hs⟩ := hv
  obtain ⟨s', hs'⟩ := cGen_conj_nf k s v
  exact ⟨s', by rw [← hs']; exact hk _ hs⟩

theorem lattice_Ybar
    {U : Subgroup (Equiv.Perm (Fin 3510))} (ht : Subgroup.zpowers t1 ≤ U) (hUQ : U ≤ Qbar)
    (hinv : InvUnder Ybar U) :
    Nat.card U = 2 ∨ Nat.card U = 2 ^ 2 ∨ Nat.card U = 2 ^ 10 ∨ Nat.card U = 2 ^ 11 := by
  have hW := finrank_invariant (checkLattice_parts Certificates.certificate450108).2.2
    (vecSub rel_qGen U) (fun v hv => mulVec_mem_vecSub 1 (hinv _ cGen_one_mem_Ybar) hv)
    (fun v hv => mulVec_mem_vecSub 2 (hinv _ cGen_two_mem_Ybar) hv)
  have hcard := card_eq_two_mul_vecSub ht hUQ
  have hpow : Nat.card (vecSub rel_qGen U) = 2 ^ Module.finrank (ZMod 2) (vecSub rel_qGen U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard, hpow]
  rcases hW with h | h | h | h <;> rw [h]
  · left
    norm_num
  · right
    left
    norm_num
  · right
    right
    left
    norm_num
  · right
    right
    right
    norm_num

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
