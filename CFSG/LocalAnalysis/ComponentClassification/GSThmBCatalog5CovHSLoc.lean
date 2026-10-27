module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovHSCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovBase

public section

namespace CFSG.ComponentClassification.GSThmB.CovHS

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.Schreier
open CFSG.LocalAnalysis.ComponentInitial

noncomputable abbrev nfix (g : Equiv.Perm (Fin 3850)) : ℕ := Nat.card {i : Fin 3850 // g i = i}

theorem nfix_conj (c g : Equiv.Perm (Fin 3850)) : nfix (c * g * c⁻¹) = nfix g :=
  Nat.card_congr (Equiv.subtypeEquiv c⁻¹ fun p => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq])

theorem nfix_of_tabRep {t : Tab} {g : Equiv.Perm (Fin 3850)} (ht : TabRep t g) :
    nfix g = J2Cover.fixedCount 3850 t :=
  J2Cover.card_fixed_eq_fixedCount ht.2

@[expose] noncomputable def yPerm : Equiv.Perm (Fin 3850) := (yWord.map hsC2Perm).prod

theorem klein_parts :
    nfix hsT1 = 170 ∧ nfix hsT2 = 30 ∧ yPerm * yPerm = 1 ∧ yPerm ≠ 1 ∧ nfix yPerm = 30 ∧
      nfix (hsT2 * yPerm) = 30 := by
  have h := covHS_klein_check
  simp only [kleinCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp1, hs1⟩, hp2⟩, hs2⟩, hw⟩, hf1⟩, hf2⟩, hyy⟩, hy1⟩, hfy⟩, hfty⟩ := h
  have ht1 : TabRep t1Tab hsT1 := tabRep_natArr hp1 hs1
  have ht2 : TabRep t2Tab hsT2 := tabRep_natArr hp2 hs2
  have hy : TabRep yTab yPerm := tabRep_wordTabS tabRep_hsC2Tabs yWord fun j hj => by
    have := List.all_eq_true.1 hw j hj
    simpa [hsC2Tabs] using this
  have hyy' := hy.comp hy
  rw [hyy] at hyy'
  refine ⟨by rw [nfix_of_tabRep ht1, hf1], by rw [nfix_of_tabRep ht2, hf2],
    (TabRep.idTab.perm_eq hyy').symm, fun h1 => ?_, by rw [nfix_of_tabRep hy, hfy],
    by rw [nfix_of_tabRep (ht2.comp hy), hfty]⟩
  rw [h1] at hy
  have := hy.tab_eq TabRep.idTab
  rw [this] at hy1
  exact absurd hy1 (by simp)

theorem yPerm_mem :
    yPerm ∈ hsC2 := by
  rw [← hsC2_eq]
  refine (genGroup 3850 hsC2Tabs hsC2Perm).list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  refine subset_closure ⟨i, ?_, rfl⟩
  simp only [yWord, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [hsC2Tabs]

theorem conj_t2_of_nfix
    {w : Equiv.Perm (Fin 3850)} (hw : w ∈ hsP) (hw2 : orderOf w = 2) (hf : nfix w = 30) :
    ∃ g ∈ hsP, w = g * hsT2 * g⁻¹ := by
  obtain ⟨r, hr, g, hg, rfl⟩ := hs_reps.2.2.2.2 w hw hw2
  rcases hr with rfl | rfl
  · exfalso
    rw [nfix_conj, klein_parts.1] at hf
    exact absurd hf (by norm_num)
  · exact ⟨g, hg, rfl⟩

noncomputable abbrev hsT4 : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl 34)

noncomputable abbrev hsC4 : Subgroup (Equiv.Perm (Fin 3850)) := hsP ⊓ centralizer ({hsT4} : Set _)

@[expose] noncomputable def c4Perm (k : ℕ) : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl (k + 35))

@[expose] noncomputable def qPerm (j : ℕ) : Equiv.Perm (Fin 3850) :=
  ((qWords.getD j []).map c4Perm).prod

theorem outer_parts :
    (∀ k < 4, permOK 3850 (hsCentTbl (k + 35)) = true ∧
      (natArr (hsCentTbl (k + 35))).size = 3850) ∧
    (∀ j < 4, ∀ i ∈ qWords.getD j [], i < 4) ∧
    enumOK 3850 qGens qEnum = true ∧ qEnum.tabs.size = 16 ∧
    normalOK 3850 qEnum.tabs c4Tabs c4Invs qGens = true ∧
    enumOK 3850 c4Tabs c4Enum = true ∧ c4Enum.tabs.size = 1920 ∧
    (c4Enum.tabs.toList.filter (commAll 3850 qGens)).length = 16 := by
  have h := covHS_outer_check
  simp only [outerCheck, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hw⟩, hq⟩, hqs⟩, hn⟩, hc⟩, hcs⟩, hcc⟩ := h
  exact ⟨fun k hk => hp k hk, by decide, hq, hqs, hn, hc, hcs, hcc⟩

theorem tabRep_c4Tabs :
    ∀ k < c4Tabs.size, TabRep c4Tabs[k]! (c4Perm k) := by
  intro k hk
  have hk4 : k < 4 := by simpa [c4Tabs] using hk
  rw [c4Tabs, getElem!_pos _ k (by simpa using hk4), Array.getElem_ofFn]
  exact tabRep_natArr (outer_parts.1 k hk4).1 (outer_parts.1 k hk4).2

theorem tabRep_qGens :
    ∀ j < qGens.size, TabRep qGens[j]! (qPerm j) := by
  intro j hj
  have hj4 : j < 4 := by simpa [qGens] using hj
  rw [qGens, getElem!_pos _ j (by simpa using hj4), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_c4Tabs _ fun i hi => by
    have := outer_parts.2.1 j hj4 i hi
    simpa [c4Tabs] using this

theorem c4_enumerates :
    Enumerates (genGroup 3850 c4Tabs c4Perm) c4Enum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_c4Tabs) (genGroup_hgens tabRep_c4Tabs)
    outer_parts.2.2.2.2.2.1

theorem q_enumerates :
    Enumerates (genGroup 3850 qGens qPerm) qEnum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_qGens) (genGroup_hgens tabRep_qGens) outer_parts.2.2.1

theorem qPerm_mem (j : ℕ) :
    qPerm j ∈ genGroup 3850 c4Tabs c4Perm := by
  refine (genGroup 3850 c4Tabs c4Perm).list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  by_cases hj : j < 4
  · exact subset_closure ⟨i, by simpa [c4Tabs] using outer_parts.2.1 j hj i hi, rfl⟩
  · rw [List.getD_eq_default _ _ (by simp [qWords]; omega)] at hi
    exact absurd hi List.not_mem_nil

theorem c4_eq :
    genGroup 3850 c4Tabs c4Perm = hsC4 := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨-, -, -, h4, h5, -⟩ := hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
  dsimp only [CFSG.Sporadic.SmallOddCore.hsC] at h4 h5
  have h4' : hsC4 = Subgroup.closure
      (tp 3850 '' {x | x ∈ #[hsCentTbl 35, hsCentTbl 36, hsCentTbl 37, hsCentTbl 38]}) := h4.symm
  have h5' : Nat.card hsC4 = 1920 := h5
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [genGroup, closure_le, h4']
    rintro _ ⟨j, hj, rfl⟩
    have hj4 : j < 4 := by simpa [c4Tabs] using hj
    refine subset_closure ⟨hsCentTbl (j + 35), ?_, rfl⟩
    interval_cases j <;> simp
  · rw [h5', c4_enumerates.card, Array.length_toList, outer_parts.2.2.2.2.2.2.1]

theorem q_facts :
    Nat.card (genGroup 3850 qGens qPerm) = 16 ∧ genGroup 3850 qGens qPerm ≤ hsC4 ∧
      hsC4 ≤ normalizer (genGroup 3850 qGens qPerm : Set (Equiv.Perm (Fin 3850))) ∧
      Nat.card ↥(hsC4 ⊓ centralizer
        (genGroup 3850 qGens qPerm : Set (Equiv.Perm (Fin 3850)))) = 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [q_enumerates.card, Array.length_toList, outer_parts.2.2.2.1]
  · rw [← c4_eq, genGroup, closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact qPerm_mem j
  · rw [← c4_eq]
    exact le_normalizer_of_normalOK tabRep_c4Tabs tabRep_qGens q_enumerates
      outer_parts.2.2.2.2.1
  · rw [← c4_eq, card_inf_centralizer_of_enum c4_enumerates tabRep_qGens,
      outer_parts.2.2.2.2.2.2.2]

theorem c4_no_component
    {B : Subgroup (Equiv.Perm (Fin 3850))} (hB : CFSG.Assembly.IsComponentOf B hsC4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQcard, hQC4, hC4Q, hC4cent⟩ := q_facts
  rcases isComponentOf_le_or_commute hB hQC4 hC4Q with hle | hcomm
  · exact not_le_of_isPGroup hB.2.2 (isPGroup_two_of_card (k := 4) (by rw [hQcard]; norm_num)) hle
  · have hle : B ≤ hsC4 ⊓ centralizer
        (genGroup 3850 qGens qPerm : Set (Equiv.Perm (Fin 3850))) := by
      intro x hx
      refine mem_inf.mpr ⟨hB.1 hx, ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
      rw [mem_centralizer_iff] at this
      exact this y hy
    exact not_le_of_isPGroup hB.2.2
      (isPGroup_two_of_card (k := 4) (by rw [hC4cent]; norm_num)) hle

theorem outerC_no_small
    {B : Subgroup (Equiv.Perm (Fin 3850))}
    (hB : CFSG.Assembly.IsComponentOf B CFSG.QuasithinUnique.Id2519.HSAut.outerC)
    (hBt : Cov.SmallQ (↥B ⧸ center ↥B)) : False := by
  set C := CFSG.QuasithinUnique.Id2519.HSAut.outerC
  have : IsSimpleGroup ↥(commutator ↥C) := CFSG.QuasithinUnique.Id2519.HSAut.commutator_simple'
  have hc := (isComponentOf_iff_isComponent_subgroupOf hB.1).1 hB
  have hle := CFSG.QuasithinUnique.Id2519.le_commutator_of_isQuasisimple hc.1
  have htop := CFSG.QuasithinUnique.Id2519.isComponent_eq_top_of_isSimpleGroup
    (CFSG.LocalCores.component_overgroup hc hle)
  have hBeq : B.subgroupOf C = commutator ↥C := le_antisymm hle (subgroupOf_eq_top.mp htop)
  let e : ↥B ≃* ↥(commutator ↥C) :=
    (subgroupOfEquivOfLe hB.1).symm.trans (MulEquiv.subgroupCongr hBeq)
  have hBs : IsSimpleGroup ↥B := MulEquiv.isSimpleGroup e
  have hBcard : Nat.card ↥B = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.QuasithinUnique.Id2519.HSAut.card_commutator'
  have hZ : center ↥B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥B) with h | h
    · exact h
    · exfalso
      obtain ⟨-, hsimple⟩ := hB.2.2
      have : Subsingleton (↥B ⧸ center ↥B) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact (not_subsingleton (↥B ⧸ center ↥B)) this
  have hq : Nat.card (↥B ⧸ center ↥B) = 20160 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, hBcard]
  rcases Cov.card_of_smallQ hBt with ⟨q, hq'⟩ | h7
  · exact Cov.ordA_one_ne_of_lt (B := 35) (by norm_num) (by decide) q (hq'.symm.trans hq)
  · rw [hq] at h7
    exact absurd h7 (by norm_num)

end CFSG.ComponentClassification.GSThmB.CovHS
