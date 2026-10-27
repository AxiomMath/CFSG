module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutAbs
public import Certificates.Certificate4147

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

@[expose] noncomputable def outerU : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl 21)

@[expose] noncomputable def outerC : Subgroup (Equiv.Perm (Fin 3850)) :=
  hsP ⊓ Subgroup.centralizer ({outerU} : Set (Equiv.Perm (Fin 3850)))

theorem exists_outerRow : ∃ r ∈ hsRows, r.rep = hsCentTbl 21 ∧
    r.centGens = [hsCentTbl 22, hsCentTbl 23, hsCentTbl 24, hsCentTbl 25] ∧
    r.centOrder = 40320 ∧ r.outer = true := by
  refine ⟨hsRows[2]'(by decide), List.getElem_mem _, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hsRows, List.getElem_cons_succ, List.getElem_cons_zero]

@[expose] noncomputable def outerRow : ClassRow := Classical.choose exists_outerRow

theorem outerRow_mem : outerRow ∈ hsRows := (Classical.choose_spec exists_outerRow).1

theorem outerRow_rep : outerRow.rep = hsCentTbl 21 := (Classical.choose_spec exists_outerRow).2.1

theorem outerRow_centGens : outerRow.centGens =
    [hsCentTbl 22, hsCentTbl 23, hsCentTbl 24, hsCentTbl 25] :=
  (Classical.choose_spec exists_outerRow).2.2.1

theorem outerRow_centOrder : outerRow.centOrder = 40320 :=
  (Classical.choose_spec exists_outerRow).2.2.2.1

theorem outerRow_C : hsC outerRow = outerC := by
  have h := (hs_involution_centralizers.2.2.2.1 outerRow outerRow_mem).2.2.2.1
  rw [h, outerRow_rep]
  rfl

theorem card_outerC : Nat.card ↥outerC = 40320 := by
  have h := (hs_involution_centralizers.2.2.2.1 outerRow outerRow_mem).2.2.2.2.1
  rw [outerRow_centOrder, outerRow_rep] at h
  exact h

theorem qGenT_size : ∀ l < 4, (qGenT l).size = 3850 ∧ permOK 3850 (qGenT l) = true := by
  have h := outerE_facts.1
  rw [allBelow_eq_true] at h
  intro l hl
  have := h l hl
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.2, this.1⟩

theorem tabRep_qPerm {l : ℕ} (hl : l < 4) : TabRep (natArr (qGenT l)) (qPerm l) :=
  tabRep_natArr (qGenT_size l hl).1 (qGenT_size l hl).2

theorem qPerm_mem {l : ℕ} (hl : l < 4) : qPerm l ∈ hsC outerRow := by
  apply Subgroup.subset_closure
  refine ⟨qGenT l, ?_, rfl⟩
  rw [outerRow_centGens]
  interval_cases l <;> simp [qGenT]

theorem tabRep_qWordTab {ls : List ℕ} (h : ∀ l ∈ ls, l < 4) :
    TabRep (qWordTab ls) (qWordPerm ls) :=
  tabRep_qWordTab' (fun _ hl => tabRep_qPerm hl) h

theorem qWordPerm_mem : ∀ {ls : List ℕ}, (∀ l ∈ ls, l < 4) → qWordPerm ls ∈ hsC outerRow
  | [], _ => by simp [qWordPerm]
  | l :: ls, h => by
    have h1 := qPerm_mem (h l List.mem_cons_self)
    have h2 := qWordPerm_mem (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    simpa [qWordPerm] using Subgroup.mul_mem _ h1 h2

theorem tabRep_e1 : TabRep e1Tab e1 := tabRep_qWordTab e1Letters_lt

theorem tabRep_e2 : TabRep e2Tab e2 := tabRep_qWordTab e2Letters_lt

theorem gensE_cover : ∀ a ∈ ({e1, e2} : Set (Equiv.Perm (Fin 3850))),
    ∃ j < gensE.size, TabRep gensE[j]! a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · have h0 : gensE[0]! = e1Tab := by simp [gensE]
    exact ⟨0, by simp [gensE], h0 ▸ tabRep_e1⟩
  · have h1 : gensE[1]! = e2Tab := by simp [gensE]
    exact ⟨1, by simp [gensE], h1 ▸ tabRep_e2⟩

theorem gensE_tabs : ∀ j < gensE.size,
    ∃ a ∈ ({e1, e2} : Set (Equiv.Perm (Fin 3850))), TabRep gensE[j]! a := by
  intro j hj
  have hj' : j < 2 := by simpa [gensE] using hj
  interval_cases j
  · have h0 : gensE[0]! = e1Tab := by simp [gensE]
    exact ⟨e1, by simp, h0 ▸ tabRep_e1⟩
  · have h1 : gensE[1]! = e2Tab := by simp [gensE]
    exact ⟨e2, by simp, h1 ▸ tabRep_e2⟩

theorem outerE_le_outerC : outerE ≤ outerC := by
  rw [← outerRow_C]
  refine (Subgroup.closure_le _).2 ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact qWordPerm_mem e1Letters_lt
  · exact qWordPerm_mem e2Letters_lt

theorem card_outerE : Nat.card ↥outerE = 20160 := by
  obtain ⟨-, hq, ρ, hρ, -⟩ := outerE_facts
  have hfin : Finite ↥outerC := Nat.finite_of_card_ne_zero (by rw [card_outerC]; norm_num)
  have hfinE : Finite ↥outerE := Finite.of_injective _ (Subgroup.inclusion_injective
    outerE_le_outerC)
  have hge : 20160 ≤ Nat.card ↥outerE := by
    rw [← hρ]
    exact Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
  have hdvd : Nat.card ↥outerE ∣ 40320 := by
    rw [← card_outerC]
    exact Subgroup.card_dvd_of_le outerE_le_outerC
  have hne : Nat.card ↥outerE ≠ 40320 := by
    intro h
    have heq : outerE = outerC :=
      Subgroup.eq_of_le_of_card_ge outerE_le_outerC (by rw [h, card_outerC])
    apply hq
    rw [heq, ← outerRow_C]
    exact qPerm_mem (by norm_num)
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

theorem outerE_equiv :
    ∃ ρ : outerE →* Equiv.Perm (Fin 35), ∃ _ : ↥outerE ≃* ↥ρ.range,
      ∃ e : Fin classSizes.size ≃ ConjClasses ρ.range,
        (∀ l, Nat.card (e l).carrier = classSizes[l.val]!) ∧
        ∃ l₀ : Fin classSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 := by
  obtain ⟨-, -, ρ, hρ, e, he⟩ := outerE_facts
  have hfin : Finite ↥ρ.range := Nat.finite_of_card_ne_zero (by rw [hρ]; norm_num)
  have hbij : Function.Bijective ρ.rangeRestrict :=
    ρ.rangeRestrict_surjective.bijective_of_nat_card_le (by rw [hρ, card_outerE])
  exact ⟨ρ, MulEquiv.ofBijective ρ.rangeRestrict hbij, e, he⟩

@[expose] noncomputable def conjClassesEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    ConjClasses H ≃ ConjClasses G where
  toFun := ConjClasses.map φ.symm.toMonoidHom
  invFun := ConjClasses.map φ.toMonoidHom
  left_inv c := by
    obtain ⟨h, rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (φ (φ.symm h)) = ConjClasses.mk h
    rw [MulEquiv.apply_symm_apply]
  right_inv c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (φ.symm (φ g)) = ConjClasses.mk g
    rw [MulEquiv.symm_apply_apply]

theorem card_conjClassesEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (c : ConjClasses H) :
    Nat.card (conjClassesEquiv φ c).carrier = Nat.card c.carrier := by
  obtain ⟨h, rfl⟩ := ConjClasses.mk_surjective c
  have e : conjClassesEquiv φ (ConjClasses.mk h) = ConjClasses.mk (φ.symm h) := rfl
  rw [e]
  apply Nat.card_congr
  refine φ.toEquiv.subtypeEquiv fun x => ?_
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
  show IsConj x (φ.symm h) ↔ IsConj (φ x) h
  constructor
  · intro hx
    have := MonoidHom.map_isConj φ.toMonoidHom hx
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this
  · intro hx
    have := MonoidHom.map_isConj φ.symm.toMonoidHom hx
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this

theorem outerE_classes :
    ∃ e : Fin classSizes.size ≃ ConjClasses ↥outerE,
      (∀ l, Nat.card (e l).carrier = classSizes[l.val]!) ∧
      ∃ l₀ : Fin classSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 := by
  obtain ⟨ρ, φ, e, hs, l₀, hl₀, he₀⟩ := outerE_equiv
  refine ⟨e.trans (conjClassesEquiv φ), fun l => ?_, l₀, hl₀, ?_⟩
  · rw [Equiv.trans_apply, card_conjClassesEquiv]
    exact hs l
  · rw [Equiv.trans_apply, he₀]
    show ConjClasses.mk (φ.symm 1) = ConjClasses.mk 1
    rw [map_one]

theorem classSums :
    ∀ l₀ : Fin classSizes.size, l₀.val = 0 → ∀ U : Finset (Fin classSizes.size),
    l₀ ∈ U → (∑ l ∈ U, classSizes[l.val]!) ∣ 20160 → U = {l₀} ∨ U = Finset.univ :=
  Certificates.certificate4147

theorem outerE_simple : IsSimpleGroup ↥outerE := by
  obtain ⟨e, hs, l₀, hl₀, he₀⟩ := outerE_classes
  have hfin : Finite ↥outerE := Nat.finite_of_card_ne_zero (by rw [card_outerE]; norm_num)
  refine isSimpleGroup_of_classes e (fun l => classSizes[l.val]!) hs l₀ he₀
    (by rw [card_outerE]; norm_num) ?_
  rw [card_outerE]
  exact classSums l₀ hl₀

theorem outerE_perfect : Group.IsPerfect ↥outerE := by
  have hs := outerE_simple
  rw [Group.isPerfect_def]
  rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥outerE) with hbot | htop
  · exfalso
    have hcomm : IsMulCommutative ↥outerE := ⟨⟨fun a b => by
      have h1 : ⁅a, b⁆ ∈ commutator ↥outerE :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1⟩⟩
    have hp := IsSimpleGroup.prime_card (α := ↥outerE)
    rw [card_outerE] at hp
    exact absurd hp (by norm_num)
  · exact htop

theorem index_outerE : (outerE.subgroupOf outerC).index = 2 := by
  have h1 := Subgroup.card_mul_index (outerE.subgroupOf outerC)
  have h2 : Nat.card (outerE.subgroupOf outerC) = Nat.card outerE :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe outerE_le_outerC).toEquiv
  rw [h2, card_outerE, card_outerC] at h1
  omega

theorem commutator_outerC_le : ⁅outerC, outerC⁆ ≤ outerE := by
  have hN : (outerE.subgroupOf outerC).Normal := Subgroup.normal_of_index_eq_two index_outerE
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hq : Nat.card (↥outerC ⧸ outerE.subgroupOf outerC) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact index_outerE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (↥outerC ⧸ outerE.subgroupOf outerC) := isCyclic_of_prime_card hq
  have hcomm : IsMulCommutative (↥outerC ⧸ outerE.subgroupOf outerC) := inferInstance
  have hmk : (QuotientGroup.mk' (outerE.subgroupOf outerC)) ⁅(⟨x, hx⟩ : ↥outerC), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  have hmem : ⁅(⟨x, hx⟩ : ↥outerC), ⟨y, hy⟩⁆ ∈ outerE.subgroupOf outerC :=
    (QuotientGroup.eq_one_iff _).1 hmk
  exact hmem

theorem commutator_outerC_eq : ⁅outerC, outerC⁆ = outerE := by
  apply le_antisymm commutator_outerC_le
  calc outerE = ⁅outerE, outerE⁆ := (Subgroup.isPerfect_iff.mp outerE_perfect).symm
    _ ≤ ⁅outerC, outerC⁆ := Subgroup.commutator_mono outerE_le_outerC outerE_le_outerC

theorem perfectResidualOf_outerC : perfectResidualOf outerC = outerE := by
  apply le_antisymm
  · calc perfectResidualOf outerC = ⁅perfectResidualOf outerC, perfectResidualOf outerC⁆ :=
          (commutator_perfectResidualOf outerC).symm
      _ ≤ ⁅outerC, outerC⁆ :=
          Subgroup.commutator_mono (perfectResidualOf_le' _) (perfectResidualOf_le' _)
      _ = outerE := commutator_outerC_eq
  · exact le_perfectResidualOf outerE_le_outerC outerE_perfect

theorem commutator_outerC_simple : IsSimpleGroup ↥⁅outerC, outerC⁆ := by
  rw [commutator_outerC_eq]
  exact outerE_simple

theorem card_commutator_outerC : Nat.card ↥⁅outerC, outerC⁆ = 20160 := by
  rw [commutator_outerC_eq]
  exact card_outerE

theorem index_commutator_outerC : (⁅outerC, outerC⁆.subgroupOf outerC).index = 2 := by
  rw [commutator_outerC_eq]
  exact index_outerE

theorem map_commutator_outerC : (commutator ↥outerC).map outerC.subtype = outerE := by
  rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  exact commutator_outerC_eq

theorem commutator_simple' : IsSimpleGroup ↥(commutator ↥outerC) := by
  have e : ↥(commutator ↥outerC) ≃* ↥((commutator ↥outerC).map outerC.subtype) :=
    Subgroup.equivMapOfInjective _ _ outerC.subtype_injective
  rw [map_commutator_outerC] at e
  exact (MulEquiv.isSimpleGroup_congr e).2 outerE_simple

theorem card_commutator' : Nat.card ↥(commutator ↥outerC) = 20160 := by
  have e : ↥(commutator ↥outerC) ≃* ↥((commutator ↥outerC).map outerC.subtype) :=
    Subgroup.equivMapOfInjective _ _ outerC.subtype_injective
  rw [map_commutator_outerC] at e
  rw [Nat.card_congr e.toEquiv]
  exact card_outerE

end CFSG.QuasithinUnique.Id2519.HSAut
