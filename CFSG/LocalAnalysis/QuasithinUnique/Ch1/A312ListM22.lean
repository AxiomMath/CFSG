module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLatAlt

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

namespace M22Lat

open Equiv PermLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem mGens_closure :
    Subgroup.closure {g | g ∈ cert.mGens} = CFSG.Blueprint.NativeSporadic.M22 := by
  unfold CFSG.Blueprint.NativeSporadic.M22
  congr 1
  ext g
  simp [cert, mGens]

abbrev Mgrp : Subgroup (Perm (Fin 22)) := Subgroup.closure {g | g ∈ cert.mGens}

abbrev Ugrp : Subgroup ↥Mgrp := (Subgroup.closure {g | g ∈ cert.tGens}).subgroupOf Mgrp

theorem closure_a5
    : Subgroup.closure {g | g ∈ a5Gens} = alternatingGroup (Fin 5) := by
  have hle : Subgroup.closure {g | g ∈ a5Gens} ≤ alternatingGroup (Fin 5) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [a5Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      (rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide)
  have hcard5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  obtain ⟨-, hc, -⟩ := exists_ext_of_diagExt (rawIsEnc 22) (rawIsEnc 5) ext5_ok
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard5])

theorem closure_a6
    : Subgroup.closure {g | g ∈ a6Gens} = alternatingGroup (Fin 6) := by
  have hle : Subgroup.closure {g | g ∈ a6Gens} ≤ alternatingGroup (Fin 6) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [a6Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      (rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide)
  have hcard6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  obtain ⟨-, hc, -⟩ := exists_ext_of_diagExt (rawIsEnc 22) (rawIsEnc 6) ext6_ok
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard6])

theorem ext5 : Nat.card (Subgroup.closure {g | g ∈ p5Gens}) = 960 ∧
    ∃ (V : Subgroup ↥(Subgroup.closure {g | g ∈ p5Gens})) (_ : V.Normal),
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 2 ^ 4 ∧
      Nonempty (↥(Subgroup.closure {g | g ∈ p5Gens}) ⧸ V ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨hA, hB, V, hV, hc, hsq, ⟨e⟩⟩ := exists_ext_of_diagExt (rawIsEnc 22) (rawIsEnc 5) ext5_ok
  refine ⟨hA, V, hV, hc, hsq, ?_, ⟨e.trans (MulEquiv.subgroupCongr closure_a5)⟩⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [Nat.card_congr e.toEquiv, hB, hA] at h
  omega

theorem ext6 : Nat.card (Subgroup.closure {g | g ∈ l6Gens}) = 5760 ∧
    ∃ (V : Subgroup ↥(Subgroup.closure {g | g ∈ l6Gens})) (_ : V.Normal),
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 2 ^ 4 ∧
      Nonempty (↥(Subgroup.closure {g | g ∈ l6Gens}) ⧸ V ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hA, hB, V, hV, hc, hsq, ⟨e⟩⟩ := exists_ext_of_diagExt (rawIsEnc 22) (rawIsEnc 6) ext6_ok
  refine ⟨hA, V, hV, hc, hsq, ?_, ⟨e.trans (MulEquiv.subgroupCongr closure_a6)⟩⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [Nat.card_congr e.toEquiv, hB, hA] at h
  omega

theorem a312For_M22_closure
    (hq : CFSG.IsQuasisimple ↥Mgrp) : A312For ↥Mgrp := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  refine A312For.of_sylow Ugrp hU fun B hB hBtop => ?_
  have hB' : B ∈ cComp (B ⊔ Ugrp) := hB
  have hPne : B ⊔ Ugrp ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hPns : ¬ Group.IsSolvable ↥(B ⊔ Ugrp) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ Ugrp))
        (Subgroup.inclusion_injective _))
  obtain ⟨j, hj, hLM, hPL, hcardj⟩ :=
    cert.overgroup_cases_idx (rawIsEnc 22) hck (B ⊔ Ugrp) le_sup_right
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  rw [hlen] at hj
  have hM : Nat.card Mgrp = 443520 := cert.card_m (rawIsEnc 22) hcl hsz
  interval_cases j
  ·
    have h128 : cert.sizes.getD 0 0 = 128 := rfl
    rw [h128] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 0) (by rw [hcardj]; norm_num)
  ·
    have h384 : cert.sizes.getD 1 0 = 384 := rfl
    rw [h384] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 1) (by rw [hcardj]; norm_num)
  ·
    have h1920 : cert.sizes.getD 2 0 = 1920 := rfl
    rw [h1920] at hcardj
    have ha := List.all_eq_true.mp incl5 2 (by simp)
    simp only [h1920, bne_self_eq_false, Bool.false_or] at ha
    have hlen2 : 2 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[2] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen2
    have hAL : Subgroup.closure {g | g ∈ p5Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen2] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, V, hVn, hVc, hVsq, hVcard, ⟨e⟩⟩ := ext5
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[2]}⁆ ≤
          Subgroup.closure {g | g ∈ p5Gens} :=
      commutator_le_of_card_eq_two_mul hAL (by rw [hcardj, hAcard])
    have hperf : ⁅Subgroup.closure {g | g ∈ p5Gens}, Subgroup.closure {g | g ∈ p5Gens}⁆ =
        Subgroup.closure {g | g ∈ p5Gens} := perfect_of_perfOK (rawIsEnc 22) perf5_ok
    have hsimple := Seven.alt5_simple
    have hext := isExt_of_perfectCore_ext (M := Mgrp) hB hAL hLM hcomm hperf hPL
      Seven.alt5_nonabelian V hVc hVsq hVcard e
    iterate 10 right
    left
    left
    exact ⟨Or.inl hext, ⟨(Subgroup.topEquiv).trans (MulEquiv.subgroupCongr mGens_closure)⟩⟩
  ·
    have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
    rw [h5760] at hcardj
    have ha := List.all_eq_true.mp incl6 3 (by simp)
    simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
    have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
    have hAL : Subgroup.closure {g | g ∈ l6Gens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen3] at this
      exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, V, hVn, hVc, hVsq, hVcard, ⟨e⟩⟩ := ext6
    have hLA := Subgroup.eq_of_le_of_card_ge hAL (by rw [hcardj, hAcard])
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]}⁆ ≤
          Subgroup.closure {g | g ∈ l6Gens} := by
      rw [← hLA]
      exact commutator_self_le _
    have hperf : ⁅Subgroup.closure {g | g ∈ l6Gens}, Subgroup.closure {g | g ∈ l6Gens}⁆ =
        Subgroup.closure {g | g ∈ l6Gens} := perfect_of_perfOK (rawIsEnc 22) perf6_ok
    have hsimple := Seven.alt6_simple
    have hext := isExt_of_perfectCore_ext (M := Mgrp) hB hAL hLM hcomm hperf hPL
      Seven.alt6_nonabelian V hVc hVsq hVcard e
    iterate 10 right
    left
    left
    exact ⟨Or.inr hext, ⟨(Subgroup.topEquiv).trans (MulEquiv.subgroupCongr mGens_closure)⟩⟩
  ·
    have h443520 : cert.sizes.getD 4 0 = 443520 := rfl
    rw [h443520] at hcardj
    exfalso
    apply hPne
    have heq := Subgroup.eq_of_le_of_card_ge hLM (by rw [hM]; exact hcardj.symm.le)
    rw [hPL]
    exact (congrArg (fun K => K.subgroupOf Mgrp) heq).trans (Subgroup.subgroupOf_self Mgrp)
  ·
    have h384 : cert.sizes.getD 5 0 = 384 := rfl
    rw [h384] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 7) (b := 1) (by rw [hcardj]; norm_num)

theorem a312For_M22
    (hq : CFSG.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M22) :
    A312For ↥CFSG.Blueprint.NativeSporadic.M22 := by
  let e : ↥CFSG.Blueprint.NativeSporadic.M22 ≃* ↥(Subgroup.closure {g | g ∈ cert.mGens}) :=
    (MulEquiv.subgroupCongr mGens_closure).symm
  exact A312For.of_mulEquiv e
    (a312For_M22_closure (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq))

end M22Lat

theorem m22 : FamM22 := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  exact A312For.of_mulEquiv e'
    (M22Lat.a312For_M22 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq))

end CFSG.QuasithinUnique.Vol2Native.A312L
