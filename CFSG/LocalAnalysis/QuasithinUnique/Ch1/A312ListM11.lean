module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM11Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLatAlt
public import Certificates.Certificate4084
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

namespace M11Lat

open Equiv PermLat
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4084.1

theorem diag_ok :
    diagOK (RN.enc : Perm (Fin 11) → RN 11) (RN.enc : Perm (Fin 6) → RN 6) 64
    aGens a6Gens 360 = true :=
  Certificates.certificate4084.2.1

theorem a_le :
    (List.range 5).all (fun j => cert.sizes.getD j 0 != 720 ||
    aGens.all fun g => (elts (RN.enc : Perm (Fin 11) → RN 11) 64
      ((cert.tGens :: cert.lat).getD j [])).contains (RN.enc g)) = true :=
  Certificates.certificate4084.2.2

theorem mGens_closure :
    Subgroup.closure {g | g ∈ cert.mGens} = CFSG.Blueprint.NativeSporadic.M11 := by
  unfold CFSG.Blueprint.NativeSporadic.M11
  congr 1
  ext g
  simp [cert, mGens]

abbrev Mgrp : Subgroup (Perm (Fin 11)) := Subgroup.closure {g | g ∈ cert.mGens}

abbrev Ugrp : Subgroup ↥Mgrp := (Subgroup.closure {g | g ∈ cert.tGens}).subgroupOf Mgrp

theorem aEquiv : Nat.card (Subgroup.closure {g | g ∈ aGens}) = 360 ∧
    Nonempty (↥(Subgroup.closure {g | g ∈ aGens}) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hA, ⟨e⟩⟩ := nonempty_mulEquiv_of_diagOK (rawIsEnc 11) (rawIsEnc 6) diag_ok
  have hle : Subgroup.closure {g | g ∈ a6Gens} ≤ alternatingGroup (Fin 6) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [a6Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      (rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]; decide)
  have hcard6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hc : Nat.card (Subgroup.closure {g | g ∈ a6Gens}) = 360 := by
    rw [← Nat.card_congr e.toEquiv, hA]
  have heq : Subgroup.closure {g | g ∈ a6Gens} = alternatingGroup (Fin 6) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard6])
  exact ⟨hA, ⟨e.trans (MulEquiv.subgroupCongr heq)⟩⟩

theorem a312For_M11_closure (hq : CFSG.IsQuasisimple ↥Mgrp) : A312For ↥Mgrp := by
  classical
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 11) hck (k := 4) (m := 495) (by decide) (by decide) (by omega)
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
    cert.overgroup_cases_idx (rawIsEnc 11) hck (B ⊔ Ugrp) le_sup_right
  have hlen : (cert.tGens :: cert.lat).length = 5 := by simp [cert, lat]
  rw [hlen] at hj
  have hM : Nat.card Mgrp = 7920 := cert.card_m (rawIsEnc 11) hcl hsz
  interval_cases j
  ·
    have h16 : cert.sizes.getD 0 0 = 16 := rfl
    rw [h16] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 4) (b := 0) (by rw [hcardj]; norm_num)
  ·
    have h720 : cert.sizes.getD 1 0 = 720 := rfl
    rw [h720] at hcardj
    have ha := List.all_eq_true.mp a_le 1 (by simp)
    simp only [h720, bne_self_eq_false, Bool.false_or] at ha
    have hlen1 : 1 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
    have hmem : (cert.tGens :: cert.lat)[1] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen1
    have hAL : Subgroup.closure {g | g ∈ aGens} ≤
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[1]} := by
      rw [Subgroup.closure_le]
      intro g hg
      have := List.all_eq_true.mp ha g hg
      rw [List.getD_eq_getElem _ _ hlen1] at this
      exact (mem_closure_iff_H (rawIsEnc 11) _ cert.depth
        (cert.members_closed hcl _ hmem) g).mpr (Std.HashSet.contains_iff_mem.mp this)
    obtain ⟨hAcard, ⟨eA⟩⟩ := aEquiv
    have hcomm : ⁅Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[1]},
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[1]}⁆ ≤
          Subgroup.closure {g | g ∈ aGens} :=
      commutator_le_of_card_eq_two_mul hAL (by rw [hcardj, hAcard])
    have hAM : Subgroup.closure {g | g ∈ aGens} ≤ Mgrp := hAL.trans hLM
    have hsimple := Seven.alt6_simple
    have hperf : ⁅Subgroup.closure {g | g ∈ aGens}, Subgroup.closure {g | g ∈ aGens}⁆ =
        Subgroup.closure {g | g ∈ aGens} :=
      Seven.perfect_of_equiv_simple Seven.alt6_nonabelian eA
    have hpc := perfectCore_subgroupOf_eq (M := Mgrp) hAL hLM hcomm hperf
    rw [← hPL] at hpc
    let eN : ↥(perfectCore (B ⊔ Ugrp)) ≃* alternatingGroup (Fin 6) :=
      (MulEquiv.subgroupCongr hpc).trans ((Subgroup.subgroupOfEquivOfLe hAM).trans eA)
    obtain ⟨eB⟩ := Seven.lFamily_equiv_of_perfectCore_equiv hB Seven.alt6_nonabelian eN
    iterate 9 right
    left
    refine ⟨⟨eB⟩, ⟨?_⟩⟩
    exact (Subgroup.topEquiv).trans (MulEquiv.subgroupCongr mGens_closure)
  ·
    have h48 : cert.sizes.getD 2 0 = 48 := rfl
    rw [h48] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 4) (b := 1) (by rw [hcardj]; norm_num)
  ·
    have h7920 : cert.sizes.getD 3 0 = 7920 := rfl
    rw [h7920] at hcardj
    exfalso
    apply hPne
    have heq := Subgroup.eq_of_le_of_card_ge hLM (by rw [hM]; exact hcardj.symm.le)
    rw [hPL]
    exact (congrArg (fun K => K.subgroupOf Mgrp) heq).trans (Subgroup.subgroupOf_self Mgrp)
  ·
    have h144 : cert.sizes.getD 4 0 = 144 := rfl
    rw [h144] at hcardj
    exfalso
    apply hPns
    rw [hPL]
    exact solvable_subgroupOf_two_three hLM (a := 4) (b := 2) (by rw [hcardj]; norm_num)

theorem a312For_M11 (hq : CFSG.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M11) :
    A312For ↥CFSG.Blueprint.NativeSporadic.M11 := by
  let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* ↥(Subgroup.closure {g | g ∈ cert.mGens}) :=
    (MulEquiv.subgroupCongr mGens_closure).symm
  exact A312For.of_mulEquiv e
    (a312For_M11_closure (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq))

end M11Lat

theorem m11 : FamM11 := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M11 := e
  exact A312For.of_mulEquiv e'
    (M11Lat.a312For_M11 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq))

end CFSG.QuasithinUnique.Vol2Native.A312L
