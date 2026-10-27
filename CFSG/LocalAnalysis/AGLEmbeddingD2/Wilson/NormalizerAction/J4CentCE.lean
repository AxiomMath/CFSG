module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4C0pK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.CentOrderThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.WAJ4Facts
public import Certificates.Certificate12618
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRepBase

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc
  CFSG.AGLEmbeddingD2.Wilson.Coordinator Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem cent_iff {x y : J} : x ∈ centralizer ({y} : Set J) ↔ y * x = x * y :=
  ⟨fun h => mem_centralizer_iff.1 h y (Set.mem_singleton _), fun h =>
    mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact h⟩

theorem invChk_parts :
    eqRows (mulRows (invRows ()) cMat) (mulRows (mulRows cMat cMat) (invRows ())) = true ∧
      ∀ m < 4096, m = 0 ∨ ((!eqRows (mulRows (qNFRows false m) cMat)
          (mulRows cMat (qNFRows false m))) = true ∧
        (!eqRows (mulRows (qNFRows true m) cMat) (mulRows cMat (qNFRows true m))) = true) := by
  have h := Certificates.certificate12618
  simp only [invChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  exact h

section Words

set_option linter.unusedSectionVars false

@[expose] noncomputable def gWord (w : List ℕ) : J := w.foldl (fun acc n => acc * gE n) 1

theorem gWord_mem_M2 (w : List ℕ) (hw : ∀ n ∈ w, n < 32) : gWord w ∈ M2 := by
  have : ∀ (l : List ℕ), (∀ n ∈ l, n < 32) → ∀ acc : J, acc ∈ M2 →
      l.foldl (fun acc n => acc * gE n) acc ∈ M2 := by
    intro l
    induction l with
    | nil => intro _ acc h; exact h
    | cons n l ih =>
      intro hl acc hacc
      rw [List.foldl_cons]
      exact ih (fun m hm => hl m (List.mem_cons_of_mem _ hm)) _
        (M2.mul_mem hacc (gE_mem_M2 matFacts (hl n List.mem_cons_self)))
  exact this w hw 1 M2.one_mem

theorem Mx_gWord (w : List ℕ) (hw : ∀ n ∈ w, n < 32) :
    Mx (gWord w) = rowsMatrix (w.foldl (fun acc n => mulRows acc gmats[n]!) idRows) := by
  have : ∀ (l : List ℕ), (∀ n ∈ l, n < 32) → ∀ (acc : J) (R : Array V2),
      Mx acc = rowsMatrix R →
      Mx (l.foldl (fun acc n => acc * gE n) acc) =
        rowsMatrix (l.foldl (fun acc n => mulRows acc gmats[n]!) R) := by
    intro l
    induction l with
    | nil => intro _ acc R h; exact h
    | cons n l ih =>
      intro hl acc R hacc
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (fun m hm => hl m (List.mem_cons_of_mem _ hm)) _ _ ?_
      rw [map_mul, hacc, Mx_gE matFacts (hl n List.mem_cons_self), rowsMatrix_mulRows]
  exact this w hw 1 idRows (by rw [map_one, rowsMatrix_idRows])

end Words

section Facts

set_option linter.unusedSectionVars false

theorem invRows_eq : invRows () = invWord.foldl (fun acc n => mulRows acc gmats[n]!) idRows := rfl

theorem invWord_lt : ∀ n ∈ invWord, n < 32 := by decide +kernel

theorem exists_inv_cE : ∃ h ∈ M2, h * cE * h⁻¹ = cE⁻¹ := by
  refine ⟨gWord invWord, gWord_mem_M2 _ invWord_lt, ?_⟩
  have h3 := cE_pow_three matFacts
  have hc : cE⁻¹ = cE ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']; exact h3
  have hmain : gWord invWord * cE = cE ^ 2 * gWord invWord := by
    apply Mx_injective
    have h1 := congrArg rowsMatrix (eqRows_iff.1 invChk_parts.1)
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, invRows_eq] at h1
    rw [map_mul, map_mul, map_pow, Mx_gWord _ invWord_lt, Mx_cE matFacts, pow_two]
    exact h1
  rw [hc, hmain]
  group

theorem not_comm_of_chk {e : Bool} {m : ℕ}
    (h : (!eqRows (mulRows (qNFRows e m) cMat) (mulRows cMat (qNFRows e m))) = true) :
    ¬ (Coordinator.qNF e m * cE = cE * Coordinator.qNF e m) := by
  intro hc
  have hf : eqRows (mulRows (qNFRows e m) cMat) (mulRows cMat (qNFRows e m)) = false := by
    simpa using h
  have hw1 := wfR_mulRows (wfR_qNFRows e m) wfR_cMat
  have hw2 := wfR_mulRows wfR_cMat (wfR_qNFRows e m)
  apply ne_of_eqRows_false hw1 hw2 hf
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← Mx_qNF, ← Mx_cE matFacts, ← map_mul, ← map_mul,
    hc]

theorem centralizer_Qgrp_cE {x : J} (hx : x ∈ Qgrp) (hc : x * cE = cE * x) :
    x ∈ zpowers z0 := by
  obtain ⟨e, m, hm, rfl⟩ := mem_Qgrp_nf hx
  rcases (invChk_parts.2 m hm) with h0 | ⟨h1, h2⟩
  · subst h0
    have : Coordinator.qNF e 0 = if e then z0 else 1 := by simp [Coordinator.qNF, eta_zero]
    rw [this]
    split_ifs
    · exact mem_zpowers z0
    · exact one_mem _
  · exfalso
    cases e
    · exact not_comm_of_chk h1 hc
    · exact not_comm_of_chk h2 hc

theorem z0_comm_cE : Commute z0 cE := by
  have h0 : cE ∈ Subgroup.centralizer ({z0} : Set J) := cE_mem_M2 matFacts
  show z0 * cE = cE * z0
  exact cent_iff.1 h0

end Facts

section Main

theorem normal_Kgrp_subgroupOf (hF : J4Facts) : (Kgrp.subgroupOf M2).Normal := by
  have : Kgrp.subgroupOf M2 = (rho hF).ker := by
    ext g
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    exact mem_Kgrp_iff_rho hF g g.2
  rw [this]
  infer_instance

theorem card_centralizer_cE_M2 (hF : J4Facts) :
    Nat.card ↥(M2 ⊓ centralizer ({cE} : Set J)) = 2661120 := by
  obtain ⟨h, hhM, hinv⟩ := exists_inv_cE
  have key := card_centralizer_mul_card Qgrp cE z0 M2 (cE_normalizes_Qgrp matFacts)
    (cE_pow_three matFacts) (cE_ne_one matFacts) (card_Qgrp matFacts) (z0_mul_self matFacts)
    (z0_ne_one matFacts) (z0_mem_Qgrp matFacts) z0_comm_cE
    (fun q hq hqc => centralizer_Qgrp_cE hq hqc) (Kgrp_le_M2 hF) (normal_Kgrp_subgroupOf hF)
    (card_Kgrp hF) hhM hinv
  rw [card_M2 hF] at key
  generalize Nat.card ↥(M2 ⊓ centralizer ({cE} : Set J)) = x at key ⊢
  norm_num at key
  omega

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
