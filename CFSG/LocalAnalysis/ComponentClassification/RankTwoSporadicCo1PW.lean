module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1PWTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.Sporadic.Schreier.Co1Base
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Sporadic.Co1Schreier
open scoped commutatorElement

section PerfGen

variable {W : Type*} [Group W]

structure PerfGen (P : Subgroup W) : Prop where
  perfect : ⁅P, P⁆ = P
  gen : ∃ x ∈ P, IsPGroup 2 (zpowers x) ∧ P ≤ closure {y | ∃ p ∈ P, y = p * x ^ 2 * p⁻¹}

theorem le_centDer_of_perfect {X P : Subgroup W} {t : W} (hPX : P ≤ X ⊓ centralizer {t})
    (hP : ⁅P, P⁆ = P) : P ≤ centDer X t := by
  rw [← hP]
  exact commutator_mono hPX hPX

theorem pWitness_of_perfGen {X E P : Subgroup W} {t : W} (ht : t ∈ E) (ht1 : t ≠ 1)
    (hPX : P ≤ X ⊓ centralizer {t}) (hP : PerfGen P) (hEP : ¬ E ≤ centralizer (P : Set W)) :
    PWitness X E := by
  obtain ⟨x, hx, hx2, hgen⟩ := hP.gen
  refine ⟨P, ?_, hP.perfect, hEP, x, hx, hx2, hgen⟩
  exact (le_centDer_of_perfect hPX hP.perfect).trans
    (le_iSup₂_of_le t ht (le_iSup_of_le ht1 le_rfl))

theorem PerfGen.map {U : Type*} [Group U] {P : Subgroup W} (hP : PerfGen P) (ι : W →* U) :
    PerfGen (P.map ι) := by
  obtain ⟨x, hx, hx2, hgen⟩ := hP.gen
  refine ⟨by rw [← map_commutator, hP.perfect], ι x, ⟨x, hx, rfl⟩, ?_, ?_⟩
  · rw [← MonoidHom.map_zpowers]
    exact hx2.map ι
  · refine (map_mono hgen).trans ?_
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨ι p, ⟨p, hp, rfl⟩, by simp⟩

theorem comm_of_isElemAbelian {E : Subgroup W} (hE : CFSG.Open.IsElemAbelian 2 E) {a b : W}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

end PerfGen

@[expose] def entryG (E : List GL24) (k : ℕ) : GL24 := E.getD (k - 1) 1

@[expose] def conjProdG (E : List GL24) (z : GL24) (ps : List ℕ) : GL24 :=
  ps.foldl (fun acc k => acc * (entryG E k * z * (entryG E k)⁻¹)) 1

theorem mrep_entry {E : List Native.Rows} {EG : List GL24} (h : List.Forall₂ MRep E EG)
    (k : ℕ) : MRep (entryR E k) (entryG EG k) :=
  getD_rep h MRep.one (k - 1)

theorem entryG_mem {H : Subgroup GL24} {E : List GL24} (h : ∀ g ∈ E, g ∈ H) (k : ℕ) :
    entryG E k ∈ H :=
  getD_mem_of_forall h (k - 1)

theorem mrep_conjProd_foldl {E : List Native.Rows} {EG : List GL24} (h : List.Forall₂ MRep E EG)
    {zr : Native.Rows} {z : GL24} (hz : MRep zr z) (ps : List ℕ) (hps : invsOK E ps = true) :
    ∀ (A : Native.Rows) (g : GL24), MRep A g →
      MRep (ps.foldl (fun acc k => Native.mul acc (Native.mul (Native.mul (entryR E k) zr)
        (Native.inv (entryR E k)))) A)
        (ps.foldl (fun acc k => acc * (entryG EG k * z * (entryG EG k)⁻¹)) g) := by
  induction ps with
  | nil => exact fun _ _ hA => hA
  | cons k ps ih =>
    intro A g hA
    simp only [invsOK, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hps
    have hk := mrep_entry h k
    have hki := hk.inv hps.1
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (by simpa [invsOK] using hps.2) _ _ (hA.mul ((hk.mul hz).mul hki))

theorem mrep_conjProd {E : List Native.Rows} {EG : List GL24} (h : List.Forall₂ MRep E EG)
    {zr : Native.Rows} {z : GL24} (hz : MRep zr z) {ps : List ℕ} (hinv : invsOK E ps = true) :
    MRep (conjProdR E zr ps) (conjProdG EG z ps) :=
  mrep_conjProd_foldl h hz ps hinv _ _ MRep.one

theorem conjProdG_mem {P : Subgroup GL24} {E : List GL24} (hE : ∀ g ∈ E, g ∈ P) (z : GL24)
    (ps : List ℕ) : conjProdG E z ps ∈ Subgroup.closure {y | ∃ p ∈ P, y = p * z * p⁻¹} := by
  unfold conjProdG
  suffices ∀ g ∈ Subgroup.closure {y | ∃ p ∈ P, y = p * z * p⁻¹},
      ps.foldl (fun acc k => acc * (entryG E k * z * (entryG E k)⁻¹)) g ∈
        Subgroup.closure {y | ∃ p ∈ P, y = p * z * p⁻¹} from this 1 (one_mem _)
  induction ps with
  | nil => exact fun g hg => hg
  | cons k ps ih =>
    intro g hg
    rw [List.foldl_cons]
    exact ih _ (mul_mem hg (Subgroup.subset_closure ⟨entryG E k, entryG_mem hE k, rfl⟩))

theorem decOK_spec {E : List Native.Rows} {EG : List GL24} (hE : List.Forall₂ MRep E EG)
    {zr : Native.Rows} {z : GL24} (hz : MRep zr z) {S : List Native.Rows} {SG : List GL24}
    (hS : List.Forall₂ MRep S SG) :
    ∀ {dec : List (List ℕ)}, decOK E zr S dec = true → ∀ g ∈ SG, ∃ ps, g = conjProdG EG z ps := by
  induction hS with
  | nil => intro dec _ g hg; exact absurd hg List.not_mem_nil
  | @cons s g' S' SG' hsg _ ih =>
    intro dec h g hg
    match dec, h with
    | ps :: dec', h =>
      simp only [decOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hinv, heq⟩, hrest⟩ := h
      rcases List.mem_cons.mp hg with rfl | hg
      · have hcp := mrep_conjProd hE hz hinv
        rw [heq] at hcp
        exact ⟨ps, hsg.eq hcp⟩
      · exact ih hrest g hg

theorem pw_of_check {S : List Native.Rows} {SG : List GL24} (hS : List.Forall₂ MRep S SG)
    {d₂ : List (List ℤ)} {iz ih : ℕ} {dec : List (List ℕ)} {r : Native.Rows} {rG : GL24}
    (hr : MRep r rG) (h : pwOK S d₂ iz ih dec r = true) :
    (∀ s ∈ SG, s * rG = rG * s) ∧ PerfGen (Subgroup.closure {g | g ∈ SG}) := by
  simp only [pwOK, pwCoreOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hD, ⟨⟨hz4, hhz⟩, hcomm⟩, hdec⟩ := h
  have hrep := dag_rep hS d₂ hD
  have hEG : ∀ g ∈ dagG SG d₂, g ∈ Subgroup.closure {g | g ∈ SG} :=
    dagG_mem (fun g hg => Subgroup.subset_closure hg) d₂
  have hzr := mrep_entry hrep iz
  have hhr := mrep_entry hrep ih
  have hz2r := hzr.mul hzr
  set z := entryG (dagG SG d₂) iz
  set hh := entryG (dagG SG d₂) ih
  have hz4' : z * z * (z * z) = 1 := (hz2r.mul hz2r).eq (by rw [hz4]; exact MRep.one)
  have hhz' : hh * z = z * z * z * hh :=
    (hhr.mul hzr).eq (by rw [hhz]; exact (hz2r.mul hzr).mul hhr)
  refine ⟨fun s hs => ?_, ?_⟩
  ·
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hjS : j < S.length := by rw [hS.length_eq]; exact hj
    have hc := List.all_eq_true.mp hcomm (S[j]) (List.getElem_mem hjS)
    simp only [commR, beq_iff_eq] at hc
    have hsr : MRep S[j] SG[j] := by
      have := getD_rep hS MRep.one j
      rwa [List.getD_eq_getElem _ _ hjS, List.getD_eq_getElem _ _ hj] at this
    exact (hsr.mul hr).eq (by rw [hc]; exact hr.mul hsr)
  · have hzP : z ∈ Subgroup.closure {g | g ∈ SG} := entryG_mem hEG iz
    have hhP : hh ∈ Subgroup.closure {g | g ∈ SG} := entryG_mem hEG ih
    have hgen : Subgroup.closure {g | g ∈ SG} ≤
        Subgroup.closure {y | ∃ p ∈ Subgroup.closure {g | g ∈ SG}, y = p * z ^ 2 * p⁻¹} := by
      refine (Subgroup.closure_le _).mpr fun g hg => ?_
      obtain ⟨ps, e⟩ := decOK_spec hrep hz2r hS hdec g hg
      rw [e, pow_two]
      exact conjProdG_mem hEG (z * z) ps
    have hcomm' : z ^ 2 = ⁅hh, z⁆ := by
      have e1 : hh * z * hh⁻¹ = z * z * z := by rw [hhz', mul_inv_cancel_right]
      rw [commutatorElement_def, e1, pow_two]
      group
    have hle : Subgroup.closure {g | g ∈ SG} ≤
        ⁅Subgroup.closure {g | g ∈ SG}, Subgroup.closure {g | g ∈ SG}⁆ := by
      refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
      rintro _ ⟨p, hp, rfl⟩
      rw [hcomm', show p * ⁅hh, z⁆ * p⁻¹ = ⁅p * hh * p⁻¹, p * z * p⁻¹⁆ by
        simp only [commutatorElement_def]; group]
      exact commutator_mem_commutator (mul_mem (mul_mem hp hhP) (inv_mem hp))
        (mul_mem (mul_mem hp hzP) (inv_mem hp))
    have hself : ⁅Subgroup.closure {g | g ∈ SG}, Subgroup.closure {g | g ∈ SG}⁆ ≤
        Subgroup.closure {g | g ∈ SG} :=
      commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    refine ⟨le_antisymm hself hle, z, hzP, ?_, hgen⟩
    have h4 : z ^ (2 ^ 2) = 1 := by
      rw [show 2 ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
      exact hz4'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h4)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

end CFSG.ComponentClassification.RankTwoSporadic.Co1
