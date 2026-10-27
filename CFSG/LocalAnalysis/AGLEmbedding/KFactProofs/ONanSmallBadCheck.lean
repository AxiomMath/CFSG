module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound
public import Certificates.Data.MaxD2NonComm

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm
open Certificates.FusD2Perm (powT wordT)

theorem noncomm_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data} (hn : D.n = n)
    (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (h : check D = true) (hT : checkNonComm D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)), R ≤ Subgroup.closure {g | g ∈ S} ∧
      Nat.card R = D.p ^ 2 ∧
      ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin n))) ⊓ Subgroup.closure {g | g ∈ S},
      ∃ b ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin n))) ⊓ Subgroup.closure {g | g ∈ S},
        a * b * a⁻¹ * b⁻¹ ∉ R := by
  subst hn
  show ∃ R : Subgroup (Equiv.Perm (Fin D.n)), R ≤ Gsub S ∧ Nat.card R = D.p ^ 2 ∧
    ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S,
    ∃ b ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S, a * b * a⁻¹ * b⁻¹ ∉ R
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hcardG : Nat.card (Gsub S) = D.gOrder := hcard
  have hNeq := normalizer_inf_eq hS hgi hlen hcardG hR hN hNorm hMoves hMax
  have hR' := enum_R hS hgi hR
  have hRok : enumOK D.n (rGens D) (rEnum D) = true := by
    simp only [checkR, Bool.and_eq_true] at hR
    exact hR.1
  have hinvs := invsOK_of_checkNormal hNorm
  simp only [checkNonComm, anyBelow_eq_true, Bool.not_eq_true'] at hT
  obtain ⟨i, hi, j, hj, hnot⟩ := hT
  have hi' : i < D.nW.length := by simpa [nGens] using hi
  have hj' : j < D.nW.length := by simpa [nGens] using hj
  have hra : TabRep (nGens D)[i]! ((D.nW.map (wordVal S))[i]'(by simpa using hi')) :=
    rep_getElem!_of_words S D.gT (giT D) hS hgi D.nW hi'
  have hrb : TabRep (nGens D)[j]! ((D.nW.map (wordVal S))[j]'(by simpa using hj')) :=
    rep_getElem!_of_words S D.gT (giT D) hS hgi D.nW hj'
  have hrai := invsOK_spec hinvs hi hra
  have hrbi := invsOK_spec hinvs hj hrb
  have hmemN : ∀ k (hk : k < D.nW.length), (D.nW.map (wordVal S))[k]'(by simpa using hk) ∈
      Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S := by
    intro k hk
    rw [hNeq]
    exact Subgroup.subset_closure (List.getElem_mem _)
  refine ⟨Rsub D S, Rsub_le_Gsub, card_R hS hgi hR, _, hmemN i hi', _, hmemN j hj', ?_⟩
  intro hmem
  have hcomm := TabRep.commTab hra hrb hrai hrbi
  have hfound := (found_iff_mem hRok hR' hcomm).2 (by simpa [commutatorElement_def] using hmem)
  rw [hfound] at hnot
  exact Bool.noConfusion hnot

theorem noncomm_of_checkHeis {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data} (hn : D.n = n)
    (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (h : Certificates.MaxD2Heis.checkHeis D = true)
    (hT : Certificates.MaxD2Heis.checkHNonComm D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)), R ≤ Subgroup.closure {g | g ∈ S} ∧
      Nat.card R = D.p ^ 3 ∧
      ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin n))) ⊓ Subgroup.closure {g | g ∈ S},
      ∃ b ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin n))) ⊓ Subgroup.closure {g | g ∈ S},
        a * b * a⁻¹ * b⁻¹ ∉ R := by
  subst hn
  show ∃ R : Subgroup (Equiv.Perm (Fin D.n)), R ≤ Gsub S ∧ Nat.card R = D.p ^ 3 ∧
    ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S,
    ∃ b ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S, a * b * a⁻¹ * b⁻¹ ∉ R
  simp only [Certificates.MaxD2Heis.checkHeis, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hZ⟩, hExp⟩, hComm⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hcardG : Nat.card (Gsub S) = D.gOrder := hcard
  have hNeq := normalizer_inf_eq_H hS hgi hlen hcardG hR hN hNorm hMoves hMax
  have hR' := enum_RH hS hgi hR
  have hRok : enumOK D.n (rGens D) (Certificates.MaxD2Heis.hrEnum D) = true := by
    simp only [Certificates.MaxD2Heis.checkHR, Bool.and_eq_true] at hR
    exact hR.1
  have hinvs := invsOK_of_checkHNormal hNorm
  simp only [Certificates.MaxD2Heis.checkHNonComm, anyBelow_eq_true, Bool.not_eq_true'] at hT
  obtain ⟨i, hi, j, hj, hnot⟩ := hT
  have hi' : i < D.nW.length := by simpa [nGens] using hi
  have hj' : j < D.nW.length := by simpa [nGens] using hj
  have hra : TabRep (nGens D)[i]! ((D.nW.map (wordVal S))[i]'(by simpa using hi')) :=
    rep_getElem!_of_words S D.gT (giT D) hS hgi D.nW hi'
  have hrb : TabRep (nGens D)[j]! ((D.nW.map (wordVal S))[j]'(by simpa using hj')) :=
    rep_getElem!_of_words S D.gT (giT D) hS hgi D.nW hj'
  have hrai := invsOK_spec hinvs hi hra
  have hrbi := invsOK_spec hinvs hj hrb
  have hmemN : ∀ k (hk : k < D.nW.length), (D.nW.map (wordVal S))[k]'(by simpa using hk) ∈
      Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S := by
    intro k hk
    rw [hNeq]
    exact Subgroup.subset_closure (List.getElem_mem _)
  refine ⟨Rsub D S, Rsub_le_Gsub, card_RH hS hgi hR, _, hmemN i hi', _, hmemN j hj', ?_⟩
  intro hmem
  have hcomm := TabRep.commTab hra hrb hrai hrbi
  have hfound := (found_iff_mem hRok hR' hcomm).2 (by simpa [commutatorElement_def] using hmem)
  rw [hfound] at hnot
  exact Bool.noConfusion hnot

end CFSG.AGLEmbedding.MaxD2
