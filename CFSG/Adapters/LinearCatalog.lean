module

public import CFSG.Adapters.TypeALinearCandidate
public import CFSG.Adapters.LinearFieldTransport
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

noncomputable section

namespace CFSG.ClassicalModels

open Matrix TauCeti CFSG.Assembly.LowTwoRank

def linearCatalogCandidateEquivPSL
    (r : ℕ) (q : PrimePower) [Fact q.p.Prime]
    (hv : (LieTypeIndex.A r q).Valid) :
    (ValidLieTypeIndex.Group ⟨LieTypeIndex.A r q, hv⟩) ≃*
      ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent) := by
  change (TypeALieIndex.ofA r q hv).Group ≃*
    ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent)
  exact typeALinearCandidateEquivPSL r q hv

theorem linearCatalog_index_valid
    (n p f : ℕ) (h : StatedLieAdmissible .PSL n p f)
    (hdup : ¬ (LieTypeIndex.A (n - 1)
      ⟨p, f, h.1, by have hf := h.2.1; omega⟩).IsDuplicateRepresentative) :
    (LieTypeIndex.A (n - 1)
      ⟨p, f, h.1, by have hf := h.2.1; omega⟩).Valid := by
  rw [LieTypeIndex.valid_iff]
  refine ⟨?_, hdup⟩
  rw [LieTypeIndex.inStandardRange_iff]
  simp only [PrimePower.card_def]
  have hn : 2 ≤ n := h.2.2.1
  refine ⟨by omega, ?_⟩
  intro hr
  have hn2 : n = 2 := by omega
  have h22 : (n, p ^ f) ≠ (2, 2) := h.2.2.2.1
  have h23 : (n, p ^ f) ≠ (2, 3) := h.2.2.2.2
  have hp2 : p ^ f ≠ 2 := fun hp => h22 (Prod.ext hn2 hp)
  have hp3 : p ^ f ≠ 3 := fun hp => h23 (Prod.ext hn2 hp)
  have hpow : 2 ≤ p ^ f :=
    (h.1.two_le).trans (Nat.le_self_pow (by have hf := h.2.1; omega) p)
  omega

theorem statedClassicalModel_PSL_inCatalog_of_not_duplicate
    (G : Type) [Group G] (n p f : ℕ) (h : StatedClassicalModel G .PSL n p f)
    (hdup : ¬ (LieTypeIndex.A (n - 1)
      ⟨p, f, h.1.1, by have hf := h.1.2.1; omega⟩).IsDuplicateRepresentative) :
    CFSG.Assembly.InCatalog G := by
  let q : PrimePower := ⟨p, f, h.1.1, by have hf := h.1.2.1; omega⟩
  let _ : Fact p.Prime := ⟨h.1.1⟩
  have hv : (LieTypeIndex.A (n - 1) q).Valid :=
    linearCatalog_index_valid n p f h.1 hdup
  obtain ⟨K, hfield, hfinite, hKcard, e⟩ := h.2
  let _ := hfield
  let _ := hfinite
  obtain ⟨e⟩ := e
  let eK := statedLinearModelEquivGaloisPSL K n p f
    (by have hf := h.1.2.1; omega) hKcard
  have hdim : n - 1 + 1 = n := by have hn := h.1.2.2.1; omega
  have eC := linearCatalogCandidateEquivPSL (n - 1) q hv
  have eC' : (ValidLieTypeIndex.Group ⟨LieTypeIndex.A (n - 1) q, hv⟩) ≃*
      ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f) := by
    rw [hdim] at eC
    exact eC
  exact ⟨.lie ⟨LieTypeIndex.A (n - 1) q, hv⟩, ⟨(e.trans eK).trans eC'.symm⟩⟩

end CFSG.ClassicalModels
