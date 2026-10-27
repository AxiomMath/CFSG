
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealNFBase
public import Certificates.Data.GrSLitL34FactsRealBCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

structure RealBParts : Prop where
  c2 : c2OK = true
  c6 : c6OK = true
  repS : repSOK = true

theorem kGensC_eq : kGensC = kGens := rfl

theorem inKC_iff (κ : ZMod 4 × ZMod 4) (i j : ZMod 4) : inKC κ i j ↔ inK κ i j := Iff.rfl

theorem tg_zero' : tg 0 = [] := rfl

theorem wordPerm_tg_zero' : wordPerm (tg 0) = 1 := by rw [tg_zero']; rfl

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

noncomputable abbrev nfM (l : Cover →* E) (x : MElt) : E :=
  nf l x.1 x.2.1 x.2.2

theorem mem_allM {x : MElt} (hx : x.1 < 64) : x ∈ allM := by
  obtain ⟨k, a, b⟩ := x
  unfold allM
  refine List.mem_flatMap.2 ⟨k, List.mem_range.2 hx, ?_⟩
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange _, List.mem_map.2 ⟨b, List.mem_finRange _, rfl⟩⟩

theorem lt_of_mem_allM {x : MElt} (hx : x ∈ allM) : x.1 < 64 := by
  unfold allM at hx
  obtain ⟨k, hk, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨a, -, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  exact List.mem_range.1 hk

section Setting

theorem nfM_one : nfM l oneM = 1 := nf_zero

end Setting

theorem pow4M_spec {t i : ℕ} (hi : i < 36) (h : pow4M t i = true) :
    (wordPerm (tg t) * repPerm i) ^ 4 = 1 := by
  have hy := (tabRep_wordTab (tg t)).comp (tabRep_repTab hi)
  have h4 := ((hy.comp hy).comp (hy.comp hy)).beq_iff TabRep.idTab
  simp only [pow4M] at h
  have e : (wordPerm (tg t) * repPerm i) ^ 4 =
      wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) *
        (wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i)) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]
  rw [e]
  exact h4.1 h

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
