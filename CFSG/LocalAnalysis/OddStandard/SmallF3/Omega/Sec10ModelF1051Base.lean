
module

public import Certificates.Data.OmegaF1051Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelT0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore

@[expose] public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

local notation "Q0l" => Certificates.OmegaF1051.q0l ()

local notation "CA0" => Certificates.OmegaF1051.centL (elemsT QA45) z0

local notation "CL0" => Certificates.OmegaF1051.centL (elemsT QP45) z0

def Q32 : Subgroup P45 := Subgroup.closure {g | g ∈ Certificates.OmegaF1051.q0l ()}

theorem mem_closure_list_iff {l : List P45} (h1 : (1 : P45) ∈ l) (hinv : ∀ a ∈ l, a⁻¹ ∈ l)
    (hmul : ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) {g : P45} :
    g ∈ Subgroup.closure {x | x ∈ l} ↔ g ∈ l := by
  constructor
  · intro hg
    let S : Subgroup P45 :=
      { carrier := {g | g ∈ l}
        mul_mem' := fun {a b} ha hb => hmul a ha b hb
        one_mem' := h1
        inv_mem' := fun {a} ha => hinv a ha }
    have hle : Subgroup.closure {x | x ∈ l} ≤ S := (Subgroup.closure_le S).2 fun x hx => hx
    exact hle hg
  · intro hg
    exact Subgroup.subset_closure hg

def oTwoC : Subgroup P45 :=
  oTwoRes (QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45))

end CFSG.OddStandard.SmallF3.Omega
