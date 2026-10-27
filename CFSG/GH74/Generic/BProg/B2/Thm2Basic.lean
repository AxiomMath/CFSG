module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.Stage2Frozen

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

variable {G : Type} [Group G]

theorem gammaKC_le_gammaK (p : ℕ) (B : Subgroup G) (k : ℕ) : gammaKC p B k ≤ gammaK p B k :=
  iSup_mono fun Q => iSup_mono fun _ => iSup_mono fun _ => Subgroup.centralizer_le_normalizer (Q : Set G)

theorem InU0.toC {M B : Subgroup G} (h : InU0 M B) : InU0C M B :=
  ⟨h.1, h.2.1, (gammaKC_le_gammaK 2 B _).trans h.2.2⟩

theorem Stage2Concl2C.toConcl2 {M : Subgroup G} (h : Stage2Concl2C M) : Stage2Concl2 M :=
  fun B hB g hg => h B (InU0.toC hB) g hg

theorem stage2Thm2_of_C (h : Stage2Thm2C) : Stage2Thm2 :=
  fun G _ _ x K A M P Q H hs h1 =>
    Stage2Concl2C.toConcl2 (h G x K A M P Q H hs (Stage2Concl1.toCore h1))

end CFSG.GH74.Generic.BProg.B2
