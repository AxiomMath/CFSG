module

public import CFSG.GH74.Generic.BProg.B2.Thm2Assembly
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC23
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyBasic
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC1
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC2
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC3
import CFSG.GH74.Generic.BProg.B2.TwoSided
import CFSG.GH74.Generic.BProg.B2.Lemma82
import CFSG.GH74.Generic.BProg.B2.Lemma83Bar
import CFSG.GH74.Generic.BProg.B2.Thm2Comp
import CFSG.GH74.Generic.BProg.B2.TwoA7
public import Certificates.Kernel.ThCent.Leaves
import CFSG.GH74.Generic.BProg.B2.TwoA7Comp

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem sectionalTwoRankLE_Mbar {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) : SectionalTwoRankLE (Mbar M) 4 :=
  Gen4.quotient (pPrimeCore 2 ↥M) (Gen4.subgroup M hs.hyp.gen4)

theorem sigX_le_centralizer_of_weakNormG4 {G : Type} [Group G] [Finite G] {M B : Subgroup G}
    {h : G} (S : Sym8A M B h) (hnot : normalizer (pPrimeCoreOf 2 M : Set G) ≠ ⊤)
    (hY4 : SectionalTwoRankLE (Mbar M) 4) {J : Subgroup (Mbar M)} (hJ : IsComponent J)
    (hW : WeakSig2NormG4 ↥J) (hN : barIn M (conjugate B h) ≤ normalizer (J : Set (Mbar M))) :
    barIn M (sigX M h) ≤ centralizer (J : Set (Mbar M)) := by
  obtain ⟨hO, hDel, hrk, hWodd, -, hDW, hgam⟩ := sym8A_bar S hnot
  exact hW (Mbar M) hO hY4 J hJ ⟨MulEquiv.refl _⟩ (barIn M (conjugate B h))
    (barIn M (sigX M h)) hDel hrk hWodd hDW hgam hN

theorem sigX_le_centralizer_of_weakTwoG4 {G : Type} [Group G] [Finite G] {M B : Subgroup G}
    {h : G} (S : Sym8A M B h) (hnot : normalizer (pPrimeCoreOf 2 M : Set G) ≠ ⊤)
    (hY4 : SectionalTwoRankLE (Mbar M) 4) {J : Subgroup (Mbar M)} (hJ : IsComponent J)
    (hW : WeakSig2TwoG4 ↥J)
    (horb : ∃ L' : Subgroup (Mbar M), ∀ d ∈ barIn M (conjugate B h),
      conjugate J d = J ∨ conjugate J d = L') :
    barIn M (sigX M h) ≤ centralizer (J : Set (Mbar M)) := by
  obtain ⟨hO, hDel, hrk, hWodd, -, hDW, hgam⟩ := sym8A_bar S hnot
  exact hW (Mbar M) hO hY4 J hJ ⟨MulEquiv.refl _⟩ (barIn M (conjugate B h))
    (barIn M (sigX M h)) hDel hrk hWodd hDW hgam horb

end CFSG.GH74.Generic.BProg.B2
