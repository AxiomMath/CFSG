module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Transfer
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CoverToCatalog
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.I137Tr
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem i137At_of_comp {G : Type} [Group G] [Finite G] {p : ℕ}
    (hA : I137ChevClosureComp) (hBT : I137BorelTits) (hO5 : I137Order5) (hL3 : I137LieCore3) :
    I137At G p := by
  intro hp hp2 Y J I S x hY hJ hcov hS hS2 hSn hxN hx _hC hI hI₀ _hxS hcat
  obtain ⟨I₀, hI₀I, hI₀O, hI₀N⟩ := hI₀
  have hIJ : I ≤ J := hI.1.trans inf_le_left
  have hI₀J : I₀ ≤ J := hI₀I.trans hIJ
  have hKq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hchev : IsChevSimple 2 (PQuot p J ⧸ Subgroup.center (PQuot p J)) := by
    obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian hp hJ
    have hlev : IsChevSimple p (PSimple p J) ∨ catalogIs (PSimple p J) (k2 p) := by
      rcases k1Cover_or_k2Cover_of_fullCoverLevel_le_two hcov with h | h
      · exact Or.inl h.2
      · exact Or.inr (k2Cover_imp_catalogIs p h)
    have hK : CFSG.Open.IsKGroup (PSimple p J) :=
      ((CFSG.Open.IsKGroup.of_le hY hJ.1).quotient _).quotient _
    have hxp : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx
    obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp hxN hxp hI
    exact hA p hp hp2 (PSimple p J) hsimple hnonab hK hlev (chevAut p J ⟨x, hxN⟩)
      (chevAut_pow_eq_one p J hxN hx) _ (glaPComponent_chevTransfer hp hxN hxp hI)
      ((catalogIs_congr e).1 hcat)
  have hT2 : IsPGroup 2 ((barX p J S).map (QuotientGroup.mk' (Subgroup.center (PQuot p J)))) :=
    (isPGroup_barX hS2 hS).map _
  have hT0 := barX_map_ne_bot hp hp2 hS hS2 hSn
  have hAN : (phi0 p hI₀J).range ≤ Subgroup.normalizer
      (((barX p J S).map (QuotientGroup.mk' (Subgroup.center (PQuot p J)))) : Set _) := by
    rintro g ⟨a, rfl⟩
    exact phi0_mem_normalizer hI₀J hS hI₀N a
  have hfA : ∃ f : (phi0 p hI₀J).range →* PSimple p I, Function.Surjective f :=
    ⟨factorThrough (phi0 p hI₀J) ((psiI p I).comp (Subgroup.inclusion hI₀I))
        (phi0_ker_le hp hIJ hI₀I),
      factorThrough_surjective _ _ _ (psiI_comp_inclusion_surjective hI₀I hI₀O)⟩
  have hcases : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 7 with h | h
    · interval_cases p <;> first | omega | (norm_num at hp)
    · exact Or.inr (Or.inr h)
  rcases hcases with h3 | h5 | h7
  · subst h3
    obtain ⟨f, hf⟩ := hfA
    exact ⟨rfl, hL3 (PQuot 3 J) hKq hcov hchev _ _ hT2 hT0 hAN (PSimple 3 I) ⟨f, hf⟩ hcat⟩
  · subst h5
    exfalso
    obtain ⟨P, hPtop, hNP⟩ := hBT _ hchev _ hT2 hT0
    obtain ⟨f, hf⟩ := hfA
    have hAP : (phi0 5 hI₀J).range ≤ P := hAN.trans hNP
    have h1 : Nat.card (PSimple 5 I) ≤ Nat.card (phi0 5 hI₀J).range :=
      Nat.card_le_card_of_surjective f hf
    have h2 : Nat.card (phi0 5 hI₀J).range ≤ Nat.card P :=
      Subgroup.card_le_of_le hAP
    have h3 : Nat.card P < Nat.card (PSimple 5 J) := by
      have hlt : P < ⊤ := lt_top_iff_ne_top.2 hPtop
      have := card_lt_of_lt' hlt
      rwa [Subgroup.card_top] at this
    have h4 : Nat.card (PSimple 5 J) ≤ Nat.card (PSimple 5 I) :=
      hO5 (PQuot 5 J) hKq hcov hchev (PSimple 5 I) hcat
    omega
  · exfalso
    obtain ⟨i, hi, _⟩ := hcat
    exact isList93_eq_false_of_ge_seven h7 i hi

theorem i137_of_comp {G : Type} [Group G] [Finite G] {p : ℕ}
    (hA : I137ChevClosureComp) (hBT : I137BorelTits) (hO5 : I137Order5) (hL3 : I137LieCore3) :
    I137At G p :=
  i137At_of_comp hA hBT hO5 hL3

theorem i137_3_of_comp {G : Type} [Group G] [Finite G]
    (hA : I137ChevClosureComp) (hBT : I137BorelTits) (hO5 : I137Order5) (hL3 : I137LieCore3) :
    I137At G 3 :=
  i137At_of_comp hA hBT hO5 hL3

end CFSG.LocalAnalysis.GLTheoremA
