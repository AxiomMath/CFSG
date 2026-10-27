module

public import CFSG.GH74.Generic.BProg.B2.SDCheap
public import CFSG.GH74.Generic.BProg.B2.SDSmallComp
public import CFSG.GH74.Generic.BProg.B2.Thm2Assembly
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC23
import CFSG.GH74.Generic.BProg.B1.PilotS3
import CFSG.GH74.Generic.BProg.B2.Lemma82
import CFSG.GH74.Generic.BProg.B2.Lemma83Bar
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyBasic
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyG4
import CFSG.GH74.Generic.BProg.B2.TwoSided
import CFSG.GH74.Generic.JMaxCongr
import CFSG.GH74.GLS.C3.Layer1.BackConj
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B2.SD2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.GLS.C3.Layer1.Back (conjugateEquiv)

theorem false_of_c1_SD
    {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H B : Subgroup G} {h : G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H) (S : Sym8A M B h)
    (h3 : B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)) (hc1 : barIn M H = barIn M K)
    (hGen : ∀ (J : Type) [Group J] [Finite J], B1.QShape3SD J → GenProp J)
    (hWK : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J →
      QShape3 J → WeakSig2TwoG4 J)
    (hWS : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → SmallLie J →
      WeakSig2NormG4 J) : False := by
  classical
  have hnot := normalizer_pPrimeCoreOf_ne_top hs.hyp.simple S.maxM S.O_ne
  have hY4 := SDCheap.sectionalTwoRankLE_Mbar hs
  obtain ⟨hKc, -⟩ := Thm2AssemblyBasic.components_c1 hs h1 hc1
  obtain ⟨e⟩ := SDCheap.exists_equiv_barIn h1.K_le hKc
  obtain ⟨J₀, hJ₀, hnc⟩ := exists_component_Mbar_of_simple hs.hyp.simple S
  by_cases hJK : J₀ = barIn M K
  · subst hJK
    exact hnc (barK_centralized hs h1 S h3.qShape3 hc1 hWK)
  rcases smallComp_of_ne_barK hs h1 h3.qShape3 hc1 hJ₀ hJK with hSL | hSA
  · by_cases hN : barIn M (conjugate B h) ≤ normalizer (J₀ : Set (Mbar M))
    · exact hnc (sigX_le_centralizer_of_weakNormG4 S hnot hY4 hJ₀ (hWS ↥J₀ hJ₀.1 hSL) hN)
    ·
      obtain ⟨d, hdn⟩ := not_forall.1 hN
      obtain ⟨-, hdn⟩ := not_imp.1 hdn
      have hne : conjugate J₀ d ≠ J₀ := fun hc =>
        hdn (SDCheap.mem_normalizer_of_conjugate_eq' hc)
      have hdK : conjugate J₀ d = barIn M K := by
        by_contra hdK
        exact hne (component_eq_of_ne_barK hs h1 h3.qShape3 hc1
          (Thm2AssemblyBasic.isComponent_conjugate hJ₀ d) hJ₀ hdK hJK)
      have eJ : ↥J₀ ≃* (↥K ⧸ pPrimeCore 2 ↥K) :=
        ((conjugateEquiv J₀ d).trans (MulEquiv.subgroupCongr hdK)).trans e.symm
      have hq3 : QShape3 ↥J₀ := isL3OddGt3_of_mulEquiv eJ.symm h3.qShape3
      have hsimp : IsSimpleGroup ↥J₀ := by
        have := B1.PilotS3.isSimpleGroup_of_qShape3 h3.qShape3
        exact eJ.isSimpleGroup
      refine hnc (sigX_le_centralizer_of_weakTwoG4 S hnot hY4 hJ₀ (hWK ↥J₀ hJ₀.1 hsimp hq3)
        ⟨barIn M K, fun d' _ => ?_⟩)
      by_cases hd' : conjugate J₀ d' = barIn M K
      · exact Or.inr hd'
      · exact Or.inl (component_eq_of_ne_barK hs h1 h3.qShape3 hc1
          (Thm2AssemblyBasic.isComponent_conjugate hJ₀ d') hJ₀ hd' hJK)
  · exact false_of_smallAut hs h1 S h3 hc1 hGen hWK J₀ hJ₀ hJK hSA

theorem thm2CaseSDJ_of
    (hc23 : C23Kill)
    (hGen : ∀ (J : Type) [Group J] [Finite J], B1.QShape3SD J → GenProp J)
    (hWK : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J →
      QShape3 J → WeakSig2TwoG4 J)
    (hWS : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → SmallLie J →
      WeakSig2NormG4 J) : SD.Thm2CaseSDJ := by
  intro G _ _ x K A M P Q H hs h1 h3 _ B hBU g hg
  by_contra hgM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBM, hBel, -⟩ := hBU.1
  have hB2 : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  obtain ⟨h, hhM, hD, hBh⟩ := exists_two_sided_of_isPGroup hB2 hBM hg hgM
  let S : Sym8A M B h := ⟨hs.maxM, h1.O_ne, hBU, hhM, hD, hBh⟩
  by_cases hc1 : barIn M H = barIn M K
  · exact false_of_c1_SD hs h1 S h3 hc1 hGen hWK hWS
  · exact hc23 G x K A M P Q H B h hs h1 S hc1

end CFSG.GH74.Generic.BProg.B2.SD2
