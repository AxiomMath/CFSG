module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCentralPoint
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isMulCommutative_of_unique_generic {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) {x : G} (hx : IsGenericPoint p P M x)
    (hU : ∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x) (h5 : 5 ≤ p) {m : ℕ}
    (hm : 2 ≤ m) (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    IsMulCommutative (P : Subgroup G) := by
  have hPC := le_centralizer_of_unique_generic hPM hx hU
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsyl, hrk⟩ := hx
  rw [inf_of_le_left hPC] at hsyl hrk
  exact isMulCommutative_of_isSylowOf_mulEquiv_psl h5 hsyl (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _) hxP hx1 hxp (fun c hc => mem_centralizer_singleton_iff.mp hc)
    hrk.le hm e

@[expose] def GL83GenericStructureCore (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        (∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x) ∧ Group.IsSolvable M ∧
          rankThreeFrobeniusProduct (rankThreePrimeCore p M) (pCoreOf 2 M)
            (centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G))

theorem gl83GenericStructure_of_core (hS : Setting G) (hL : GL83GenericLayer G)
    (hB : GL83GenericStructureCore G) : GL83GenericStructure G := by
  intro p hp P M hM hfail hIH x hgen
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hU, hsol, hfrob⟩ := hB p hp P M hM hfail hIH x hgen
  obtain ⟨h5, hf, m, hm2, ⟨e⟩⟩ := hL p hp P M hM hfail hIH x hgen
  exact ⟨hU, isMulCommutative_of_unique_generic (sylow_le_of_isCoreMaxLocal hS hp hM).1 hgen hU
    h5 hm2 e, hsol, hfrob⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
