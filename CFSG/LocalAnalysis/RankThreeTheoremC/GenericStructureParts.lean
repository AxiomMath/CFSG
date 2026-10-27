module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericPrimeCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericStructureRes
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericSolvable (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x → Group.IsSolvable M

@[expose] def GL83GenericFPF (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        ∀ v ∈ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G),
          v ≠ 1 → Odd (orderOf v) → Nat.Coprime p (orderOf v) →
            ∀ k ∈ pCoreOf 2 M, k * v = v * k → k = 1

theorem gl83GenericStructureRes_of_parts (hS : Setting G) (hD1 : TheoremD1 G)
    (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) (hF : FPFSolvable)
    (h1 : GL83GenericSolvable G) (h2 : GL83GenericFPF G) : GL83GenericStructureRes G := by
  intro p hp P M hM hfail hIH x hgen
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨h5, hf, m, hm2, ⟨e⟩⟩ := hL p hp P M hM hfail hIH x hgen
  have hsol : Group.IsSolvable M := h1 p hp P M hM hfail hIH x hgen
  refine ⟨hsol, fun v hv hv1 hcop => ?_, ?_⟩
  · have hodd := not_two_dvd_card_centralizer_layer hS hD1 hD2 hU0 hL hp hM hfail hIH hgen
    have hdvd : orderOf v ∣ Nat.card ↥(centralizer ((rankThreeLayer (centralizer ({x} : Set G)) :
        Subgroup G) : Set G)) := by
      have := Subgroup.orderOf_dvd_natCard _ hv
      simpa using this
    exact h2 p hp P M hM hfail hIH x hgen v hv hv1
      (Odd.of_dvd_nat (Nat.odd_iff.mpr (by omega)) hdvd) hcop
  · have hNM := (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M).1
    have : Group.IsSolvable (rankThreePrimeCore p M) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNM)
        (Subgroup.inclusion_injective hNM)
    exact rankThreePrimeCore_le_of_isSolvable hS hD1 hU0 hF hp hM hgen h5 hm2 e this

end CFSG.LocalAnalysis.RankThreeTheoremC
