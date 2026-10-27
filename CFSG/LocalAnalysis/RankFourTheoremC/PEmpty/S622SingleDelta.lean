module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622P65
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65SC
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCField

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup I291P65
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def S622DeltaNPC : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A),
    Plane65 p P X x z → normalizer ((zpowers x ⊔ zpowers z : Subgroup A) : Set A) ≤ X →
    ∀ L : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf L ⊤ →
      (∀ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf K ⊤ → K = L) →
      IsLinearOrUnitaryAt p (↥L ⧸ center ↥L) →
      CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set A))

section CertificateInstances


theorem scCaseTwo_holds : SCCaseTwo :=
  scCaseTwo_of_kdata
    (kdMultP5_of_tables CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
    kdFieldP5_holds kd29Inner_holds

theorem s622KFactP65Single_of_delta (hδ : S622DeltaNPC) : S622KFactP65Single := by
  intro A _ _ p P X x z hpl hN hnpc hU W hWX hWcop hBW
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPX : (P : Subgroup A) ≤ X := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hxX : x ∈ X := hPX (hBP (Subgroup.mem_sup_left (mem_zpowers x)))
  have hzX : z ∈ X := hPX (hBP (Subgroup.mem_sup_right (mem_zpowers z)))
  have hpl63 := plane63_of_plane65 hpl hxX hzX
  obtain ⟨L, hL, hLu⟩ :=
    unique_component_of_uniquePComponent (primeComplementCore_quotient_eq_bot p) hU
  by_cases hlu : IsLinearOrUnitaryAt p (↥L ⧸ center ↥L)
  · exact absurd (hδ A p P X x z hpl hN L hL hLu hlu) hnpc
  · have hW'cop : Nat.Coprime p (Nat.card (W.subgroupOf X)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv]
    have hBmap : (zpowers (⟨x, hxX⟩ : ↥X) ⊔ zpowers (⟨z, hzX⟩ : ↥X)).map X.subtype =
        zpowers x ⊔ zpowers z := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    have hBW' : zpowers (⟨x, hxX⟩ : ↥X) ⊔ zpowers (⟨z, hzX⟩ : ↥X) ≤
        normalizer ((W.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      intro b hb
      have hb' : (b : A) ∈ zpowers x ⊔ zpowers z := hBmap ▸ mem_map_of_mem X.subtype hb
      have hn := Subgroup.mem_normalizer_iff.mp (hBW hb')
      refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
      exact hn (h : A)
    have hW := scCaseTwo_holds p ↥X (P.subtype hPX) ⟨x, hxX⟩ ⟨z, hzX⟩ hpl63 L hL hLu hlu
      (W.subgroupOf X) hW'cop hBW'
    intro w hw
    rw [rankThreePrimeCore_eq_map hprime]
    exact ⟨⟨w, hWX hw⟩, hW hw, rfl⟩

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
