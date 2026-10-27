module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriKac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriConv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriLayerTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints d4Nodes D4TrialityLayer)


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}

theorem excTri_perfect_E8 (S : LangSetup .E8 L p) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit .E8 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  obtain ⟨hnin, hA | ⟨hr', hc, hnin2⟩⟩ := exc_kind hk
  · exfalso; omega
  · obtain ⟨N, hN, hNL, hTN⟩ := excTri_exists_order S hT
    obtain ⟨v, hv, hρ⟩ := excTri_d4_pinned_E8 S hN hNL hT hTN i hr' hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact excTri_perfect_of_layer S i hρ
      (excTri_layer_untw d4Base_E8
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 S hFr hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hnin2)

theorem excTri_perfect_E7 (S : LangSetup .E7 L p) {a : Fin Tag.E7.rank → Lˣ}
    (hT : rootDiagUnit .E7 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  obtain ⟨hnin, hA | ⟨hr', hc, hnin2⟩⟩ := exc_kind hk
  · exfalso; omega
  · obtain ⟨N, hN, hNL, hTN⟩ := excTri_exists_order S hT
    obtain ⟨v, hv, hρ⟩ := excTri_d4_pinned_E7 S hN hNL hT hTN i hr' hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact excTri_perfect_of_layer S i hρ
      (excTri_layer_untw d4Base_E7
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 S hFr hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin hnin2)

theorem excTri_perfect_E6 (S : LangSetup .E6 L p) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit .E6 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  obtain ⟨hnin, hA | ⟨hr', hc, hnin2⟩⟩ := exc_kind hk
  · exfalso; omega
  · obtain ⟨N, hN, hNL, hTN⟩ := excTri_exists_order S hT
    obtain ⟨v, hv, hρ⟩ := excTri_d4_pinned_E6 S hN hNL hT hTN i hr' hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact excTri_perfect_of_layer S i hρ
        (excTri_layer_untw d4Base_E6 d4TrialityLayer_E6 S hFr hΦ' hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin hnin2)
    · rw [hs, Function.iterate_one] at hnin
      rw [hs, mul_one] at hnin2
      exact excTri_perfect_of_layer S i hρ
        (excTri_layer_twE6 S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin hnin2)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
