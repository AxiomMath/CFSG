module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.FixedCase

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (Coord)
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks (isComponentOf_centralizerImage_cases)

section Top


variable (K : Type) [Field K] [Finite K]

theorem finrank_fixedSpace_four_or_six {y : (Coord → K) ≃ₗ[K] (Coord → K)}
    (hyΩ : y ∈ orthDerived (quadPlus 4 K)) (hy1 : y ≠ 1)
    (hlist : FixedLayerListed (quadPlus 4 K) y) :
    finrank K (fixedSpace y) = 4 ∨ finrank K (fixedSpace y) = 6 := by
  have hQ := nondegenerate_quadPlus_four K
  have hev := even_finrank_sub_fixedSpace hQ hyΩ
  have hV : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by simp
  have h3 : 3 ≤ finrank K (fixedSpace y) := hlist.1
  have hle : finrank K (fixedSpace y) ≤ 8 := by
    rw [← hV]
    exact Submodule.finrank_le _
  have hne : finrank K (fixedSpace y) ≠ 8 := by
    intro h8
    apply hy1
    have htop : fixedSpace y = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h8, hV])
    refine LinearEquiv.ext fun v => ?_
    have : v ∈ fixedSpace y := htop ▸ Submodule.mem_top
    exact CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace.1 this
  obtain ⟨r, hr⟩ := hev
  have key : 8 - finrank K (fixedSpace y) = r + r := by
    rw [← hV]
    exact hr
  omega

theorem rootSL2_of_component (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hK3 : ringChar K ≠ 3) (T2 : LeviSelfDual K) (T3 : LeviFixed K) (T4 : SixNotL2 K)
    {x : orthDerived (quadPlus 4 K)} (hx3 : orderOf x = 3)
    (hx : OddOrderIsometry (quadPlus 4 K) 3 (x : (Coord → K) ≃ₗ[K] (Coord → K)))
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives (x : (Coord → K) ≃ₗ[K] (Coord → K)) Rep)
    {I : Subgroup (ProjOrthDerived (quadPlus 4 K))}
    (hI : CFSG.Open.IsComponentOf I
      (centralizerImage (quadPlus 4 K) (x : (Coord → K) ≃ₗ[K] (Coord → K)))) {q : ℕ}
    (hq : 64 ≤ q) (hT : IsTypeL2 q ↥I) :
    ∃ c : adjointGroup Tag.D4 K, I.map (eTheta K).toMonoidHom =
      (simplePosSubgroup Tag.D4 K node0 ⊔ simpleNegSubgroup Tag.D4 K node0).map
        (MulAut.conj c).toMonoidHom := by
  classical
  rcases isComponentOf_centralizerImage_cases (nondegenerate_quadPlus_four K) Nat.prime_three
    (by norm_num) x hx hRep hI with
    ⟨h, hh, hne1, hqs, rfl⟩ | ⟨hlist, n, C, hsup, hC, hcomm, i, rfl⟩
  · exact rootSL2_of_block K hO T2 hx (hRep.1 hh) hne1 hqs hq hT
  · have hIle : C i ≤ fixedComponentImage (quadPlus 4 K) (x : (Coord → K) ≃ₗ[K] (Coord → K)) := by
      rw [← hsup]
      exact le_iSup C i
    have hx1 : (x : (Coord → K) ≃ₗ[K] (Coord → K)) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx3
      omega
    rcases finrank_fixedSpace_four_or_six K x.2 hx1 hlist with hw | hw
    · exact rootSL2_of_fixed_four K hK3 T2 T3 hx hlist hw hI hIle
    · exact (false_of_fixed_six K hK3 T4 hx hlist hw hI hIle hq hT).elim

end Top

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
