module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockAlt
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockFrame
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockHom
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockLift
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockPure
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockS

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section CaseThree
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]
section A5Leaves
variable {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7))}
  {V₄ B : Subgroup ↥(alternatingGroup (Fin 7))} {Ik : Subgroup X}

theorem a7_gen_A5 {V₄ : Subgroup ↥(alternatingGroup (Fin 7))} (hV₄ : IsRootFour V₄) :
    ∃ B : Subgroup ↥(alternatingGroup (Fin 7)), V₄ ≤ B ∧
      Nonempty (↥B ≃* ↥(alternatingGroup (Fin 5))) ∧
      ∀ H : Subgroup ↥(alternatingGroup (Fin 7)), B ≤ H →
        Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))) ≤ H → H = ⊤ :=
  A5Alt.a7_gen_A5_aux hV₄

theorem a5_lift (h : Setup28 W K S)
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7)))
    {B : Subgroup ↥(alternatingGroup (Fin 7))} (hB : Nonempty (↥B ≃* ↥(alternatingGroup (Fin 5)))) :
    ∃ Ik : Subgroup X, Ik ≤ K ∧ (∀ k : ↥K, (k : X) ∈ Ik → piOf e k ∈ B) ∧
      (∀ b ∈ B, ∃ k : ↥K, (k : X) ∈ Ik ∧ piOf e k = b) ∧
      ∀ k : ↥K, (k : X) ∈ Ik → piOf e k = 1 → (k : X) ∈ W := A5Lift.a5_lift_aux h e hB

theorem a5_S_dec (h : Setup28 W K S) (hR : Red28 W K S)
    {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7))}
    (hroot : ActsLikeRootFourCQ (bar W S) (bar W K) 7 e)
    (hS4 : Nat.card ↥(bar W S ⊓ bar W K) = 4) (hind : Nat.card ↥(indAut W K S) = 4) :
    ∃ V₄ : Subgroup ↥(alternatingGroup (Fin 7)), IsRootFour V₄ ∧ SOverV4 W K S (piOf e) V₄ :=
  A5S.a5_S_dec_aux h hroot hS4 hind

theorem a5_NK (h : Setup28 W K S) (hR : Red28 W K S)
    {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7))}
    {V₄ : Subgroup ↥(alternatingGroup (Fin 7))} (hsv : SOverV4 W K S (piOf e) V₄) :
    ∀ g ∈ Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))),
      ∃ k : ↥K, (k : X) ∈ Subgroup.normalizer (S : Set X) ∧ piOf e k = g :=
  A5S.a5_NK_aux h hR hsv

theorem a5_I_hom (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    ∃ φ : ↥(Ik ⊔ S) →* ↥(alternatingGroup (Fin 5)), Function.Surjective φ ∧
      ∀ x : ↥(Ik ⊔ S), φ x = 1 ↔ (x : X) ∈ kerAct W K S := A5Hom.a5_I_hom_aux h hR d

theorem oTwo_of_hom {I N : Subgroup X} (hNI : N ≤ I) (hN : IsPGroup 2 ↥N)
    (φ : ↥I →* ↥(alternatingGroup (Fin 5))) (hφ : Function.Surjective φ)
    (hker : ∀ x : ↥I, φ x = 1 ↔ (x : X) ∈ N) :
    pCoreOf 2 I = N ∧ Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥(alternatingGroup (Fin 5))) :=
  A5Pure.oTwo_of_hom_aux hNI hN φ hφ hker

theorem a5_I_sylow (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    CFSG.QuasithinUnique.IsSylowTwoOf S (Ik ⊔ S) := A5Hom.a5_I_sylow_aux h hR d

theorem a5_I_dec_zker (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    (∀ i ∈ Ik ⊔ S, ∃ k ∈ K, k ∈ Ik ⊔ S ∧ i * k⁻¹ ∈ kerAct W K S) ∧
      (Ik ⊔ S) ⊓ zPre W K ≤ kerAct W K S := A5Hom.a5_I_dec_zker_aux h hR d

theorem a5_I_gen (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    ∀ H : Subgroup X, H ≤ K → (Ik ⊔ S) ⊓ K ≤ H →
      (∀ k ∈ K, k ∈ Subgroup.normalizer (S : Set X) → k ∈ H) → K ≤ H ⊔ (K ⊓ kerAct W K S) :=
  A5Hom.a5_I_gen_aux h hR d

end A5Leaves

theorem a5_nochar (h : Setup28 W K S) (hR : Red28 W K S) (hd : ¬ Concl28d K S) {I : Subgroup X}
    (hI : A5Frame W K S I) : CFSG.QuasithinUnique.Setup.Campbell.NoCharNormal S I :=
  A5Fr.a5_nochar_aux h hR hd hI

theorem a5_pick (h : Setup28 W K S) (hR : Red28 W K S) {I : Subgroup X} (hI : A5Frame W K S I) :
    ∃ p ∈ K, p ∉ zPre W K ∧ p ∈ CFSG.Quasithin.pResidualOf 2 I := A5Fr.a5_pick_aux h hR hI

end CaseThree

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
