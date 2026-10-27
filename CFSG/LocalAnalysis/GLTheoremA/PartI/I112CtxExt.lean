module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VExt

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem i112c_ext (T : Tables112) (TL : TableL2) (TT : Tables112Types) (TM : Tables112More)
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X B L : Subgroup G} (hB : IsElemAbelian p B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    X ≠ ⊤ ∧ p = 3 ∧ (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
      (∀ y ∈ B, y ∉ Subgroup.normalizer (L : Set G) →
        GLAPComponent 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))
            (GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ∧
          Nonempty (↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
            GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ≃*
            (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L)))) ∧
      (IsLTwoOddPow (barOf 3 L) ∨
        (IsElemAbelian 3 (barCenterX 3 X (bClosure B L)) ∧
          (Nat.card (barCenterX 3 X (bClosure B L)) = 3 ∨
            (Nat.card (barCenterX 3 X (bClosure B L)) = 9 ∧
              Nat.card ↥(barCenterX 3 X (bClosure B L) ⊓
                Subgroup.centralizer (barX 3 X B : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) = 3)) ∧
          ∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
            (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) →
              IsThreeOnePlusTwo R ∧ barCenterX 3 X R = barCenterX 3 X L)) := by
  obtain ⟨hXne, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ :=
    i112c_bar hsimple hKP hp hp2 hB hBX hr hL hnL
  obtain ⟨h3, hrel, -, hZE, -, hcase⟩ :=
    i112v_core T TL TT TM hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  have hJ : barX 3 X (bClosure B L) = i112J (barX 3 X B) (barX 3 X L) :=
    i112f_barX_bClosure hBX hL.1
  have hcen : barCenterX 3 X (bClosure B L) =
      i112J (barX 3 X B) (barX 3 X L) ⊓
        Subgroup.centralizer (i112J (barX 3 X B) (barX 3 X L) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rw [barCenterX, hJ, map_subtype_center]
    rfl
  refine ⟨hXne, rfl, (i112f_relIndex_barX hL hBX).symm.trans hrel,
    fun y hyB hyn => i112c_layer_G T TL TT TM hsimple hKP hB hBX hr hL hnL hyB hyn, ?_⟩
  rcases hcase with ⟨-, -, -, hL2⟩ | ⟨hZ3', ht5, hcZ⟩
  · exact Or.inl (i112f_isLTwoOddPow_of_mulEquiv e.symm hL2)
  · right
    refine ⟨by rw [hcen]; exact hZE, ?_, fun R hRL hR3 hRmax => ?_⟩
    · rw [hcen]
      rcases hcZ with h3' | ⟨h9, -, hC, -⟩
      · exact Or.inl h3'
      · exact Or.inr ⟨h9, hC⟩
    · exact i112v_ext_sylow TM hL (i116e_isQuasisimple hQcore hLbar) (isKGroup_of_le hQK _) hZ3'
        ht5 hRL hR3 hRmax

end CFSG.LocalAnalysis.GLTheoremA
