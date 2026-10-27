module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
public import CFSG.LocalAnalysis.GLTheoremA.PartI.BmaxCent
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G : Type} [Group G] [Finite G]

theorem closureIn_eq_bClosure (K B : Subgroup G) : closureIn K B = bClosure B K := by
  refine le_antisymm (iSup₂_le fun a ha => ?_) (iSup₂_le fun b hb => ?_)
  · have h : K.map (MulAut.conj a).toMonoidHom = GLBConj a⁻¹ K := by
      show K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj a⁻¹⁻¹).toMonoidHom
      rw [inv_inv]
    rw [h]
    exact le_iSup₂_of_le (f := fun (b : G) (_ : b ∈ B) => GLBConj b K) a⁻¹ (B.inv_mem ha) le_rfl
  · exact le_iSup₂_of_le (f := fun (a : G) (_ : a ∈ B) => K.map (MulAut.conj a).toMonoidHom) b⁻¹
      (B.inv_mem hb) le_rfl

theorem i1122IsoAt_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : I1122IsoAt G p := by
  intro B y K b hB hy hK hb hbn J hJ
  set X : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hBX : B ≤ X := le_centralizer_of_mem hB.1 hy.1
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B :=
    glaTwoLocalRank_le_pRank_of_isBmax hp hB X
  have hnK : ¬ B ≤ Subgroup.normalizer (K : Set G) := fun h => hbn (h hb)
  obtain ⟨-, h3, -, -⟩ := i112c_types T TL TT hsimple hKP hp hp2 hB.1 hBX hr hK hnK
  subst h3
  obtain ⟨hcomp, ⟨e⟩⟩ := i112c_layer_G T TL TT TM hsimple hKP hB.1 hBX hr hK hnK hb hbn
  rw [closureIn_eq_bClosure] at hJ
  have hJeq : J = GLAPLayer 3 (bClosure B K ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Lemma53Ns.glaPComponent_eq_of_le hp hJ hcomp (le_sSup hJ)
  subst hJeq
  exact ⟨e.trans (QuotientGroup.congr _ _ (quotEquivBarX hp hK.1 hK.2.1)
    (Subgroup.map_center_eq _)).symm⟩

end CFSG.LocalAnalysis.GLTheoremA
