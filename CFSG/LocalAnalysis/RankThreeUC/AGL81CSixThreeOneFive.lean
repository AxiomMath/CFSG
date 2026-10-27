module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSympDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReduce
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneModel
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSympBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneIsotropic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSplit
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneQuasisimple
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneLinearFive
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneThree
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup
open scoped Matrix MatrixGroups

private theorem sixThreeOneList_of_irreducible_not_quasisimple {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hC2 : SympIrredNotQuasisimpleAt p) {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W] (hW : Module.finrank (ZMod p) W = 4)
    (B : LinearMap.BilinForm (ZMod p) W) (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0)
    (hBalt : ∀ w : W, B w w = 0) {H : Subgroup (Module.End (ZMod p) W)ˣ}
    (hH : oPPrimeHull p H = H)
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    (hirr : ∀ U : Submodule (ZMod p) W,
      (∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnq : ¬ CFSG.IsQuasisimple ↥H) :
    SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H) := by
  classical
  haveI : Finite W := Module.finite_of_finite (ZMod p)
  obtain ⟨c, τ, -, hτc, hSp⟩ := exists_symplecticCoordinates hW B hBnd hBalt
  let G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p)) := H.map τ.toMonoidHom
  have hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact (hSp y).mpr (hiso y hy)
  have hGgen : oPPrimeHull p G = G := oPPrimeHull_map_eq τ.toMonoidHom hH
  have hGirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G :=
    (isIrreducibleOn_map_iff c τ hτc H).mpr hirr
  have hHG : ↥H ≃* ↥G := Subgroup.equivMapOfInjective H τ.toMonoidHom τ.injective
  have hGnotq : ¬ CFSG.IsQuasisimple ↥G := fun hqG =>
    hnq (CFSG.IsQuasisimple.of_mulEquiv hHG hqG)
  obtain ⟨hp5eq, hext⟩ := hC2 hp5 G hGS hGgen hGirr hGnotq
  have hpc : CFSG.pCore p ↥H = ⊥ := pCore_eq_bot_of_irreducible hirr
  let eY : (↥H ⧸ CFSG.pCore p ↥H) ≃* ↥G :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans (QuotientGroup.quotientBot.trans hHG)
  have hbase : SixThreeOneList p ↥G :=
    Or.inr (Or.inr (Or.inl ⟨hp5eq, Or.inr hext⟩))
  exact SixThreeOneList.of_mulEquiv eY.symm hbase

private theorem sixThreeOneList_or_hasIsotropicPlaneGroup_of_reducible {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] (hW : Module.finrank (ZMod p) W = 4)
    (B : LinearMap.BilinForm (ZMod p) W) (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0)
    (hBalt : ∀ w : W, B w w = 0) {H : Subgroup (Module.End (ZMod p) W)ˣ}
    (hH : oPPrimeHull p H = H)
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    (hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ →
      (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
      ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    {U : Submodule (ZMod p) W} (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤)
    (hUH : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U) :
    SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H) ∨ HasIsotropicPlaneGroup p B H := by
  obtain ⟨U₁, U₂, hU, hU₁, hU₂, hB12, hHU₁, hHU₂⟩ :=
    exists_orthogonal_planes_of_reducible hW B hBnd hBalt hiso hU0 hU1 hUH hno
  exact sixThreeOneList_or_hasIsotropicPlaneGroup_of_planes hp5 B hBalt hH hU hU₁ hU₂ hB12
    hHU₁ hHU₂ hno

section


private theorem sixThreeOneList_or_hasIsotropicPlaneGroup_of_irreducible {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hC2 : SympIrredNotQuasisimpleAt p) {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W] (hW : Module.finrank (ZMod p) W = 4)
    (B : LinearMap.BilinForm (ZMod p) W) (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0)
    (hBalt : ∀ w : W, B w w = 0) {H : Subgroup (Module.End (ZMod p) W)ˣ}
    (hH : oPPrimeHull p H = H)
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    (hirr : ∀ U : Submodule (ZMod p) W,
      (∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U) → U = ⊥ ∨ U = ⊤) :
    SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H) ∨ HasIsotropicPlaneGroup p B H := by
  by_cases hq : CFSG.IsQuasisimple ↥H
  · rcases sixThreeOneList_or_isotropic_of_quasisimple hp5 hW B hBnd hBalt hH hiso hirr hq
      with hlist | hplane | hfull
    · exact Or.inl hlist
    · exact Or.inr hplane
    · exact Or.inr (hasIsotropicPlaneGroup_of_forall_isometry_mem hW B hBnd hBalt hfull)
  · exact Or.inl
      (sixThreeOneList_of_irreducible_not_quasisimple hp5 hC2 hW B hBnd hBalt hH hiso hirr hq)

theorem sympSplitAt_of_five_le {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hC2 : SympIrredNotQuasisimpleAt p) : SympSplitAt p := by
  classical
  intro W _ _ _ hW B hBnd hBalt H hH hsim
  have hp2 : p ≠ 2 := by omega
  have hBne : B ≠ 0 := by
    intro hB0
    have hpos : 0 < Module.finrank (ZMod p) W := by omega
    haveI : Nontrivial W := Module.finrank_pos_iff.mp hpos
    obtain ⟨u, hu⟩ := exists_ne (0 : W)
    exact hu (by simpa [hB0] using hBnd u (fun v => by simp [hB0]))
  have hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v :=
    isometry_of_mem_of_oPPrimeHull hBne hH hsim
  by_cases hisoSub : ∃ T : Submodule (ZMod p) W, T ≠ ⊥ ∧
      (∀ u ∈ T, ∀ v ∈ T, B u v = 0) ∧
      ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T
  · obtain ⟨T, hT0, hTB, hTH⟩ := hisoSub
    rcases sl2_or_trivial_of_isotropic_invariant hp2 hW B hBnd hBalt hH hiso hT0 hTB hTH with
      h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))
  · have hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ →
        (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
        ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T := by
      intro T hT0 hTB hTH
      exact hisoSub ⟨T, hT0, hTB, hTH⟩
    by_cases hred : ∃ U : Submodule (ZMod p) W, U ≠ ⊥ ∧ U ≠ ⊤ ∧
        ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U
    · obtain ⟨U, hU0, hU1, hUH⟩ := hred
      exact sixThreeOneList_or_hasIsotropicPlaneGroup_of_reducible hp5 hW B hBnd hBalt hH
        hiso hno hU0 hU1 hUH
    · have hirr : ∀ U : Submodule (ZMod p) W,
          (∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U) → U = ⊥ ∨ U = ⊤ := by
        intro U hU
        by_cases hU0 : U = ⊥
        · exact Or.inl hU0
        · exact Or.inr (by
            by_contra hU1
            exact hred ⟨U, hU0, hU1, hU⟩)
      exact sixThreeOneList_or_hasIsotropicPlaneGroup_of_irreducible hp5 hC2 hW B hBnd hBalt
        hH hiso hirr

end

section


theorem sixThreeOneAt_of_five_le {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hC2 : SympIrredNotQuasisimpleAt p) : SixThreeOneAt p :=
  sixThreeOneAt_of_split (Fact.out : p.Prime) (by omega) (linearListAt_of_five_le hp5)
    (sympSplitAt_of_five_le hp5 hC2)

end

section


theorem sixThreeOne_of_sympIrredNotQuasisimple
    (hC2 : ∀ (p : ℕ) [Fact p.Prime], SympIrredNotQuasisimpleAt p) : SixThreeOne := by
  refine sixThreeOne_of_forall fun p hp hp2 => ?_
  by_cases hp3 : p = 3
  · subst hp3
    exact sixThreeOneAt_three
  · haveI : Fact p.Prime := ⟨hp⟩
    have hp5 : 5 ≤ p := by
      have h2 : 2 ≤ p := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by decide)
      omega
    exact sixThreeOneAt_of_five_le hp5 (hC2 p)

end

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
