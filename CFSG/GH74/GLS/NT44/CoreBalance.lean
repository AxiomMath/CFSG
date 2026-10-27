module

public import CFSG.GH74.GLS.C3.Layer1.Th2Defs
import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZFStar
public import CFSG.GH74.GLS.TwoThin.Struct

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2.Bal

theorem isKBal_one_of_le_core_centralizers
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hcore : ∀ a ∈ A, a ≠ 1 →
      A ≤ (CFSG.Op_p'p 2 ↥(Subgroup.centralizer ({a} : Set G))).map
        ((Subgroup.centralizer ({a} : Set G)).subtype)) :
    CFSG.GH74.GLS.IsKBal 1 A := by
  intro D hD a ha ha1
  obtain ⟨hDA, hDel, hDrk⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer ({a} : Set G) with hH
  have hAH : A ≤ H := by
    intro x hx
    have hxmap : x ∈
        (CFSG.Op_p'p 2 ↥(Subgroup.centralizer ({a} : Set G))).map
          (Subgroup.centralizer ({a} : Set G)).subtype :=
      (hcore a ha ha1) hx
    obtain ⟨u, -, hu⟩ := hxmap
    rw [← hu]
    simp [hH]
  have hDH : D ≤ Subgroup.centralizer ({a} : Set G) := by
    simpa [hH] using hDA.trans hAH
  have hDsq : ∀ d ∈ D, d * d = 1 :=
    (CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hDel).2
  have hDk : 2 ^ 1 ≤ Nat.card D := by
    rw [CFSG.GH74.GLS.C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    exact Nat.pow_le_pow_right (by norm_num) hDrk
  by_contra hnle
  obtain ⟨c, hc, hcn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  set Y : Subgroup G := AG D ⊓ H
  have hY : ∀ d ∈ D, d ≠ 1 →
      Y ≤ pPrimeCoreOf 2 (Subgroup.centralizer ({d} : Set G)) := by
    intro d hd hd1
    exact inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
  have hN1 : (Y.subgroupOf (Subgroup.centralizer ({a} : Set G))).map (piBar a) ≠ ⊥ := by
    intro h
    apply hcn
    have hmem : piBar a ⟨c, hc.2⟩ ∈
        (Y.subgroupOf (Subgroup.centralizer ({a} : Set G))).map (piBar a) :=
      ⟨⟨c, hc.2⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
    rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
    exact ⟨⟨c, hc.2⟩, hmem, rfl⟩
  set F : Subgroup (CFSG.GH74.CentralizerBar a) :=
    (D.subgroupOf (Subgroup.centralizer ({a} : Set G))).map (piBar a) with hF
  have hFk : 2 ^ 1 ≤ Nat.card F := by
    rw [hF, card_map_piBar hDsq hDH]
    exact hDk
  have hk1 : 1 ≤ (1 : ℕ) := by norm_num
  obtain ⟨f, hfF, hfne⟩ := exists_ne_one_of_two_pow_le hk1 hFk
  have hFp : F ≤ CFSG.pCore 2 (CFSG.GH74.CentralizerBar a) := by
    intro f hf
    obtain ⟨d0, hd0, rfl⟩ := hf
    have hdD : (d0 : G) ∈ D := Subgroup.mem_subgroupOf.mp hd0
    have hdA : (d0 : G) ∈ A := hDA hdD
    have hxmap : (d0 : G) ∈
        (CFSG.Op_p'p 2 ↥(Subgroup.centralizer ({a} : Set G))).map
          (Subgroup.centralizer ({a} : Set G)).subtype :=
      (hcore a ha ha1) hdA
    obtain ⟨u, huOp, huval⟩ := hxmap
    have hu_eq : u = d0 := Subtype.ext huval
    rw [← hu_eq]
    change CFSG.GH74.GLS.TwoThin.barMk ↥(Subgroup.centralizer ({a} : Set G)) u ∈
      CFSG.pCore 2 (CFSG.GH74.GLS.TwoThin.barQ ↥(Subgroup.centralizer ({a} : Set G)))
    simpa [CFSG.Op_p'p, CFSG.GH74.GLS.TwoThin.barMk,
      CFSG.GH74.GLS.TwoThin.barQ] using huOp
  obtain ⟨L, hL, -, hfaith, -, -, -⟩ :=
    exists_component_of_image hk1 hDH hDk hDsq hY (le_refl _) hN1
  have hLcent : CFSG.pCore 2 (CFSG.GH74.CentralizerBar a) ≤
      Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.pCore_le_centralizer_of_isComponent
      (p := 2) hL
  refine hfaith f ?_ hfne ?_
  · simpa [hF] using hfF
  · intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hLcent (hFp hfF)) x hx).symm

end CFSG.GH74.GLS.NT44

end
