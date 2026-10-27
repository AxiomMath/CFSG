module

public import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
public import CFSG.GH74.GLS.Balance.Bender.Final
public import CFSG.GH74.GLS.Bg.Pu5.BalStatements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Bg.Iii2 CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem bl0_of : BL0S := by
  intro G _ _ _ a b ha _ hab H hH y _ hyz l hl
  have hba : a ∈ centralizer ({b} : Set G) := TwoThin.mem_centralizer_symm hab
  have hHL : pLayerOf 2 (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) ≤
      pLayerOf 2 (centralizer ({b} : Set G)) :=
    sSup_le fun Λ hΛ => le_pLayerOf_of_isPCompIn_inf ha hba hΛ
  exact commutator_mem_pPrimeCoreOf_of_forall_mem_cSec
    (fun M hM => mem_cSec_of_mem_zStar_rigidProduct hyz hM) l (hHL (hH hl))

section Solv

variable {G : Type} [Group G] [Finite G]

theorem isSolvTwoCompSL23In_subgroupOf {a b : G} (hba : a ∈ centralizer ({b} : Set G)) {V : Subgroup G}
    (hV : Balance.IsSolvTwoCompSL23In (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) V) :
    Balance.IsSolvTwoCompSL23In
      (centralizer ({(⟨a, hba⟩ : ↥(centralizer ({b} : Set G)))} : Set ↥(centralizer ({b} : Set G))))
      (V.subgroupOf (centralizer ({b} : Set G))) := by
  set Cb : Subgroup G := centralizer ({b} : Set G) with hCb
  set a' : ↥Cb := ⟨a, hba⟩ with ha'
  set W : Subgroup G := centralizer ({a} : Set G) ⊓ Cb with hW
  have hmem : ∀ g : ↥W, (⟨(g : G), (Subgroup.mem_inf.mp g.2).2⟩ : ↥Cb) ∈ centralizer ({a'} : Set ↥Cb) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).1)
  let f : ↥W →* ↥(centralizer ({a'} : Set ↥Cb)) :=
    { toFun := fun g => ⟨⟨(g : G), (Subgroup.mem_inf.mp g.2).2⟩, hmem g⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hfinj : Function.Injective f := by
    intro g h hgh
    exact Subtype.ext (congrArg (fun z : ↥(centralizer ({a'} : Set ↥Cb)) => ((z : ↥Cb) : G)) hgh)
  have hfsurj : Function.Surjective f := by
    rintro ⟨⟨g, hgb⟩, hg⟩
    have hga : g ∈ centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
    exact ⟨⟨g, Subgroup.mem_inf.mpr ⟨hga, hgb⟩⟩, rfl⟩
  have hodd : Odd (Nat.card f.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr hfinj, Subgroup.card_bot]
    exact odd_one
  refine ⟨?_, ?_⟩
  · intro v hv
    have hvW : (v : G) ∈ W := hV.1 (Subgroup.mem_subgroupOf.mp hv)
    exact hmem ⟨(v : G), hvW⟩
  · have h := Balance.isSolvTwoCompSL23_map f hfsurj hodd hV.2
    have heq : (V.subgroupOf W).map f = (V.subgroupOf Cb).subgroupOf (centralizer ({a'} : Set ↥Cb)) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        obtain ⟨⟨g, hgb⟩, hg⟩ := z
        have hga : g ∈ centralizer ({a} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
        exact ⟨⟨g, Subgroup.mem_inf.mpr ⟨hga, hgb⟩⟩, hz, rfl⟩
    rwa [heq] at h

theorem bl0s_of : BL0sS := by
  intro G _ _ _ a b ha _ hab V hV y _ hyz v hv
  have hba : a ∈ centralizer ({b} : Set G) := TwoThin.mem_centralizer_symm hab
  set Cb : Subgroup G := centralizer ({b} : Set G) with hCb
  have hV' := isSolvTwoCompSL23In_subgroupOf hba hV
  have ha' : orderOf (⟨a, hba⟩ : ↥Cb) = 2 := TwoThin.orderOf_mk_centralizer hba ha
  have hvV : v ∈ V := Balance.oPrimeResidualOf_le_self V hv
  have hvb : v ∈ Cb := (Subgroup.mem_inf.mp (hV.1 hvV)).2
  have hres : oPrimeResidualOf 2 V ≤ (oPrimeResidualOf 2 (V.subgroupOf Cb)).map Cb.subtype := by
    refine Balance.oPrimeResidualOf_le_of_two_elements fun w hw h2 => ?_
    have hwb : w ∈ Cb := (Subgroup.mem_inf.mp (hV.1 hw)).2
    refine ⟨⟨w, hwb⟩, Balance.mem_oPrimeResidualOf_of_two_element (Subgroup.mem_subgroupOf.mpr hw) ?_, rfl⟩
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨v', hv', hv'v⟩ := hres hv
  have hyL : y ∈ pLayerOf 2 Cb := rigidProduct_le_pLayerOf b hyz.1
  rcases Balance.solvableL2PrimeBalance_proved ↥Cb ⟨a, hba⟩ ha' _ hV' with h1 | ⟨L, hL, -, hRL⟩
  ·
    have hvO : v ∈ O22 Cb := ⟨v', h1 hv', hv'v⟩
    have h2 := commutator_mem_pPrimeCoreOf_of_forall_mem_cSec (y := v)
      (fun M hM => O22_le_cSec hM hvO) y hyL
    have h3 : ⁅v, y⁆ = (⁅y, v⁆)⁻¹ := (commutatorElement_inv y v).symm
    rw [h3]
    exact inv_mem h2
  ·
    have hM : IsPCompIn 2 Cb (L.map Cb.subtype) := by
      refine ⟨Subgroup.map_subtype_le _, ?_⟩
      have e : (L.map Cb.subtype).subgroupOf Cb = L :=
        Subgroup.comap_map_eq_self_of_injective Cb.subtype_injective L
      rw [e]
      exact hL
    have hvM : v ∈ L.map Cb.subtype := ⟨v', hRL hv', hv'v⟩
    exact pPrimeCoreOf_le_of_isPCompIn hM ((mem_cSec_of_mem_zStar_rigidProduct hyz hM).2.2 v hvM)

end Solv

end CFSG.GH74.GLS.Bg.Pu5
