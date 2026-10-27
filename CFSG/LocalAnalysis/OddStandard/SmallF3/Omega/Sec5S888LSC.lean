module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem l515S_normal_subgroupOf {E H : Subgroup G}
    (h : ∀ g ∈ H, CFSG.conjugate E g = E) : (E.subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : CFSG.conjugate E (g : G) = E := h (g : G) g.2
  have hn' : (n : G) ∈ CFSG.conjugate E (g : G) := by rw [hg]; exact hn
  rw [sec5b_mem_conjugate_iff] at hn'
  simpa using hn'

section Half

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_layerCent_conj (h52a : Asc82Lemma52a) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {d g : G} (hgt : g ∈ centralizer ({t} : Set G)) (hgd : g ∈ centralizer ({d} : Set G)) :
    CFSG.conjugate (layerCent L d) g = layerCent L d := by
  have hL : CFSG.conjugate L g = L := sec5_conj_L h52a c hgt
  have hC : CFSG.conjugate (centralizer ({d} : Set G)) g = centralizer ({d} : Set G) :=
    sec5b513_conjugate_eq_iff.mpr (Subgroup.le_normalizer hgd)
  unfold layerCent
  rw [← sec5b517_inSubgroup_layer_conjugate, sec5b517_conjugate_inf, hL, hC]

theorem l515S_isComponentIn_layerCent (h52a : Asc82Lemma52a)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hq : IsQuasisimple (layerCent L d)) :
    IsComponentIn (layerCent L d) (centralizer ({t, d} : Set G)) := by
  have hle : layerCent L d ≤ centralizer ({t, d} : Set G) := by
    rw [centralizer_pair_eq_inf]
    have h0 : layerCent L d ≤ L ⊓ centralizer ({d} : Set G) := inSubgroup_le _ _
    exact le_inf (h0.trans (inf_le_left.trans c.component.le)) (h0.trans inf_le_right)
  refine isComponentIn_of_normal hle hq (l515S_normal_subgroupOf fun g hg => ?_)
  rw [centralizer_pair_eq_inf] at hg
  exact l515S_layerCent_conj h52a c hg.1 hg.2

theorem l515S_half (h52a : Asc82Lemma52a) (hM1 : Asc82FactRhoStar)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {P₁ P₂ : Subgroup G}
    (hP : (P₁ = K₁ ∧ P₂ = K₂) ∨ (P₁ = K₂ ∧ P₂ = K₁)) {q w : G} (hq : q ∈ P₁)
    (hq2 : q * q = z) (hw2 : w * w = z) (hwt : w * t = t * w)
    (hwK : K₁ ⊔ K₂ ≤ centralizer ({w} : Set G)) :
    LieModel ↥(layerCent L (q * w)) .PSU 3 3 1 ∧ P₂ ≤ layerCent L (q * w) ∧
      IsComponentIn (layerCent L (q * w)) (centralizer ({t, q * w} : Set G)) := by
  have hΩ : IsOm6Z2 L := c.toSec5Setting.isOm6Z2
  have hodd : oddCoreIn L = ⊥ := sec5b517_oddCore_bot c
  have hwt' : w ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hwt
  have hwL : w ∈ normalizer (L : Set G) :=
    sec5b513_conjugate_eq_iff.mp (sec5_conj_L h52a c hwt')
  have hq4 : orderOf q = 4 := l515S_orderOf_eq_four hq2 c.z_mul_self c.z_ne_one
  have hz2 : orderOf z = 2 := l515S_orderOf_eq_two c.z_mul_self c.z_ne_one
  have hwy : ∀ y ∈ L, (w * w) * y * (w * w)⁻¹ = z * y * z⁻¹ := by
    intro y _
    rw [hw2]
  have hM : LieModel ↥(layerCent L (q * w)) .PSU 3 3 1 ∧ P₂ ≤ layerCent L (q * w) := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hq
      rw [h2]
      exact hM1 G t L z K₁ K₂ hz2 hΩ hodd c.centre c.pocket₁ c.pocket₂ c.ne c.comm c.prod q hq
        hq4 w hwL hwK hwy
    · rw [h1] at hq
      rw [h2]
      have hcomm' : ⁅K₂, K₁⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact c.comm
      exact hM1 G t L z K₂ K₁ hz2 hΩ hodd c.centre c.pocket₂ c.pocket₁ c.ne.symm hcomm'
        (by rw [sup_comm]; exact c.prod) q hq hq4 w hwL (by rw [sup_comm]; exact hwK) hwy
  exact ⟨hM.1, hM.2,
    l515S_isComponentIn_layerCent h52a c (l515S_isQuasisimple_of_u33 hM.1)⟩

end Half

end CFSG.OddStandard.SmallF3.Omega
