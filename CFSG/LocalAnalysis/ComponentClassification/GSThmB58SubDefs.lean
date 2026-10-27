module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Steps
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecSyl

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement Pointwise

namespace Sub58

variable {X : Type} [Group X] [Finite X]

theorem layerIn_centralizer_le_of_le {B₀ E : Subgroup X} (hE : IsPGroup 2 E) (hBE : B₀ ≤ E)
    (hEN : E ≤ normalizer (B₀ : Set X)) :
    layerIn (centralizer (E : Set X)) ≤ layerIn (centralizer (B₀ : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (B₀ : Set X) with hC
  set Y := C ⊔ E with hY
  have hCY : C ≤ Y := le_sup_left
  have hEY : E ≤ Y := le_sup_right
  have hCE : centralizer (E : Set X) ≤ C := centralizer_le (SetLike.coe_subset_coe.mpr hBE)
  have hEnC : E ≤ normalizer (C : Set X) := fun e he => B5a.mem_normalizer_centralizer (hEN he)
  have hA : IsPGroup 2 (E.subgroupOf Y) := hE.comap_subtype
  have h1 := ClassicalInvolution.l2PrimeBalance ↥Y (E.subgroupOf Y) hA
  have h2 : layerIn ((centralizer (E : Set X)).subgroupOf Y) ≤ pLayer ↥Y 2 := by
    rw [← B5a.centralizer_subgroupOf hEY]
    exact h1
  rw [B5a.layerIn_subgroupOf (hCE.trans hCY)] at h2
  have h3 : layerIn (centralizer (E : Set X)) ≤ layerIn Y := by
    intro x hx
    have hxY : x ∈ Y := ((map_subtype_le _).trans (hCE.trans hCY)) hx
    exact ⟨⟨x, hxY⟩, h2 (show (⟨x, hxY⟩ : ↥Y) ∈
      (layerIn (centralizer (E : Set X))).subgroupOf Y from hx), rfl⟩
  have : (C.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCY).mpr (sup_le le_normalizer hEnC)
  have : Group.IsNilpotent ↥E := hE.isNilpotent
  have hEs : Group.IsSolvable ↥E := inferInstance
  have h4 : CFSG.Open.lBalancePLayer 2 Y ≤ CFSG.Open.lBalancePLayer 2 C :=
    LBalance.Asm.pLayer_le_of_pComponents_le 2 C Y hCY fun L hL => by
      have : Group.IsPerfect L := LBalance.pComponent_perfect 2 _ L hL
      exact B5a.perfect_le_of_le_sup hEnC hEs (LBalance.subnormal_le hL.1)
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h4
  exact h3.trans h4

theorem le_layerIn_centralizer_of_isPComponent {B₀ E L : Subgroup X} (hE : IsPGroup 2 E)
    (hBE : B₀ ≤ E) (hEN : E ≤ normalizer (B₀ : Set X)) (hLN : L ≤ normalizer (E : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (normalizer (E : Set X)))) :
    L ≤ layerIn (centralizer (B₀ : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) E hE
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
  have h2 : L ≤ (pLayer ↥(normalizer (E : Set X)) 2).map (normalizer (E : Set X)).subtype := by
    have h3 := map_mono (f := (normalizer (E : Set X)).subtype)
      (show L.subgroupOf (normalizer (E : Set X)) ≤ pLayer _ 2 from le_sSup hL)
    rwa [map_subgroupOf_eq_of_le hLN] at h3
  exact (h2.trans h1).trans (layerIn_centralizer_le_of_le hE hBE hEN)

end Sub58

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

variable (h : Hyp52 X) (y : X)

abbrev secL0 : Subgroup X := layerIn (centralizer (h.secB0 y : Set X))

abbrev secC0 : Subgroup X := centralizer ({h.a} : Set X) ⊓ h.secG0 y

abbrev secSub : Subgroup X :=
  layerIn (centralizer (h.secB0 y : Set X)) ⊔ (centralizer ({h.a} : Set X) ⊓ h.secG0 y)

abbrev secSubImg : Subgroup (h.secBar y) := h.secImage y (h.secSub y)

abbrev subJ : Subgroup ↥(h.secSubImg y) := (h.secImage y (h.secJ0 y)).subgroupOf (h.secSubImg y)

abbrev subS : Subgroup ↥(h.secSubImg y) := (h.secImage y h.S).subgroupOf (h.secSubImg y)

abbrev subB : Subgroup ↥(h.secSubImg y) := (h.secImage y h.B).subgroupOf (h.secSubImg y)

abbrev subK : Subgroup ↥(h.secSubImg y) := (h.secImage y h.K).subgroupOf (h.secSubImg y)

theorem secL0_le_centralizer : h.secL0 y ≤ centralizer (h.secB0 y : Set X) := map_subtype_le _

theorem secL0_le_G0 : h.secL0 y ≤ h.secG0 y :=
  (h.secL0_le_centralizer y).trans (h.centralizer_le_G0 y)

theorem secC0_le_G0 : h.secC0 y ≤ h.secG0 y := inf_le_right

theorem secL0_le_secSub : h.secL0 y ≤ h.secSub y := le_sup_left

theorem secC0_le_secSub : h.secC0 y ≤ h.secSub y := le_sup_right

theorem secSub_le_G0 : h.secSub y ≤ h.secG0 y := sup_le (h.secL0_le_G0 y) (h.secC0_le_G0 y)

theorem G0_le_normalizer_secL0 : h.secG0 y ≤ normalizer (h.secL0 y : Set X) :=
  Seven.normalizer_le_normalizer_layerIn_centralizer (h.secB0 y)

theorem exists_mul_of_mem_secSub {g : X} (hg : g ∈ h.secSub y) :
    ∃ l ∈ h.secL0 y, ∃ c ∈ h.secC0 y, l * c = g := by
  have h1 : ((h.secSub y : Subgroup X) : Set X) = (h.secL0 y : Set X) * (h.secC0 y : Set X) :=
    coe_mul_of_right_le_normalizer_left _ _ ((h.secC0_le_G0 y).trans (h.G0_le_normalizer_secL0 y))
  have h2 : g ∈ ((h.secSub y : Subgroup X) : Set X) := hg
  rw [h1] at h2
  obtain ⟨l, hl, c, hc, hlc⟩ := h2
  exact ⟨l, hl, c, hc, hlc⟩

theorem secB0_le_secC0 : h.secB0 y ≤ h.secC0 y :=
  le_inf ((h.secB0_le_B y).trans (h.B_le.trans (inf_le_left.trans (h.S_le.trans inf_le_left))))
    (h.secB0_le_G0 y)

theorem secB0_le_secSub : h.secB0 y ≤ h.secSub y := (h.secB0_le_secC0 y).trans (h.secC0_le_secSub y)

theorem S_inf_le_secC0 : h.S ⊓ h.secG0 y ≤ h.secC0 y :=
  inf_le_inf_right _ (h.S_le.trans inf_le_left)

theorem secJ0_le_secC0 : h.secJ0 y ≤ h.secC0 y :=
  le_inf ((h.secJ0_le y).trans inf_le_left) (h.secJ0_le_G0 y)

theorem secJ0_le_secSub : h.secJ0 y ≤ h.secSub y := (h.secJ0_le_secC0 y).trans (h.secC0_le_secSub y)

theorem secImage_secJ0_le : h.secImage y (h.secJ0 y) ≤ h.secSubImg y :=
  secImage_mono (h.secJ0_le_secSub y)

theorem secImage_S_le : h.secImage y h.S ≤ h.secSubImg y := by
  rw [← secImage_W_inf]
  exact secImage_mono (h.S_inf_le_secC0 y |>.trans (h.secC0_le_secSub y))

theorem secImage_B_le : h.secImage y h.B ≤ h.secSubImg y :=
  (secImage_mono (h.B_le.trans inf_le_left)).trans (h.secImage_S_le y)

variable {h y}

theorem V_le_secL0 (hc : h.SecCond y) : h.V ≤ h.secL0 y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) h.B (B5a.isPGroup_B h)
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
  exact h1.trans (Sub58.layerIn_centralizer_le_of_le (B5a.isPGroup_B h) (h.secB0_le_B y)
    hc.B_le_G0)

theorem V_le_secSub (hc : h.SecCond y) : h.V ≤ h.secSub y :=
  (V_le_secL0 hc).trans (h.secL0_le_secSub y)

theorem K_le_secSub (hc : h.SecCond y) : h.K ≤ h.secSub y := K_le_V.trans (V_le_secSub hc)

theorem conjugate_K_le_secSub (hc : h.SecCond y) : conjugate h.K h.a ≤ h.secSub y :=
  conjugate_K_le_V.trans (V_le_secSub hc)

theorem secImage_V_le (hc : h.SecCond y) : h.secImage y h.V ≤ h.secSubImg y :=
  secImage_mono (V_le_secSub hc)

theorem secImage_K_le (hc : h.SecCond y) : h.secImage y h.K ≤ h.secSubImg y :=
  secImage_mono (K_le_secSub hc)

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem a_mem_secC0 : h.a ∈ h.secC0 y :=
  mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, hc.a_mem_G0⟩

theorem y_mem_secC0 : y ∈ h.secC0 y :=
  mem_inf.mpr ⟨(mem_inf.mp (h.S_le hc.mem_S)).1, hc.y_mem_G0⟩

theorem a_mem_secSub : h.a ∈ h.secSub y := h.secC0_le_secSub y hc.a_mem_secC0

theorem y_mem_secSub : y ∈ h.secSub y := h.secC0_le_secSub y hc.y_mem_secC0

theorem Q_le_secC0 : h.Q ≤ h.secC0 y :=
  le_inf (inf_le_left.trans (h.S_le.trans inf_le_left)) hc.Q_le

theorem B_le_secSub : h.B ≤ h.secSub y :=
  (h.B_le_Q.trans hc.Q_le_secC0).trans (h.secC0_le_secSub y)

theorem secA_mem_secSubImg : hc.secA ∈ h.secSubImg y :=
  mem_map_of_mem _ (show (⟨h.a, hc.a_mem_G0⟩ : ↥(h.secG0 y)) ∈
    (h.secSub y).subgroupOf (h.secG0 y) from hc.a_mem_secSub)

theorem secX_mem_secSubImg : hc.secX ∈ h.secSubImg y :=
  mem_map_of_mem _ (show (⟨y, hc.y_mem_G0⟩ : ↥(h.secG0 y)) ∈
    (h.secSub y).subgroupOf (h.secG0 y) from hc.y_mem_secSub)

abbrev subA : ↥(h.secSubImg y) := ⟨hc.secA, hc.secA_mem_secSubImg⟩

abbrev subX : ↥(h.secSubImg y) := ⟨hc.secX, hc.secX_mem_secSubImg⟩

end SecCond

theorem normalizer_subB : normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
    Set ↥(h.secSubImg y)) =
      (normalizer (h.secImage y h.B : Set (h.secBar y))).subgroupOf (h.secSubImg y) :=
  (subgroupOf_normalizer_eq (h.secImage_B_le y)).symm

theorem SecCond.subA_mem_normalizer (hc : h.SecCond y) :
    hc.subA ∈ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) := by
  rw [normalizer_subB]
  exact hc.secA_mem_normalizer

theorem SecCond.isPComponent_subL (hc : h.SecCond y) {L : Subgroup X}
    (hL : L = h.K ∨ L = conjugate h.K h.a) :
    (h.secImage y L).subgroupOf (h.secSubImg y) ≤
        normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) ∧
      IsPComponent 2 (((h.secImage y L).subgroupOf (h.secSubImg y)).subgroupOf
        (normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLW, hLc⟩ := isPComponent_secK hc hL
  have hLH : h.secImage y L ≤ h.secSubImg y := by
    rcases hL with rfl | rfl
    · exact secImage_K_le hc
    · exact secImage_mono (conjugate_K_le_secSub hc)
  have h1 : IsPComponent 2 ((h.secImage y L).subgroupOf
      (normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓ h.secSubImg y)) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLW hLH) inf_le_left hLc
  rw [← isPComponent_subgroupOf_subgroupOf_iff' (inf_le_right : normalizer
    (h.secImage y h.B : Set (h.secBar y)) ⊓ h.secSubImg y ≤ h.secSubImg y) 2 Nat.prime_two,
    inf_subgroupOf_right] at h1
  rw [normalizer_subB]
  exact ⟨fun z hz => hLW hz, h1⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
