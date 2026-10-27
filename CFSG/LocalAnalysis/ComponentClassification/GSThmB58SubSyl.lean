module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

namespace SubSylAux

theorem exists_sylow_of_relIndex {G : Type*} [Group G] [Finite G] {P D : Subgroup G}
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.relIndex D) :
    ∃ R : Sylow 2 ↥D, (R : Subgroup ↥D) = P.subgroupOf D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨(hP.comap_subtype (K := D)).toSylow hodd, rfl⟩

theorem secImage_sup_secB0 {Y : Subgroup X} (hY : Y ≤ h.secG0 y) :
    h.secImage y (Y ⊔ h.secB0 y) = h.secImage y Y := by
  show ((Y ⊔ h.secB0 y).subgroupOf (h.secG0 y)).map (h.secMk y) =
    (Y.subgroupOf (h.secG0 y)).map (h.secMk y)
  rw [subgroupOf_sup hY (h.secB0_le_G0 y), Subgroup.map_sup]
  have h1 : ((h.secB0 y).subgroupOf (h.secG0 y)).map (h.secMk y) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, Hyp52.ker_secMk]
  rw [h1, sup_bot_eq]

omit [Finite X] in
theorem mem_normalizer_sup {A C : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hC : g ∈ normalizer (C : Set X)) : g ∈ normalizer ((A ⊔ C : Subgroup X) : Set X) := by
  apply mem_normalizer_of_conjugate_eq
  show (A ⊔ C).map (MulAut.conj g⁻¹).toMonoidHom = A ⊔ C
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conjugate_eq_of_mem_normalizer hA) (conjugate_eq_of_mem_normalizer hC)

theorem mem_normalizer_of_secMk {Y : Subgroup X} (hBY : h.secB0 y ≤ Y) (hYG : Y ≤ h.secG0 y)
    {g : ↥(h.secG0 y)} (hg : h.secMk y g ∈ normalizer (h.secImage y Y : Set (h.secBar y))) :
    (g : X) ∈ normalizer (Y : Set X) := by
  rw [normalizer_secImage hBY hYG] at hg
  exact (secMk_mem_secImage_iff (hBY.trans le_normalizer) g).mp hg

theorem relIndex_secImage {A C : Subgroup X} (hBA : h.secB0 y ≤ A) (hAC : A ≤ C)
    (hCG : C ≤ h.secG0 y) : (h.secImage y A).relIndex (h.secImage y C) = A.relIndex C := by
  have hcA := card_secImage hBA (hAC.trans hCG)
  have hcC := card_secImage (hBA.trans hAC) hCG
  have e1 := Subgroup.card_mul_index ((h.secImage y A).subgroupOf (h.secImage y C))
  have e2 := Subgroup.card_mul_index (A.subgroupOf C)
  rw [Nat.card_congr (subgroupOfEquivOfLe (secImage_mono hAC)).toEquiv] at e1
  rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv] at e2
  have hpos : 0 < Nat.card (h.secImage y A) * Nat.card (h.secB0 y) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  show Nat.card (h.secImage y A) * Nat.card (h.secB0 y) *
      ((h.secImage y A).subgroupOf (h.secImage y C)).index =
    Nat.card (h.secImage y A) * Nat.card (h.secB0 y) * (A.subgroupOf C).index
  calc Nat.card (h.secImage y A) * Nat.card (h.secB0 y) *
        ((h.secImage y A).subgroupOf (h.secImage y C)).index
      = Nat.card (h.secImage y A) * ((h.secImage y A).subgroupOf (h.secImage y C)).index *
          Nat.card (h.secB0 y) := by ring
    _ = Nat.card C := by rw [e1, hcC]
    _ = Nat.card A * (A.subgroupOf C).index := e2.symm
    _ = Nat.card (h.secImage y A) * Nat.card (h.secB0 y) * (A.subgroupOf C).index := by
        rw [hcA]

theorem mem_secImage_secC0 (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hκ : ∀ l ∈ layerIn (centralizer (h.secB0 y : Set X)),
      l ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
      l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secB0 y → l * h.a = h.a * l)
    {q : h.secBar y} (hq : q ∈ h.secSubImg y) (hqa : q * hc.secA = hc.secA * q)
    (hqJ : q ∈ normalizer (h.secImage y (h.secJ0 y) : Set (h.secBar y))) :
    q ∈ h.secImage y (h.secC0 y) := by
  obtain ⟨g, hg, rfl⟩ := mem_map.mp hq
  have hgH : (g : X) ∈ h.secSub y := hg
  obtain ⟨l, hl, c, hcC, hlc⟩ := h.exists_mul_of_mem_secSub y hgH
  have h1 : g * ⟨h.a, hc.a_mem_G0⟩ * g⁻¹ * (⟨h.a, hc.a_mem_G0⟩ : ↥(h.secG0 y))⁻¹ ∈
      h.secB0' y := by
    rw [← ker_secMk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    change h.secMk y g * hc.secA * (h.secMk y g)⁻¹ * hc.secA⁻¹ = 1
    rw [hqa]
    group
  have hga : (g : X) * h.a * (g : X)⁻¹ * h.a⁻¹ ∈ h.secB0 y := h1
  have hca : c * h.a = h.a * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hcC).1
  have hla : l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secB0 y := by
    have e : (g : X) * h.a * (g : X)⁻¹ * h.a⁻¹ = l * h.a * l⁻¹ * h.a⁻¹ := by
      rw [← hlc, mul_assoc l c h.a, hca]
      group
    rwa [e] at hga
  have hJ0G : h.secJ0 y ≤ h.secG0 y := h.secJ0_le_G0 y
  have hJBG : h.secJ0 y ⊔ h.secB0 y ≤ h.secG0 y := sup_le hJ0G (h.secB0_le_G0 y)
  have hgN : (g : X) ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) := by
    rw [← SubSylAux.secImage_sup_secB0 hJ0G] at hqJ
    exact SubSylAux.mem_normalizer_of_secMk le_sup_right hJBG hqJ
  have hcG : c ∈ h.secG0 y := (mem_inf.mp hcC).2
  have hcN : c ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) :=
    SubSylAux.mem_normalizer_sup (mem_normalizer_secJ0 hcG (hCN (mem_inf.mp hcC).1)) hcG
  have hlN : l ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) := by
    have e : l = (g : X) * c⁻¹ := by
      rw [← hlc]
      group
    rw [e]
    exact mul_mem hgN (inv_mem hcN)
  have hlC : l ∈ h.secC0 y :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hκ l hl hlN hla), h.secL0_le_G0 y hl⟩
  have hgC : (g : X) ∈ h.secC0 y := by
    rw [← hlc]
    exact mul_mem hlC hcC
  exact mem_map_of_mem _ (show g ∈ (h.secC0 y).subgroupOf (h.secG0 y) from hgC)

theorem secImage_secC0_le (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X)) {q : h.secBar y}
    (hq : q ∈ h.secImage y (h.secC0 y)) :
    q ∈ h.secSubImg y ∧ q * hc.secA = hc.secA * q ∧
      q ∈ normalizer (h.secImage y (h.secJ0 y) : Set (h.secBar y)) := by
  refine ⟨secImage_mono (h.secC0_le_secSub y) hq, ?_⟩
  obtain ⟨c, hcC, rfl⟩ := mem_map.mp hq
  have hcC' : (c : X) ∈ h.secC0 y := hcC
  refine ⟨?_, secMk_mem_normalizer c.2 (mem_normalizer_secJ0 c.2 (hCN (mem_inf.mp hcC').1))⟩
  show h.secMk y c * h.secMk y ⟨h.a, hc.a_mem_G0⟩ = h.secMk y ⟨h.a, hc.a_mem_G0⟩ * h.secMk y c
  rw [← map_mul, ← map_mul]
  exact congrArg (h.secMk y) (Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp hcC').1))

theorem centralizer_inf_normalizer_eq (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hκ : ∀ l ∈ layerIn (centralizer (h.secB0 y : Set X)),
      l ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
      l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secB0 y → l * h.a = h.a * l) :
    centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (h.secImage y (h.secC0 y)).subgroupOf (h.secSubImg y) := by
  have hN : normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (normalizer (h.secImage y (h.secJ0 y) : Set (h.secBar y))).subgroupOf (h.secSubImg y) :=
    (subgroupOf_normalizer_eq (h.secImage_secJ0_le y)).symm
  ext z
  rw [mem_inf, hN, mem_centralizer_singleton_iff, mem_subgroupOf, mem_subgroupOf]
  constructor
  · rintro ⟨hza, hzJ⟩
    exact SubSylAux.mem_secImage_secC0 hc hCN hκ z.2 (congrArg Subtype.val hza) hzJ
  · intro hz
    obtain ⟨-, hza, hzJ⟩ := SubSylAux.secImage_secC0_le hc hCN hz
    exact ⟨Subtype.ext hza, hzJ⟩

end SubSylAux

theorem SecCond.subS_sylow (hc : h.SecCond y)
    (hB : Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y))
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hκ : ∀ l ∈ layerIn (centralizer (h.secB0 y : Set X)),
      l ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
      l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secB0 y → l * h.a = h.a * l) :
    ∃ R : Sylow 2 ↥(centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))),
      (R : Subgroup _) = (h.subS y).subgroupOf (centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (h.subS y) :=
    (((B5a.isPGroup_S h).comap_subtype (K := h.secG0 y)).map (h.secMk y)).comap_subtype
  have hBS : h.secB0 y ≤ h.S ⊓ h.secG0 y :=
    le_inf ((h.secB0_le_B y).trans (h.B_le.trans inf_le_left)) (h.secB0_le_G0 y)
  have hodd : ¬ 2 ∣ (h.subS y).relIndex (centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
      normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) := by
    rw [SubSylAux.centralizer_inf_normalizer_eq hc hCN hκ,
      Subgroup.relIndex_subgroupOf (secImage_mono (h.secC0_le_secSub y)), ← secImage_W_inf h.S,
      SubSylAux.relIndex_secImage hBS (h.S_inf_le_secC0 y) (h.secC0_le_G0 y)]
    obtain ⟨-, R, hR⟩ := hB
    have h1 := R.not_dvd_index
    rw [hR] at h1
    exact h1
  exact SubSylAux.exists_sylow_of_relIndex hS2 hodd

end Hyp52

end CFSG.ComponentClassification.GSThmB
