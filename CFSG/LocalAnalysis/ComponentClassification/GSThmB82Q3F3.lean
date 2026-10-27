module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight2

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

private theorem subQ_eq_one_of_mem_oddCore (h : Hyp52 X) (y : X) {o : X}
    (ho : o ∈ (pPrimeCore 2 ↥(Seven.Lay h y)).map (Seven.Lay h y).subtype)
    (hoH : o ∈ h.secSub y) : h.subQ y ⟨o, hoH⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := Seven.Lay h y with hL
  set O : Subgroup X := (pPrimeCore 2 ↥L).map L.subtype with hO
  have hOH : O ≤ h.secSub y := (map_subtype_le _).trans (h.secL0_le_secSub y)
  have hHN : h.secSub y ≤ normalizer (O : Set X) := fun g hg =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L)
      ((h.secSub_le_G0 y).trans (Seven.secG0_le_normalizer_Lay h y) hg)
  have hn : (O.subgroupOf (h.secSub y)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOH).mpr hHN
  have hn' : ((O.subgroupOf (h.secSub y)).map (h.subMk y)).Normal :=
    hn.map _ (h.subMk_surjective y)
  have hcop : Nat.Coprime 2 (Nat.card ((O.subgroupOf (h.secSub y)).map (h.subMk y))) := by
    have h1 := Subgroup.card_map_dvd (O.subgroupOf (h.secSub y)) (h.subMk y)
    rw [Nat.card_congr (subgroupOfEquivOfLe hOH).toEquiv, hO,
      card_map_of_injective L.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hle : (O.subgroupOf (h.secSub y)).map (h.subMk y) ≤ pPrimeCore 2 ↥(h.secSubImg y) :=
    le_sSup ⟨hn', hcop⟩
  show QuotientGroup.mk' _ (h.subMk y ⟨o, hoH⟩) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hle (mem_map_of_mem _ (mem_subgroupOf.mpr ho))

theorem mem_secB0_of_mem_coreActionKernel {w : X} {k : ℕ} (hw : w ^ 2 ^ k = 1)
    (hwC : w ∈ c.s.h.secC0 c.s.y) (hwL : w ∈ coreActionKernel (Seven.Lay c.s.h c.s.y)) :
    w ∈ c.s.h.secB0 c.s.y := by
  have hwH : w ∈ c.s.h.secSub c.s.y := c.s.h.secC0_le_secSub c.s.y hwC
  have hcent : c.s.h.subQ c.s.y ⟨w, hwH⟩ ∈
      centralizer (generalizedFitting (c.s.h.subQuot c.s.y) : Set (c.s.h.subQuot c.s.y)) := by
    rw [mem_centralizer_iff]
    intro f hf
    rw [← c.s.map_Lay_eq] at hf
    obtain ⟨l, hl, rfl⟩ := mem_map.mp hf
    have hlL : (l : X) ∈ Seven.Lay c.s.h c.s.y := mem_subgroupOf.mp hl
    have h1 := (mem_coreActionKernel.mp hwL).2 l hlL
    have h2 := subQ_eq_one_of_mem_oddCore c.s.h c.s.y h1
      (mul_mem (mul_mem (mul_mem (inv_mem l.2) (inv_mem hwH)) l.2) hwH)
    have e : (⟨(l : X)⁻¹ * w⁻¹ * l * w,
        mul_mem (mul_mem (mul_mem (inv_mem l.2) (inv_mem hwH)) l.2) hwH⟩ :
          ↥(c.s.h.secSub c.s.y)) = l⁻¹ * (⟨w, hwH⟩ : ↥(c.s.h.secSub c.s.y))⁻¹ * l * ⟨w, hwH⟩ :=
      rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc c.s.h.subQ c.s.y l * c.s.h.subQ c.s.y ⟨w, hwH⟩ =
        c.s.h.subQ c.s.y ⟨w, hwH⟩ * (c.s.h.subQ c.s.y l * ((c.s.h.subQ c.s.y l)⁻¹ *
          (c.s.h.subQ c.s.y ⟨w, hwH⟩)⁻¹ * c.s.h.subQ c.s.y l * c.s.h.subQ c.s.y ⟨w, hwH⟩)) := by
          group
      _ = c.s.h.subQ c.s.y ⟨w, hwH⟩ * c.s.h.subQ c.s.y l := by rw [h2, mul_one]
  rw [c.s.centralizer_eq, mem_bot] at hcent
  exact Hyp52.subQ_eq_one_of_two (w := ⟨w, hwH⟩) hw hcent

end CtxA0

end Eight2

end CFSG.ComponentClassification.GSThmB
