module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusSec
public import CFSG.ClassicalInvolution.AschTight.S19QAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped commutatorElement

section Odd

variable {G : Type} [Group G] [Finite G]

@[expose] def oddPart3 (K C : Subgroup G) : Subgroup ↥(conjGen (secL K C)) :=
  (secL K C).subgroupOf (conjGen (secL K C)) ⊓
    (oddCoreOf K).comap (C.subtype.comp (conjGen (secL K C)).subtype)

theorem odd_natCard_oddPart3 (K C : Subgroup G) : Odd (Nat.card (oddPart3 K C)) := by
  set φ := C.subtype.comp (conjGen (secL K C)).subtype with hφ
  have hinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hle : (oddPart3 K C).map φ ≤ oddCoreOf K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hcard : Nat.card ((oddPart3 K C).map φ) = Nat.card (oddPart3 K C) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).toEquiv).symm
  rw [← hcard]
  exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem map_oddPart3_le_oddCoreOf (K C : Subgroup G) :
    (oddPart3 K C).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen (secL K C)))) ≤
      oddCoreOf (secImg (conjGen (secL K C)) (secL K C)) := by
  set Y₁ := conjGen (secL K C) with hY₁
  set N := (oddPart3 K C).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₁)) with hN
  set H := secImg Y₁ (secL K C) with hH
  have hNH : N ≤ H := Subgroup.map_mono inf_le_left
  have hnorm : (N.subgroupOf H).Normal := by
    constructor
    intro n hn h
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    obtain ⟨y, hy, hyh⟩ := h.2
    have hyK : (((y : ↥C)) : G) ∈ K :=
      (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)).1
    refine ⟨y * x * y⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hx.1) (Subgroup.inv_mem _ hy)
    · exact S19Q.conj_mem_oddCoreOf hyK hx.2
    · rw [map_mul, map_mul, map_inv, hxn, hyh]
      rfl
  have hodd : Odd (Nat.card (N.subgroupOf H)) := by
    have h1 : Nat.card (N.subgroupOf H) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    rw [h1]
    exact (odd_natCard_oddPart3 K C).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hle : N.subgroupOf H ≤ classicalInvolutionOddCore ↥H := le_sSup ⟨hnorm, hodd⟩
  intro n hn
  exact mem_oddCoreOf_iff.mpr ⟨hNH hn, hle (Subgroup.mem_subgroupOf.mpr hn)⟩

variable {K : Subgroup G} {z : G} {C : Subgroup G}

namespace FusSec3

variable (h : FusSec3 K z C)

include h

theorem secAct_fixes_of_mem_cStar
    (hO : oddCoreOf (secImg (conjGen (secL K C)) (secL K C)) = ⊥) {y : ↥C}
    (hyz : (y : G) * z = z * (y : G)) (hyK : (y : G) ∈ centralizerModOdd ⊤ K) :
    ∀ x ∈ secImg (conjGen (secL K C)) (secL K C), secAct (conjGen (secL K C)) y x = x := by
  have hyN := h.mem_normalizer_sec hyz
  rintro _ ⟨k, hk, rfl⟩
  rw [QuotientGroup.mk'_apply, secAct_mk]
  set c : ↥(conjGen (secL K C)) := MulAut.conjNormal y k * k⁻¹ with hc
  have hkL : (k : ↥C) ∈ secL K C := Subgroup.mem_subgroupOf.mp hk
  have hkK : ((k : ↥C) : G) ∈ K := (Subgroup.mem_subgroupOf.mp hkL).1
  have hc1 : c ∈ (secL K C).subgroupOf (conjGen (secL K C)) := by
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((MulAut.conjNormal y k : ↥(conjGen (secL K C))) : ↥C) = y * k * y⁻¹ :=
      MulAut.conjNormal_apply y k
    change ((MulAut.conjNormal y k : ↥(conjGen (secL K C))) : ↥C) * (k : ↥C)⁻¹ ∈ secL K C
    rw [h1]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hyN _).mp hkL)
      (Subgroup.inv_mem _ hkL)
  have hc2 : c ∈ (oddCoreOf K).comap (C.subtype.comp (conjGen (secL K C)).subtype) := by
    change ((((MulAut.conjNormal y k : ↥(conjGen (secL K C))) : ↥C) : G) *
        ((k : ↥C) : G)⁻¹) ∈ oddCoreOf K
    rw [MulAut.conjNormal_apply]
    have h2 := hyK.2.2.2 _ hkK
    rw [commutatorElement_def] at h2
    simpa [mul_assoc] using h2
  have hcO : c ∈ oddPart3 K C := Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
  have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen (secL K C))) c) ∈
      oddCoreOf (secImg (conjGen (secL K C)) (secL K C)) :=
    map_oddPart3_le_oddCoreOf K C ⟨c, hcO, rfl⟩
  rw [hO, Subgroup.mem_bot, QuotientGroup.mk'_apply, hc, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, mul_inv_eq_one] at h1
  exact h1

end FusSec3

end Odd

end CFSG.ClassicalInvolution.Q3.Q3T6
