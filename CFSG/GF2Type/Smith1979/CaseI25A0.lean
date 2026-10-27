module

public import CFSG.GF2Type.Smith1979.CaseIChain
public import CFSG.GF2Type.Smith1979.CaseIClosure
public import CFSG.GF2Type.Smith1979.CaseICount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.OrthoF2 CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Standing

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem twoCentralBar_of_strongClosed
    (hSC : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) : TwoCentralBar S t := by
  have hcard := card_Obar_eq_three_sc hCE H hNo C ht ht1 hVQ hΩ hN h6.ge hSC
  have hP : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_eq_two H ht ht1, pow_one])
  obtain ⟨T, hT, htT⟩ := S5.exists_isSylowTwoIn_ge (zpowers_le.mpr (S.Lbar_le_Mbar g ht)) hP
  refine ⟨T, hT, fun x hx => ?_⟩
  have htT' : t ∈ T := htT (mem_zpowers t)
  have h1 : x * t * x⁻¹ * t⁻¹ ∈ Obar S :=
    comm_mem_Obar_sc hCE H hNo C ht ht1 hVQ hΩ hN h6.ge hSC (hT.le hx)
  have h2 : x * t * x⁻¹ * t⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem hx htT') (T.inv_mem hx)) (T.inv_mem htT')
  obtain ⟨k, hk⟩ := hT.exists_pow_eq_one h2
  have h3 : (x * t * x⁻¹ * t⁻¹) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Obar S) (x := (⟨_, h1⟩ : Obar S))
    rw [hcard] at this
    exact congrArg Subtype.val this
  have h4 : x * t * x⁻¹ * t⁻¹ = 1 := by
    have hd : orderOf (x * t * x⁻¹ * t⁻¹) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h3)
    have hcop : Nat.gcd (2 ^ k) 3 = 1 := by
      refine Nat.Coprime.pow_left k ?_
      norm_num
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
    _ = t * x := by rw [h4, one_mul]

theorem delta_six_of_not_twoCentral (h2c : ¬ TwoCentralBar S t) :
    (Delta S g t).ncard = 6 ∧ (orbitOf (RmodN S g t) (aV ht)).ncard = 27 := by
  rcases strongClosed_or_delta_six hCE countSixStmt H hNo C ht ht1 hVQ hΩ hN h6 with hSC | ⟨hD, h27⟩
  · exact absurd (twoCentralBar_of_strongClosed hCE H hNo C ht ht1 hVQ hΩ hN h6 hSC) h2c
  · rw [← CaseIClosure.Delta_eq_class_inter H C ht] at hD
    exact ⟨hD, h27⟩

end Standing

end Case25

end CFSG.GF2Type.Smith1979
