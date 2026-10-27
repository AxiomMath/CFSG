module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaCases
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G]

theorem card_RmodN_eq_thirtysix {S : Setting G} {g : G} (H : Hyp4 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hplus : CFSG.GF2Type.Smith1979.PlusTypeAt S g ht) : Nat.card (RmodN S g t) = 36 := by
  obtain ⟨Q, hQ, -, hR, -, hsing⟩ := hΩ.exists_form
  obtain ⟨P, hP2, hP⟩ := hplus
  have hplusQ : CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    refine ⟨P, by rw [hP2, h4], fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    · exact (hsing v hv0).mpr (hP v hv hv0)
  haveI : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hcardZ := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    (K := ZMod 2) (V := Vt S g t) hQ (m := 1) (by rw [h4]) (ε := 1)
    (Or.inl ⟨rfl, hplusQ⟩)
  have h72 : (2 * (Nat.card (ZMod 2) : ℤ) ^ (1 * (1 + 1)) *
      ((Nat.card (ZMod 2) : ℤ) ^ (1 + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1)) = 72 := by
    norm_num [Nat.card_zmod]
  rw [h72] at hcardZ
  have hcardO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 72 :=
    Nat.cast_injective hcardZ
  haveI : Nontrivial (Vt S g t) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hidx := Subgroup.relIndex_mul_card (omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q)
  rw [inf_eq_left.mpr (omegaGroup_le Q hQ), relIndex_omegaGroup] at hidx
  have h36 : Nat.card (omegaGroup Q hQ) = 36 := by omega
  rw [hR]
  exact h36

end CFSG.GF2Type.Smith1979.TriPlus
