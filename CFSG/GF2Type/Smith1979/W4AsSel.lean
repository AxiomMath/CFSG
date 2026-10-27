module

public import CFSG.GF2Type.Smith1979.W4FiveQ
public import CFSG.LargeExtraspecial.S7One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_Rbar_ne_of_not_TI
    (hTI : ¬ ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨
      S.Lbar ((h : G) * g) = S.Lbar g) :
    ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g := by
  by_contra hcon
  push Not at hcon
  refine hTI fun h => ?_
  by_cases hb : S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
    have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
    have hle : S.Lbar ((h : G) * g) ≤ S.Lbar g := by
      rw [← hcon t ht.2 ht1']
      exact Lbar_mul_le_Rbar ht.1
    have hcard : Nat.card (S.Lbar ((h : G) * g)) = Nat.card (S.Lbar g) := by
      rw [Lbar_mul S h g]
      exact Subgroup.card_map_of_injective (MulAut.conj (S.ρ h)).injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem classify_four (hw : S.width = 4) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g) :
    (LinCase S g ht ∧ finrank (ZMod 2) (Vt S g t) = 2) ∨
      ∃ hVQ : ¬ V S g t ≤ S.Qa g, OmegaCase H C ht ht1 hVQ ∧
        finrank (ZMod 2) (Vt S g t) = 4 := by
  rcases timmesfeld_4_5 H hNo C ht ht1 with h | hL | ⟨hVQ, hcase⟩
  · exact absurd h hR
  ·
    refine Or.inl ⟨hL, ?_⟩
    have hm := hL.two_le_finrank
    have hT := Submodule.finrank_mono (S6.Vt_le_Tt H hNo ht1 hL)
    have hU := S7.finrank_commSpace_eq H ht ht1
    have htt : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
      congrArg Subtype.val (mul_self_of_mem_Lbar S H.conj_mem ht)
    have h2 := two_mul_finrank_commSpace_le htt
    have hQ := S.finrank_Qt_eq_two_mul_width
    omega
  ·
    have h4 : finrank (ZMod 2) (Vt S g t) = 4 :=
      le_antisymm (W4Five.finrank_Vt_le_four hw H ht1)
        (four_le_finrank_Vt H C ht ht1 hVQ hNo)
    rcases hcase with hSp | hA | hΩ | hP
    · exact (W4ThmA.not_spCase_four hw H C ht ht1 hVQ h4 hSp).elim
    · exact (W4ThmA.not_a6Case hw H C ht ht1 hVQ hA).elim
    · exact Or.inr ⟨hVQ, hΩ, h4⟩
    · exact (W4ThmA.not_pgl25Case hw H C ht ht1 hVQ hP).elim

end CFSG.GF2Type.Smith1979.W4As
