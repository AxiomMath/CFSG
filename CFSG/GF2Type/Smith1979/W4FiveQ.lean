module

public import CFSG.GF2Type.Smith1979.W4ThmA
public import CFSG.LargeExtraspecial.S5Q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Five

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_Vt_le_four (hw : S.width = 4) (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) :
    finrank (ZMod 2) (Vt S g t) ≤ 4 := by
  have h1 := finrank_Wt (S := S) (g := g) (t := t)
  have h2 := Submodule.finrank_mono (Vt_le_Wt H ht1)
  have h3 := S.finrank_Qt_eq_two_mul_width
  omega

theorem quasisimple_w4 {H : Hyp4 S g} {C : Cons311 S g} (Q : Hyp45Q H C) (hNo : NoA2 S g)
    (hw : S.width = 4) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g)
    (hVQ : ¬ V S g t ≤ S.Qa g) {K : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hK : CFSG.Open.IsSubnormal K (RmodN S g t)) (hq : CFSG.Open.IsQuasisimple K) :
    K = RmodN S g t ∧ Nat.card (LmodN S g t) = 4 := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hKR := CFSG.ClassicalInvolution.isSubnormal_le hK
  have h4 : finrank (ZMod 2) (Vt S g t) = 4 :=
    le_antisymm (finrank_Vt_le_four hw H ht1) (four_le_finrank_Vt H C ht ht1 hVQ hNo)
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ', hSp | hA | hΩ | hP⟩
  · exact absurd hR' hR
  · exact absurd hL.le_Qa hVQ
  · exact (W4ThmA.not_spCase_four hw H C ht ht1 hVQ' h4 hSp).elim
  · exact (W4ThmA.not_a6Case hw H C ht ht1 hVQ' hA).elim
  · rcases Q.omega_four ht ht1 hVQ' hΩ h4 with hs | hsol
    · refine ⟨eq_of_isSubnormal_of_isSimpleGroup hK hq hs, ?_⟩
      obtain ⟨Qf, hQ, -, -, hE, hsing⟩ := hΩ.exists_form
      have hQa : Qf (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
      rw [hE, card_pointRadical hQ (aV_ne_zero H ht) hQa, h4]
      norm_num
    · exact (false_of_isQuasisimple_of_le_solvable hKR hq hsol).elim
  · exact (W4ThmA.not_pgl25Case hw H C ht ht1 hVQ' hP).elim

end CFSG.GF2Type.Smith1979.W4Five
