module

public import CFSG.GH74.Uniqueness.SU.KI1r4Parts
public import CFSG.GH74.Uniqueness.SU.KI1r4F61M22
public import CFSG.GH74.Uniqueness.SU.KI1r4F61J2
public import CFSG.GH74.Uniqueness.SU.KI1r4F61McL
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L34
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216
public import CFSG.GH74.Uniqueness.SU.KI1r3Fam
public import CFSG.GH74.Uniqueness.SU.KI1r3FamL2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Ly

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74
open CFSG.GH74.Uniqueness.SU.K.R3 CFSG.GH74.KGroups.L34

attribute [local instance] generalizedFitting_normal'

structure F61Gaps : Prop where
  j3 : OuterFourSp .J3
  ly : OuterFourSp .Ly

theorem strictSp_J3 (h : OuterFourSp .J3) : StrictFamSp .J3 :=
  strictSp_of_outerFour .J3 CFSG.Sporadic.J3.fam_j3_simplicity.2.2 (by
    show ¬ (Nat.card NativeSporadic.J3).Prime
    rw [CFSG.Sporadic.J3.card_J3]
    norm_num) h

theorem strictSp_Ly (h : OuterFourSp .Ly) : StrictFamSp .Ly :=
  strictSp_of_outerFour .Ly CFSG.Sporadic.Ly.fam_ly_simplicity.2.2 (by
    show ¬ (Nat.card NativeSporadic.Ly).Prime
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num) h

theorem no_strictFix {H : Type} [Group H] [Finite H] {x : H} (hx2 : orderOf x = 2)
    (hrk : Open.pRank 2 (centralizer ({x} : Set H) ⊓ generalizedFitting H) = 1)
    (hS : StrictFix ↥(generalizedFitting H)) : False := by
  have hx : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hα2 : (MulAut.conjNormal x : MulAut ↥(generalizedFitting H)) ^ 2 = 1 := by
    rw [← map_pow, hx, map_one]
  exact no_fixed_four_group hrk (hS _ hα2)

theorem fixedSub_conjNormal {H : Type} [Group H] [Finite H] (x : H) :
    (fixedSub ↥(generalizedFitting H) (MulAut.conjNormal x)).map (generalizedFitting H).subtype =
      centralizer ({x} : Set H) ⊓ generalizedFitting H := by
  ext a
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype, mem_fixedSub]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, k.2⟩
    have h1 := congrArg Subtype.val hk
    simp only [MulAut.conjNormal_apply] at h1
    calc (k : H) * x = x * k * x⁻¹ * x := by rw [h1]
      _ = x * k := by group
  · rintro ⟨hc, ha⟩
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [← hc]
      _ = a := by group

theorem f61full_of_gaps
    (G : F61Gaps) : F61Full := by
  intro H _ _ hGH hsimple hnab hcen x hx2 hxK hrk
  have hGHL : GHList ↥(generalizedFitting H) :=
    hGH.ghList_of_surjection (A := generalizedFitting H) (MonoidHom.id _) Function.surjective_id
      hsimple hnab
  have hx : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hα2 : (MulAut.conjNormal x : MulAut ↥(generalizedFitting H)) ^ 2 = 1 := by
    rw [← map_pow, hx, map_one]
  have hno : StrictFix ↥(generalizedFitting H) → False := fun hS => no_strictFix hx2 hrk hS
  unfold GHList at hGHL
  rcases hGHL with ⟨n, hn7, hn11, ⟨e⟩⟩ | hsp | ⟨p, f, hp, hf, hcases⟩
  · exact (hno (StrictFix.of_mulEquiv e.symm (strictAlt n hn7 hn11))).elim
  · rcases hsp with h | h | h | h | h | h | h | h | h
    · exact (hno (strictSp_M11 _ h)).elim
    · exact (hno (strictSp_M12 _ h)).elim
    · exact (hno (strictSp_M22 _ h)).elim
    · exact (hno (strictSp_M23 _ h)).elim
    · exact (hno (strictSp_J1 _ h)).elim
    · exact (hno (strictSp_J2 _ h)).elim
    · exact (hno (strictSp_J3 G.j3 _ h)).elim
    · exact (hno (strictSp_McL _ h)).elim
    · exact (hno (strictSp_Ly G.ly _ h)).elim
  · rcases hcases with ⟨hp2, hL⟩ | ⟨hp2, -, hL⟩ | ⟨hp2, -, hL⟩ | ⟨h4, hL⟩ | ⟨h4, hL⟩ | hL | ⟨-, hL⟩
    · rcases hL with hL | hL | hL | hL | hL | hL
      · exact Or.inl ⟨p, f, hp, hp2, hL, isPGL2_sup_zpowers_of_aut hcen
          (famL2 _ p f hp hp2 hL hsimple _ hα2 (conjNormal_not_inner hcen hxK)
            (no_fixed_four_group hrk))⟩
      · exact (hno (strictLie_psl3 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (strictLie_psu3 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (strictLie_psp2 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (strictLie_g2 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (strictLie_3d4 _ hsimple hnab p f hp hp2 hL)).elim
    · exact (hno (strictLie_psl4 _ hsimple hnab p f hp hp2 hL)).elim
    · exact (hno (strictLie_psu4 _ hsimple hnab p f hp hp2 hL)).elim
    · have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      exact (hno (strictLie_psl5 _ hsimple hnab p f hp hp2 hL)).elim
    · have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      exact (hno (strictLie_psu5 _ hsimple hnab p f hp hp2 hL)).elim
    · exact (hno (strictRee _ hsimple hnab f hL)).elim
    · rcases hL with hL | hL | hL | hL | hL
      · exact (hno (strictL28 hsimple hnab hL)).elim
      · exact (hno (strictL216 hL)).elim
      ·
        obtain ⟨e⟩ := CFSG.GH74.KGroups.L34.equiv_of_lieModel hL
        rcases l34_fixed_cases e _ hα2 with h4 | h9
        · exact (no_fixed_four_group hrk h4).elim
        · right
          have hmap := fixedSub_conjNormal (H := H) x
          have hcard : Nat.card ↥(fixedSub ↥(generalizedFitting H) (MulAut.conjNormal x)) =
              Nat.card ↥(centralizer ({x} : Set H) ⊓ generalizedFitting H) := by
            rw [← hmap]
            exact (Subgroup.card_map_of_injective (generalizedFitting H).subtype_injective).symm
          exact ⟨hL, by rw [← hcard]; exact h9⟩
      · exact (hno (strictU34 hsimple hnab hL)).elim
      · exact (hno (strictSz8 hsimple hnab hL)).elim

end CFSG.GH74.Uniqueness.SU.K.R4
