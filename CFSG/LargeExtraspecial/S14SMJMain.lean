module

public import CFSG.LargeExtraspecial.S14SMJL
public import CFSG.LargeExtraspecial.S14SMHDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open SMJ

theorem smithE261_of
    (hM : SmithE22Module) (hLoc : SmithE23a) (hFS : FSmithSixFiveOddInput)
    (h35 : AschbacherSmith35Input) : SmithE261 := by
  intro G _ _ _ S hw hU t u ht hu htM huM htQ huQ h3
  have C : Cfg S t u := ⟨ht, hu, htM, huM, htQ, huQ, h3⟩
  have L := Loc.of hM hLoc hw hU C
  have hext := isExtraspecialPGroup_cent2 (smithE25_of hM) (smithE34a_of_module hM) S hw hU ht
    hu htM huM htQ huQ h3 L.card_ge
  set T := setH C L hext with hT
  have hcardT : Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ (1 + 2 * T.width) := by
    rw [← card_setH_Q C L hext]
    exact T.card_Q_eq
  have hw4 : 4 ≤ T.width := by
    have h1 := L.card_ge
    rw [hcardT] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have hw10 : T.width ≤ 10 := by
    have h1 := Subgroup.card_le_of_le (inf_le_left : S.QG ⊓ cent2 t u ≤ S.QG)
    rw [hcardT, S.card_QG_eq_card_Q, S.card_Q_eq, hw] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have hAH : T.AschbacherHyp :=
    hFS _ T (by omega) (setH_oddCore C L hext hM hLoc hw hU) (setH_weak C L hext)
  have hO : ∀ x ∈ T.QG, orderOf x = 2 → T.ZInOTwo x := fun x hx hx2 => hAH x hx (by
    rintro rfl
    rw [orderOf_one] at hx2
    exact absurd hx2 (by norm_num))
  obtain ⟨hLs, hLc⟩ := T.isSimpleGroup_zGen_of_weaklyClosed (by omega) hO
    (setH_z_not_mem_center C L hext hM hLoc hw hU) (setH_weak C L hext)
  set K := T.zGen.map (cent2 t u).subtype with hK
  have hKH : K ≤ cent2 t u := map_subtype_le _
  have hKn : ∀ h ∈ cent2 t u, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    rintro h hh _ ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, T.zGen_normal.conj_mem k hk ⟨h, hh⟩, rfl⟩
  have hzK : S.z ∈ K := ⟨T.z, T.z_mem_zGen, rfl⟩
  have eK : T.zGen ≃* K := T.zGen.equivMapOfInjective _ (cent2 t u).subtype_injective
  have : IsSimpleGroup K := eK.symm.isSimpleGroup
  have hnc : ¬ ∀ k ∈ K, k * S.z = S.z * k := by
    intro h
    have hzc : T.z ∈ centralizer (T.zGen : Set ↥(cent2 t u)) := by
      rw [mem_centralizer_iff]
      intro k hk
      exact Subtype.ext (h k ⟨k, hk, rfl⟩)
    rw [hLc, mem_bot] at hzc
    exact S.z_ne_one (congrArg Subtype.val hzc)
  obtain ⟨g, hgK, hgc, hgne⟩ := exists_conj_commute S hzK hnc
  have hQK := QH_le C L hext hKH hKn hzK (isConj_iff.mpr ⟨g, rfl⟩)
    (K.mul_mem (K.mul_mem hgK hzK) (K.inv_mem hgK)) hgc hgne
  have hTLw : (setL L hext hKH hKn hzK hQK).width = T.width :=
    setL_width L hext hKH hKn hzK hQK hcardT
  rcases h35 K (setL L hext hKH hKn hzK hQK) (by rw [hTLw]; omega)
      (setL_weak L hext hKH hKn hzK hQK) with he | ⟨-, he⟩
  · obtain ⟨e⟩ := he
    rw [hTLw] at e
    by_cases h4 : T.width = 4
    · have h6 : T.width + 2 = 6 := by omega
      exact ⟨K, hzK, fun n hn => mem_cent2.mp (hKH hn), ⟨h6 ▸ e⟩⟩
    ·
      refine (false_of_dvd_card S hw hU ht (hKH.trans inf_le_left) (Or.inr rfl) ?_).elim
      rw [Nat.card_congr e.toEquiv]
      exact forty_three_dvd_card_PSU (by omega) (by omega)
  · obtain ⟨e⟩ := he
    exact (not_co2 S hw hU ht (hKH.trans inf_le_left) e).elim

end CFSG.LargeExtraspecial.S14
