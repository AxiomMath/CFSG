module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriConf.Ident
public import CFSG.GF2Type.Smith1980Orth.PathGlue
public import CFSG.LargeExtraspecial.S14C12SmHolt
public import CFSG.Holt.H78.Bridge
public import CFSG.Holt.H78.Theorem1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriConf

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.Smith1980Orth CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity
  CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

theorem alt_factorization_two_ne (n : ℕ) :
    (Nat.card (alternatingGroup (Fin n))).factorization 2 ≠ 12 ∧
      (Nat.card (alternatingGroup (Fin n))).factorization 2 ≠ 13 := by
  constructor <;> intro h
  · by_cases hn : n ≤ 15
    · have hdvd : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial 15 := by
        refine (Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))).trans ?_
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        exact Nat.factorial_dvd_factorial hn
      have h2 : 2 ^ 12 ∣ Nat.card (alternatingGroup (Fin n)) :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr (by omega)
      exact absurd (h2.trans hdvd) (by norm_num)
    · push Not at hn
      have h2 : 2 ^ 14 ∣ Nat.card (alternatingGroup (Fin n)) := by
        haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        have h15 : 2 ^ 15 ∣ Nat.factorial n :=
          dvd_trans (by norm_num : 2 ^ 15 ∣ Nat.factorial 16)
            (Nat.factorial_dvd_factorial (by omega))
        have h16 : 2 ^ 14 * 2 ∣ Nat.factorial n := by simpa [pow_succ] using h15
        exact Nat.dvd_div_of_mul_dvd h16
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
      omega
  · by_cases hn : n ≤ 15
    · have hdvd : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial 15 := by
        refine (Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))).trans ?_
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        exact Nat.factorial_dvd_factorial hn
      have h2 : 2 ^ 13 ∣ Nat.card (alternatingGroup (Fin n)) :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr (by omega)
      exact absurd (h2.trans hdvd) (by norm_num)
    · push Not at hn
      have h2 : 2 ^ 14 ∣ Nat.card (alternatingGroup (Fin n)) := by
        haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        have h15 : 2 ^ 15 ∣ Nat.factorial n :=
          dvd_trans (by norm_num : 2 ^ 15 ∣ Nat.factorial 16)
            (Nat.factorial_dvd_factorial (by omega))
        have h16 : 2 ^ 14 * 2 ∣ Nat.factorial n := by simpa [pow_succ] using h15
        exact Nat.dvd_div_of_mul_dvd h16
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
      omega

theorem reach_of_not_alternating
    [IsSimpleGroup G]
    {z : G} (hz : orderOf z = 2)
    (hS : ∃ P : Sylow 2 G, z ∈ (P : Subgroup G) ∧ (P : Subgroup G) ≤ centralizer {z})
    (hnalt : ∀ n, ¬ Nonempty (G ≃* alternatingGroup (Fin n)))
    {d e t : G} (hd : IsConj z d) (he : IsConj z e) (h4 : orderOf (d * e) = 4)
    (ht : IsConj z t) : Reach (conjugatesOf z) z t := by
  have hdord : orderOf d = 2 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hd
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
  have heord : orderOf e = 2 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp he
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
  have hd2 : d * d = 1 := by
    rw [← sq, ← hdord, pow_orderOf_eq_one]
  have he2 : e * e = 1 := by
    rw [← sq, ← heord, pow_orderOf_eq_one]
  by_contra hnt
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨d, e, fun hc => ?_⟩
    have h1 : (d * e) ^ 2 = 1 := by
      rw [_root_.sq, show d * e * (d * e) = d * (e * d) * e by group, ← hc,
        show d * (d * e) * e = (d * d) * (e * e) by group, hd2, he2, one_mul]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h2
    norm_num at h2
  rcases RankThree.Holt.holt_commutingComponent
      (CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1)
      hnonab hz hS ⟨t, ht, hnt⟩ with ⟨H, hH⟩ | ⟨n, -, ⟨φ⟩⟩
  · exact SmithHolt.false_of_isStronglyEmbedded hH hdord heord h4
  · exact hnalt n ⟨φ⟩

theorem false_of_oLocal_oPath
    [IsSimpleGroup G] {S : Setting G} (hw : S.width = 4) {g : G} (H : Hyp4 S g)
    (hirr : ¬ S.IsReducible) (hloc : OLocal S) (hpath : OPath S)
    (hM : Nat.card S.Mbar = 648 ∨ Nat.card S.Mbar = 1296)
    (hidx : Nat.card S.Mbar = 648 → S.M.index % 8 = 7) : False := by
  have h4 : ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4 := by
    by_contra hno
    push Not at hno
    refine hirr (SmithQ.isReducible_of_commute S (by omega) (isConj_iff.mpr ⟨g, rfl⟩)
      H.conj_mem H.conj_ne ?_)
    intro x y hx hxQ hy hyQ
    by_contra hxy
    exact hno x y hx hy (SmithQ.orderOf_mul_eq_four S hxQ hyQ
      (SmithQ.mul_self_eq_one_of_isConj S hx)
      (SmithQ.mul_self_eq_one_of_isConj S hy) hxy)
  have hnalt : ∀ n, ¬ Nonempty (G ≃* alternatingGroup (Fin n)) := by
    obtain ⟨e, he, hcard, -⟩ := card_G_eq_of_triality hw hM hidx
    have hfac : (Nat.card G).factorization 2 = 12 ∨ (Nat.card G).factorization 2 = 13 := by
      have h12 := factorization_two_pow_mul_odd (N := 12 + e) (odd_81_mul_index S)
      rw [← hcard] at h12
      omega
    intro n hAn
    have hcardA : Nat.card G = Nat.card (alternatingGroup (Fin n)) :=
      Nat.card_congr hAn.some.toEquiv
    rcases hfac with h | h
    · exact (alt_factorization_two_ne n).1 (hcardA ▸ h)
    · exact (alt_factorization_two_ne n).2 (hcardA ▸ h)
  have h4' := h4
  obtain ⟨d, e, hd, he, hde⟩ := h4
  have hD : ThreeFourPlusClass G {x | IsConj S.z x} := by
    refine threeFourPlusClass_of_products S fun a b ha hb => ?_
    have hra := reach_of_not_alternating S.orderOf_z
      (SmithHolt.exists_sylow_twoCentral S) hnalt hd he hde ha
    have hrb := reach_of_not_alternating S.orderOf_z
      (SmithHolt.exists_sylow_twoCentral S) hnalt hd he hde hb
    obtain ⟨v, hv, hav, hvb⟩ :=
      SmithGraph.exists_common_of_reach hpath ha (reach_trans (reach_symm hra) hrb)
    exact SmithGraph.threeFour_of_common S (local_of_OLocal S hloc) ha hb hv hav hvb
  exact false_of_threeFourPlusClass hw hD h4' hM hidx

end CFSG.GF2Type.Smith1979.TriConf
