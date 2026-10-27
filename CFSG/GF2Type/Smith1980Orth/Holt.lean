module

public import CFSG.GF2Type.Smith1980Orth.Defs
public import CFSG.LargeExtraspecial.S14C12SmHolt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.Timmesfeld.Connectivity
  CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem reach_conjugatesOf [IsSimpleGroup G]
    (hHolt : HoltUniqueFixedPointSimple) (hAlt : AltInput) {S : Setting G} (O : OrthData S)
    {d e : G} (hd : IsConj S.z d) (he : IsConj S.z e) (h4 : orderOf (d * e) = 4)
    {t : G} (ht : IsConj S.z t) : Reach (conjugatesOf S.z) S.z t := by
  by_contra hnt
  have hd2 := SmithQ.mul_self_eq_one_of_isConj S hd
  have he2 := SmithQ.mul_self_eq_one_of_isConj S he
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨d, e, fun hc => ?_⟩
    have h1 : (d * e) ^ 2 = 1 := by
      rw [_root_.sq, show d * e * (d * e) = d * (e * d) * e by group, ← hc,
        show d * (d * e) * e = (d * d) * (e * e) by group, hd2, he2, one_mul]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h2
    norm_num at h2
  rcases RankThree.Holt.holt_commutingComponent hHolt hnonab S.orderOf_z
      (SmithHolt.exists_sylow_twoCentral S) ⟨t, ht, hnt⟩ with ⟨H, hH⟩ | ⟨n, -, hφ⟩
  · exact SmithHolt.false_of_isStronglyEmbedded hH (S.orderOf_of_isConj hd)
      (S.orderOf_of_isConj he) h4
  · exact hAlt G S O n hφ

end CFSG.GF2Type.Smith1980Orth
