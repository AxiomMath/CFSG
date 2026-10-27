module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpDihedral

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem threeTransp_isConj_mul_comm (u v : G) : IsConj (u * v) (v * u) :=
  isConj_iff.mpr ⟨u⁻¹, by group⟩

private theorem threeTransp_pow_two_ne_three (k : ℕ) : 2 ^ k ≠ 3 := by
  intro h
  have hle : k ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
    norm_num at h4
    omega
  have hkpos : k ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  have hk : k = 1 := by omega
  rw [hk] at h
  norm_num at h

private theorem threeTransp_false_of_center {d e a x : G} (hd2 : d ^ 2 = 1) (he2 : e ^ 2 = 1)
    (ha2 : a ^ 2 = 1)
    (hca : a ∈ orb2A d d ∩ orb2A d e) (hcx : x ∈ orb2A d d ∩ orb2A d e)
    (hperpeq : orb2A d d ∩ orb2A d e =
      {y | y ∈ centerOf (Subgroup.closure {d, e}) ∧ y ≠ 1})
    {k : ℕ} (hk : 2 ≤ k) (hord : orderOf (d * e) = 2 * k)
    (haxord : orderOf (a * x) = 3) : False := by
  have ha_center : a ∈ centerOf (Subgroup.closure {d, e}) ∧ a ≠ 1 := by
    have h : a ∈ ({y | y ∈ centerOf (Subgroup.closure {d, e}) ∧ y ≠ 1} : Set G) := by
      rw [← hperpeq]
      exact hca
    exact h
  have hx_center : x ∈ centerOf (Subgroup.closure {d, e}) ∧ x ≠ 1 := by
    have h : x ∈ ({y | y ∈ centerOf (Subgroup.closure {d, e}) ∧ y ≠ 1} : Set G) := by
      rw [← hperpeq]
      exact hcx
    exact h
  have hka : a = (d * e) ^ k :=
    (perp_center_closure_pair hd2 he2 (k := k) hk hord a).mp ha_center
  have hkx : x = (d * e) ^ k :=
    (perp_center_closure_pair hd2 he2 (k := k) hk hord x).mp hx_center
  have hax : a = x := hka.trans hkx.symm
  have h1 : a * x = 1 := by rw [← hax, ← pow_two, ha2]
  rw [h1, orderOf_one] at haxord
  norm_num at haxord

private theorem threeTransp_false_of_pcore {d e a x : G}
    (hQa : a ∈ CFSG.Open.pCoreOf 2 (Gxy d e))
    (hQx : x ∈ CFSG.Open.pCoreOf 2 (Gxy d e))
    (haxord : orderOf (a * x) = 3) : False := by
  have hQax : a * x ∈ CFSG.Open.pCoreOf 2 (Gxy d e) :=
    (CFSG.Open.pCoreOf 2 (Gxy d e)).mul_mem hQa hQx
  have hpQ : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 (Gxy d e)) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gxy d e))).map (Gxy d e).subtype
  obtain ⟨k, hk⟩ := hpQ.exists_orderOf_eq_pow ⟨a * x, hQax⟩
  have horder : orderOf (a * x) = 2 ^ k := by
    have hcoe :=
      (Subgroup.orderOf_coe (⟨a * x, hQax⟩ : ↥(CFSG.Open.pCoreOf 2 (Gxy d e)))).trans hk
    simpa using hcoe
  rw [haxord] at horder
  exact threeTransp_pow_two_ne_three k horder.symm

theorem s7_three {a z x d e : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (hd : d ∈ orb2A a a ∩ orb2A a x) (he : e ∈ orb2A a a ∩ orb2A a x) :
    (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1 := by
  by_contra hne
  push_neg at hne
  obtain ⟨hne3, hne2⟩ := hne
  have H' : S7Hyps d z := H.of_isConj hd.1.1 (IsConj.refl z)
  have hd2 : d ^ 2 = 1 := s7_sq_of_isConj_a H hd.1.1
  have he2 : e ^ 2 = 1 := s7_sq_of_isConj_a H he.1.1
  have ha2 : a ^ 2 = 1 := s7_sq_of_isConj_a H (IsConj.refl a)
  have hda : IsConj d a := hd.1.1.symm
  have ha_dd : a ∈ orb2A d d :=
    ⟨hda, (hda.trans hd.1.2).trans (threeTransp_isConj_mul_comm a d)⟩
  have he_sBase : e ∈ sBase d a := by
    have hdm : d * d = 1 := by simpa [pow_two] using hd2
    refine ⟨hd.1.1.symm.trans he.1.1, hd.1.1.symm.trans he.1.2, ?_, ?_⟩
    · intro h
      exact hne2 (by rw [h, hdm, one_pow])
    · intro h
      have hde : d * (d * a) = a := by rw [← mul_assoc, hdm, one_mul]
      exact hne2 (by rw [h, hde, ha2])
  obtain ⟨i, hi⟩ := (H'.tableIV.self.partition a ha_dd).cover e he_sBase
  have hP : PerpFacts d z := H'.perp.self
  have hF5 : IsF5Type d z := H'.isF5
  have ha_inter : a ∈ orb2A d d ∩ orb2A d e :=
    ⟨ha_dd, ⟨hda, (hda.trans he.1.2).trans (threeTransp_isConj_mul_comm a e)⟩⟩
  have hx_dd : x ∈ orb2A d d :=
    ⟨hd.1.1.symm.trans hx.1,
      (hd.1.1.symm.trans hd.2.2).trans (threeTransp_isConj_mul_comm x d)⟩
  have hx_de : x ∈ orb2A d e :=
    ⟨hd.1.1.symm.trans hx.1,
      (hd.1.1.symm.trans he.2.2).trans (threeTransp_isConj_mul_comm x e)⟩
  have hx_inter : x ∈ orb2A d d ∩ orb2A d e := ⟨hx_dd, hx_de⟩
  fin_cases i
  · have h0 : e ∈ sBase d a ∧ IsConj d (d * e) := by simpa [sSet] using hi
    exact absurd (s7_sq_of_isConj_a H' h0.2) hne2
  · have h1 : e ∈ sBase d a ∧ IsConj z (d * e) := by simpa [sSet] using hi
    exact absurd (s7_sq_of_isConj_z H' h1.2) hne2
  · have hord : orderOf (d * e) = 4 := (perp_orderOf_row_two hF5 hda hi).1
    have hperp := hP.perp_4B_6A a ha_dd e (Or.inl hi)
    exact threeTransp_false_of_center hd2 he2 ha2 ha_inter hx_inter hperp (k := 2)
      (by norm_num) hord hx.2.1
  · have hQa := hP.pcore_4A a ha_dd e hi a ha_inter
    have hQx := hP.pcore_4A a ha_dd e hi x hx_inter
    exact threeTransp_false_of_pcore hQa hQx hx.2.1
  · have h4 : e ∈ sBase d a ∧ orderOf (d * e) = 3 := by simpa [sSet] using hi
    exact hne3 (by rw [← h4.2]; exact pow_orderOf_eq_one (d * e))
  · have hord : orderOf (d * e) = 6 := (perp_orderOf_row_five hF5 hda hi).1
    have hperp := hP.perp_4B_6A a ha_dd e (Or.inr hi)
    exact threeTransp_false_of_center hd2 he2 ha2 ha_inter hx_inter hperp (k := 3)
      (by norm_num) hord hx.2.1

end CFSG.EvenSporadicStandard.HNRecog.Section3
