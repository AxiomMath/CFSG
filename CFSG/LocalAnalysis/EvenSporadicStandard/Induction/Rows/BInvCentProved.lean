module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MRowFacts
public import CFSG.Monster.B.CTIB.UniqueComponentFinal
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.Rank2048
public import CFSG.Monster.B.Co2.Simple
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.Sporadic.NativeFinite
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.Short
open CFSG.Monster.Griess (vMinus vMinus_mem)
open CFSG.Monster.Code (classOf)

theorem isSolvable_centralizer_of_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G)
    (h' : H) (he : e g = h') (h : Group.IsSolvable ↥(centralizer ({g} : Set G))) :
    Group.IsSolvable ↥(centralizer ({h'} : Set H)) := by
  subst he
  exact isSolvable_centralizer_mulEquiv e g h

section


theorem orderOf_rs_eq_two {i : ℕ} (hi : i < 14) : orderOf (rs i) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact rs_mul_self hi) (rs_ne_one hi)

end

section


theorem not_isSolvable_cent_rs1 : ¬ Group.IsSolvable ↥(centralizer ({rs 1} : Set Sbp)) := by
  obtain ⟨K, -, -, hq, -, -, hcard, -⟩ := native_rank_1860_unique_component_final (rs 1)
    (orderOf_rs_eq_two (by norm_num)) native_four_involution_classes.2.1
  have hnt : Nontrivial K := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (K ⧸ center K) := QuotientGroup.mk_surjective.subsingleton
    have h1 : Nat.card (K ⧸ center K) = 1 := Nat.card_of_subsingleton 1
    rw [hcard] at h1
    norm_num at h1
  have : Group.IsPerfect K := hq.1
  intro hsolv
  exact Group.IsPerfect.not_isSolvable K (inferInstance : Group.IsSolvable ↥K)

end

section


theorem not_isSolvable_cent_rs5 : ¬ Group.IsSolvable ↥(centralizer ({rs 5} : Set Sbp)) := by
  obtain ⟨K, -, -, hs, -, hcard, -⟩ := native_rank_2158_distance_three_product_final.2.1 (rs 5)
    (orderOf_rs_eq_two (by norm_num)) native_four_involution_classes.2.2.2.1
  intro hsolv
  exact not_isSolvable_of_simple_card hs (by rw [hcard]; norm_num)
    (inferInstance : Group.IsSolvable ↥K)

end

section


theorem kv_simple_card : IsSimpleGroup KS ∧ Nat.card KS = 42305421312000 := by
  have h := (CFSG.Monster.B.Co2.native_short_stabilizer_simple.1 (vMinus 0 1)
    (vMinus_mem (by decide))).2.2
  have hs := (CFSG.Monster.B.Co2.native_short_stabilizer_simple.1 (vMinus 0 1)
    (vMinus_mem (by decide))).1
  have e : Kstab (classOf (vMinus 0 1)) ≃* KS :=
    MulEquiv.subgroupCongr (congrArg Kstab phi0_coordOf_rStar.symm)
  exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ hs e.symm, (Nat.card_congr e.toEquiv).symm.trans h⟩

end

section


theorem not_isSolvable_cent_rs0 : ¬ Group.IsSolvable ↥(centralizer ({rs 0} : Set Sbp)) := by
  intro hsolv
  rw [rs0_eq] at hsolv
  have hc : (1 : Sbp) * xs * (1 : Sbp)⁻¹ = xs := by simp
  have hJ : Group.IsSolvable ↥Jbar :=
    Group.isSolvable_of_surjective (f := (centJbar hc).toMonoidHom) (centJbar hc).surjective
  have hK : Group.IsSolvable KS := Group.isSolvable_of_surjective jbarToKv_surjective
  exact not_isSolvable_of_simple_card kv_simple_card.1 (by rw [kv_simple_card.2]; norm_num) hK

end

section


theorem not_isSolvable_cent_of_involution {s : Sbp} (hs : orderOf s = 2) :
    ¬ Group.IsSolvable ↥(centralizer ({s} : Set Sbp)) := by
  obtain ⟨i, ⟨hi, hconj⟩, -⟩ := native_four_involution_classes.1 s hs
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  intro hsolv
  have h := isSolvable_centralizer_of_eq (MulAut.conj c) s (rs i) hc hsolv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact not_isSolvable_cent_rs1 h
  · exact not_isSolvable_cent_rs0 h
  · exact not_isSolvable_cent_rs5 h
  · rw [rs3_eq] at h
    exact not_isSolvable_cent_qS7 h

end

section


theorem bInvCent_proved : BInvCentNonsolvable := by
  intro X _ hX b hb1 hb2
  obtain ⟨e⟩ := hX
  have e2 : Nonempty (X ≃* NativeSporadic.B) := ⟨e⟩
  obtain ⟨e'⟩ := e2
  let e'' : X ≃* Sbp := e'.trans iotaEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : e'' b ≠ 1 := fun h => hb1 (e''.injective (h.trans (map_one e'').symm))
  have hsq : e'' b * e'' b = 1 := by rw [← map_mul, hb2, map_one]
  have hord : orderOf (e'' b) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  intro hsolv
  exact not_isSolvable_cent_of_involution hord (isSolvable_centralizer_mulEquiv e'' b hsolv)

end

end CFSG.EvenSporadicStandard.Induction.Hyp
