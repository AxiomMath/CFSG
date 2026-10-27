module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114A
public import CFSG.GH74.E2.Alpha1Rank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11L114_data [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    t * t = 1 ∧ z * z = 1 ∧ t * z = z * t ∧ t ≠ 1 ∧ z ≠ 1 ∧ t ≠ z ∧ t ∈ S ∧ z ∈ S ∧
      secQ K1 K2 ≤ S := by
  have hb : Asc82Basic10 := hp.basic
  have hP5 : Asc82FactPockets5 := hp.facts.pockets5
  have hC5 : Asc82FactCentZ5 := hp.facts.centZ5
  have hbas := hp.basic G t L S z hctx.toSec10Z
  have hpsp : IsPSp43 L := hbas.1
  have htS : t ∈ S := hbas.2.2.2.1
  have ht2 : orderOf t = 2 := hctx.involution
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have ht2' : t * t = 1 := by
    rw [← pow_two, ← ht2]
    exact pow_orderOf_eq_one t
  have hz2' : z * z = 1 := by
    rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one z
  have hzQ : z ∈ secQ K1 K2 := (sec10KS_Q_elem hP5 hC5 hpsp hctx.toSec10Ctx).1
  have htQ : t ∉ secQ K1 K2 := sec10J_t_notin_Q hP5 hb hctx.toSec10Ctx
  refine ⟨ht2', hz2', hctx.central t htS, ?_, ?_, fun h => htQ (h ▸ hzQ), htS, hctx.mem_S,
    (sec10J_Q_le hP5 hb hctx.toSec10Ctx).trans inf_le_left⟩
  · intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  · intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)

theorem sec11L114_cent_le [Finite G] {t : G} {S R : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (hR : IsPGroup 2 R) (hSR : S ≤ R) {d : G}
    (hd : d ∈ R) (hdt : d * t = t * d) : d ∈ S := by
  have hle : S ⊔ zpowers d ≤ R := sup_le hSR (zpowers_le.2 hd)
  have hC : S ⊔ zpowers d ≤ centralizer ({t} : Set G) :=
    sup_le hS.1 (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hdt))
  have heq : S ⊔ zpowers d = S := IsSylow2Of.eq_of_le hS hC (hR.to_le hle) le_sup_left
  rw [← heq]
  exact mem_sup_right (mem_zpowers d)

theorem sec11L114_cent_Q [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    t ∈ centralizer (secQ K1 K2 : Set G) ∧ z ∈ centralizer (secQ K1 K2 : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, hQS⟩ := sec11L114_data hp hctx
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.1 (hctx.sylow.1 (hQS hq))
  · exact hctx.central q (hQS hq)

theorem sec11L114_cent_D [Finite G] (hp : Asc82Pre11) (h112 : Asc82Lemma112) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) {d : G} (hd : d ∈ secD K1 K2 R)
    (hdt : d * t = t * d) : d ∈ zpowers t ⊔ zpowers z := by
  obtain ⟨ht2, hz2, htz, ht1, hz1, hne, htS, hzS, -⟩ := sec11L114_data hp hctx
  obtain ⟨htQ, hzQ⟩ := sec11L114_cent_Q hp hctx
  have hdD : d ∈ centralizer (secQ K1 K2 : Set G) ⊓ R := hd
  have hdS : d ∈ S :=
    sec11L114_cent_le hctx.sylow hctx.sylowR.2.1 (hctx.S_le.trans hctx.T_le) hdD.2 hdt
  have hdC : d ∈ secCTQ K1 K2 T := ⟨hdD.1, hctx.S_le hdS⟩
  have htC : t ∈ secCTQ K1 K2 T := ⟨htQ, hctx.S_le htS⟩
  have hzC : z ∈ secCTQ K1 K2 T := ⟨hzQ, hctx.S_le hzS⟩
  rcases h112 G t L S z K1 K2 T R hctx with ⟨-, hA⟩ | ⟨-, r, hr, hCr, hD8, -⟩
  · rw [← hA]
    exact hdC
  · have hr2 : r * r = 1 := by
      rw [← pow_two, ← hr]
      exact pow_orderOf_eq_one r
    exact sec11L114_cent_dihedral ht2 hz2 hr2 htz ht1 hz1 hne htC hzC hCr hD8 hdC hdt

theorem asc82Lemma114_of (hp : Asc82Pre11) (h112 : Asc82Lemma112) : Asc82Lemma114 := by
  intro G _ _ t L S z K1 K2 T R hctx
  obtain ⟨ht2, hz2, htz, ht1, hz1, hne, htS, hzS, -⟩ := sec11L114_data hp hctx
  obtain ⟨htQ, hzQ⟩ := sec11L114_cent_Q hp hctx
  have hDR : secD K1 K2 R ≤ R := inf_le_right
  have hD2 : IsPGroup 2 (secD K1 K2 R) := hctx.sylowR.2.1.to_le hDR
  have hSR : S ≤ R := hctx.S_le.trans hctx.T_le
  have hWD : zpowers t ⊔ zpowers z ≤ secD K1 K2 R :=
    sup_le (zpowers_le.2 ⟨htQ, hSR htS⟩) (zpowers_le.2 ⟨hzQ, hSR hzS⟩)
  by_cases hWeq : zpowers t ⊔ zpowers z = secD K1 K2 R
  · left
    rw [← hWeq]
    exact sec11L114_pair_isDih2 ht2 hz2 htz ht1 hz1 hne
  · rcases CFSG.GH74.E2.dihedral_or_semidihedral_of_selfcentralizing hD2 hWD
      (sec11L114_pair_card ht2 hz2 htz ht1 hz1 hne)
      (fun w hw => sec11L114_pair_sq ht2 hz2 htz hw) (mem_sup_left (mem_zpowers t)) ht1 hWeq
      (fun d hd hdt => sec11L114_cent_D hp h112 hctx hd hdt) with
      ⟨a, ha2, ⟨e⟩⟩ | ⟨m, hm4, ⟨e⟩⟩
    · exact Or.inl ⟨a, by omega, ⟨e⟩⟩
    · exact Or.inr ⟨m, hm4, ⟨e⟩⟩

end CFSG.OddStandard.SmallF3.Omega
