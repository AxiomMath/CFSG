module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.CenterQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0Aut
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUniqueBound
public import CFSG.Sporadic.Schreier.Co3First

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.EvenSmallLie.Sp6
open CFSG.ComponentClassification.M12Cover
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0Aut

private theorem fixedSubgroup_conj_eq_centralizer {G : Type*} [Group G] (a : G) :
    fixedSubgroup (MulAut.conj a) = Subgroup.centralizer ({a} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change a * x * a⁻¹ = x ↔ x * a = a * x
  constructor
  · intro h
    calc
      x * a = (a * x * a⁻¹) * a := by rw [h]
      _ = a * x := by group
  · intro h
    calc
      a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [← h]
      _ = x := by group

private theorem fixedSubgroup_one {G : Type*} [Group G] :
    fixedSubgroup (1 : MulAut G) = ⊤ := by
  ext x
  simp [fixedSubgroup]

@[expose] def IsSp62Cover (K : Type) [Group K] : Prop :=
  commutator K = ⊤ ∧ LieModel (K ⧸ center K) .PSp 3 2 1

theorem IsTwoSp62.isSp62Cover {X : Type} [Group X] (h : IsTwoSp62 X) : IsSp62Cover X :=
  ⟨h.1, h.2.2⟩

theorem IsSp62Cover.isQuasisimple {K : Type} [Group K] (h : IsSp62Cover K) :
    CFSG.Open.IsQuasisimple K := by
  exact ⟨h.1, LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h.2⟩

theorem IsSp62Cover.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : IsSp62Cover K) : IsSp62Cover K' := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr h.1
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  exact LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center K) (Subgroup.center K') e
      (Subgroup.map_center_eq e)) h.2

theorem IsTwoSp62.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : IsTwoSp62 K) : IsTwoSp62 K' := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr h.1
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, h.2.1]
  · exact LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center K) (Subgroup.center K') e
        (Subgroup.map_center_eq e)) h.2.2

section Co3M

open CFSG.Sporadic.Schreier.Co3


theorem isTwoSp62_co3M : IsTwoSp62 ↥co3M := by
  refine ⟨Group.IsPerfect.commutator_eq_top, card_co3M_center, ?_⟩
  exact Or.inl ⟨by decide, co3MQuot_classicalModel⟩

end Co3M

section Certified


theorem sp62_involution_centralizer_card {Q : Type} [Group Q] (hQ : LieModel Q .PSp 3 2 1)
    {g : Q} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    2 ^ 7 ∣ Nat.card (centralizer ({g} : Set Q)) ∧
      Nat.card (centralizer ({g} : Set Q)) ≤ 23040 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hQ
  have hge : e g ≠ 1 := fun h => hg1 (e.injective (by simpa using h))
  have hg2p : (e g) ^ 2 = 1 := by rw [pow_two, ← map_mul, hg2, map_one]
  have horder : orderOf (e g) = 2 := orderOf_eq_prime hg2p hge
  have horderA : orderOf (((e g : co3X36) : Equiv.Perm (Fin 36))) = 2 :=
    (Subgroup.orderOf_coe (e g)).trans horder
  obtain ⟨r, hr, c, hc, hcv⟩ :=
    co3X36_involution_centralizers.1 ((e g : co3X36) : Equiv.Perm (Fin 36)) (e g).2 horderA
  have hcard1 : Nat.card (centralizer ({g} : Set Q)) =
      Nat.card (centralizer ({(e g : co3X36)} : Set co3X36)) :=
    Nat.card_congr (centralizerEquiv e g).toEquiv
  have hcard2 : Nat.card (centralizer ({(e g : co3X36)} : Set co3X36)) =
      Nat.card (centralizerIn co3X36 ((e g : co3X36) : Equiv.Perm (Fin 36))) :=
    Nat.card_congr (centralizerSubgroupEquiv co3X36 (e g)).toEquiv
  have hkey :
      2 ^ 7 ∣ Nat.card (centralizerIn co3X36 ((e g : co3X36) : Equiv.Perm (Fin 36))) ∧
        Nat.card (centralizerIn co3X36 ((e g : co3X36) : Equiv.Perm (Fin 36))) ≤ 23040 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have hc1 : Nat.card (centralizerIn co3X36 ((e g : co3X36) : Equiv.Perm (Fin 36))) =
          Nat.card (centralizerIn co3X36 sp6Rep1) := by
        rw [hcv]
        exact (Nat.card_congr (centralizerInConjEquiv co3X36 hc sp6Rep1).toEquiv).symm
      rw [hc1, co3X36_involution_centralizers.2.1]
      exact ⟨by norm_num, by norm_num⟩
    · have hc2 : Nat.card (centralizerIn co3X36 ((e g : co3X36) : Equiv.Perm (Fin 36))) =
          Nat.card (centralizerIn co3X36 sp6Rep2) := by
        rw [hcv]
        exact (Nat.card_congr (centralizerInConjEquiv co3X36 hc sp6Rep2).toEquiv).symm
      rw [hc2, co3X36_involution_centralizers.2.2.1]
      exact ⟨by norm_num, by norm_num⟩
    · have hc3 : Nat.card (centralizerIn co3X36 ((e g : co3X36) : Equiv.Perm (Fin 36))) =
          Nat.card (centralizerIn co3X36 sp6Rep3) := by
        rw [hcv]
        exact (Nat.card_congr (centralizerInConjEquiv co3X36 hc sp6Rep3).toEquiv).symm
      rw [hc3, co3X36_involution_centralizers.2.2.2.1]
      exact ⟨by norm_num, by norm_num⟩
    · have hc4 : Nat.card (centralizerIn co3X36 ((e g : co3X36) : Equiv.Perm (Fin 36))) =
          Nat.card (centralizerIn co3X36 sp6Rep4) := by
        rw [hcv]
        exact (Nat.card_congr (centralizerInConjEquiv co3X36 hc sp6Rep4).toEquiv).symm
      rw [hc4, co3X36_involution_centralizers.2.2.2.2.1]
      exact ⟨by norm_num, by norm_num⟩
  rw [hcard1, hcard2]
  exact hkey

theorem IsSp62Cover.aut_inner {K : Type} [Group K] [Finite K] (h : IsSp62Cover K)
    (α : MulAut K) : ∃ g : K, α = MulAut.conj g := by
  haveI : Finite (K ⧸ Subgroup.center K) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective (N := Subgroup.center K))
  obtain ⟨gb, hgb⟩ := autInner_of_lieModel_PSp h.2 (centerQuotAut α)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s := Subgroup.center K) gb
  refine ⟨g, centerQuotAut_injective h.1 ?_⟩
  rw [hgb, centerQuotAut_conj, hg]

theorem IsSp62Cover.card_center_le_two {K : Type} [Group K] [Finite K] (h : IsSp62Cover K) :
    Nat.card (center K) ≤ 2 := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr h.1
  have hle := CFSG.EvenSmallLie.SympSix.card_ker_le_two h.2
    (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective (N := Subgroup.center K))
    (by rw [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk'] at hle

theorem IsSp62Cover.card_eq {K : Type} [Group K] [Finite K] (h : IsSp62Cover K) :
    Nat.card K = Nat.card (center K) * 1451520 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K),
    CFSG.EvenSmallLie.SympSix.card_of_lieModel h.2]
  ring

theorem IsSp62Cover.two_pow_dvd_fixed {K : Type} [Group K] [Finite K] (h : IsSp62Cover K)
    (ζ : MulAut K) (hζ : ζ * ζ = 1) : 2 ^ 7 ∣ Nat.card (fixedSubgroup ζ) := by
  let Q := K ⧸ Subgroup.center K
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr h.1
  haveI : Finite Q :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective (N := Subgroup.center K))
  have hQ : LieModel Q .PSp 3 2 1 := h.2
  have hcenter : Subgroup.center Q = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot K
  have hζbar : centerQuotAut ζ * centerQuotAut ζ = 1 := by
    rw [← centerQuotAut_mul, hζ, centerQuotAut_one]
  obtain ⟨gb, hgb⟩ := autInner_of_lieModel_PSp hQ (centerQuotAut ζ)
  have hgg : gb * gb = 1 := by
    have hconj : MulAut.conj (gb * gb) = (1 : MulAut Q) := by
      rw [map_mul, ← hgb, hζbar]
    have hmem : gb * gb ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : (gb * gb) * x = x * (gb * gb) := by
        have h := DFunLike.congr_fun hconj x
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        calc
          (gb * gb) * x = (gb * gb) * x * (gb * gb)⁻¹ * (gb * gb) := by group
          _ = x * (gb * gb) := by rw [h]
      exact hx.symm
    have hmem' := hmem
    rw [hcenter] at hmem'
    simpa using hmem'
  have hdvdQ : 2 ^ 7 ∣ Nat.card Q := by
    rw [CFSG.EvenSmallLie.SympSix.card_of_lieModel hQ]
    norm_num
  by_cases hg1 : gb = 1
  · have hfix : fixedSubgroup (centerQuotAut ζ) = ⊤ := by
      rw [hgb, hg1, map_one]
      exact fixedSubgroup_one
    have hcard : Nat.card (fixedSubgroup (centerQuotAut ζ)) = Nat.card Q := by
      rw [hfix, Subgroup.card_top]
    exact dvd_trans (by rw [hcard]; exact hdvdQ) (card_fixed_centerQuotAut_dvd ζ)
  · have hdvdC : 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({gb} : Set Q)) :=
      (sp62_involution_centralizer_card hQ hgg hg1).1
    have hfix : fixedSubgroup (centerQuotAut ζ) =
        Subgroup.centralizer ({gb} : Set Q) := by
      rw [hgb]
      exact fixedSubgroup_conj_eq_centralizer gb
    exact dvd_trans (by rw [hfix]; exact hdvdC) (card_fixed_centerQuotAut_dvd ζ)

theorem IsSp62Cover.four_lt_fixed {K : Type} [Group K] [Finite K] (h : IsSp62Cover K)
    (ζ : MulAut K) (hζ : ζ * ζ = 1) : 4 < Nat.card (fixedSubgroup ζ) := by
  have hpos : 0 < Nat.card (fixedSubgroup ζ) :=
    Nat.card_pos_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  have hle : 2 ^ 7 ≤ Nat.card (fixedSubgroup ζ) :=
    Nat.le_of_dvd hpos (IsSp62Cover.two_pow_dvd_fixed h ζ hζ)
  norm_num at hle ⊢
  omega

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
