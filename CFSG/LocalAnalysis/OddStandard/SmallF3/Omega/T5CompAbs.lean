module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem t5_isL29_card_two_adic {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (h : IsL29 J) : 8 ∣ Nat.card J ∧ ¬ 16 ∣ Nat.card J := by
  have hcard : Nat.card J = Nat.card (↥J ⧸ oddCore ↥J) * Nat.card (oddCore ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore ↥J)
  rw [ff_card_isL29 h] at hcard
  obtain ⟨k, hk⟩ := ff_odd_card_oddCore ↥J
  constructor
  · rw [hcard, hk]
    exact dvd_mul_of_dvd_left (by norm_num : 8 ∣ 360) (2 * k + 1)
  · rw [hcard, hk]
    intro h16
    have h2 : 2 ∣ 45 * (2 * k + 1) := by
      have h' : 8 * 2 ∣ 8 * (45 * (2 * k + 1)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h16
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8) h'
    rcases (Nat.prime_two.dvd_mul).mp h2 with h | h
    · omega
    · exact Nat.not_two_dvd_bit1 k h

theorem t5_isOmega5_simple {G : Type} [Group G] {X : Subgroup G} (h : IsOmega5 X) :
    IsSimpleGroup (↥X ⧸ CFSG.oddCore ↥X) ∧ 16 ∣ Nat.card (↥X ⧸ CFSG.oddCore ↥X) := by
  refine ⟨(ff_simple_of_lieModel_psp h).1, ?_⟩
  rw [ff_card_isOmega5 h]
  norm_num

theorem t5_image_dichotomy {E F : Type} [Group E] [Group F] (f : E →* F)
    (hf : Function.Surjective f) (hX : IsSimpleGroup (F ⧸ CFSG.oddCore F)) {J : Subgroup E}
    (hJ : J.Normal) : J.map f ≤ CFSG.oddCore F ∨ J.map f ⊔ CFSG.oddCore F = ⊤ := by
  let π : F →* F ⧸ CFSG.oddCore F := QuotientGroup.mk' (CFSG.oddCore F)
  have hN : ((J.map f).map π).Normal :=
    (hJ.map f hf).map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((J.map f).map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hsup := Subgroup.comap_map_eq (f := π) (J.map f)
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at hsup
    exact hsup.symm

theorem t5_comp_false_of_simple_image {N F : Type} [Group N] [Group F] [Finite N] [Finite F]
    (f : N →* F) (hker : Nat.card f.ker ∣ 2) {E J : Subgroup N} (hJE : J ≤ E)
    (hJ : (J.subgroupOf E).Normal)
    (hX : IsSimpleGroup (↥(E.map f) ⧸ CFSG.oddCore ↥(E.map f)))
    (h16 : 16 ∣ Nat.card (↥(E.map f) ⧸ CFSG.oddCore ↥(E.map f)))
    (h8 : 8 ∣ Nat.card J) (h16' : ¬ 16 ∣ Nat.card J) : False := by
  let E' := E.map f
  let f' : ↥E →* ↥E' := f.subgroupMap E
  let J' : Subgroup ↥E := J.subgroupOf E
  have hf' : Function.Surjective f' := f.subgroupMap_surjective E
  have hcardJ : Nat.card J' = Nat.card J := by
    have h := Subgroup.card_subtype E J'
    rw [Subgroup.map_subgroupOf_eq_of_le hJE] at h
    exact h.symm
  have hker_le : f'.ker.map E.subtype ≤ f.ker := by
    rintro x ⟨y, hy, rfl⟩
    have hy' : f' y = 1 := MonoidHom.mem_ker.mp hy
    have hy'' : f ((y : ↥E) : N) = 1 := congrArg Subtype.val hy'
    simpa using hy''
  have hkercard : Nat.card f'.ker ∣ Nat.card f.ker := by
    rw [← Subgroup.card_map_of_injective (f := E.subtype) (K := f'.ker) E.subtype_injective]
    exact Subgroup.card_dvd_of_le hker_le
  have hker2 : Nat.card f'.ker ∣ 2 := hkercard.trans hker
  have hformula : Nat.card (J'.map f') * Nat.card ↥(f'.ker ⊓ J') = Nat.card J' := by
    rw [← Subgroup.relIndex_ker (f := f') (K := J')]
    exact Subgroup.relIndex_mul_card (H := f'.ker) (K := J')
  have h8' : 8 ∣ Nat.card J' := hcardJ.symm ▸ h8
  have h16'' : ¬ 16 ∣ Nat.card J' := by
    rw [hcardJ]
    exact h16'
  rcases t5_image_dichotomy f' hf' hX hJ with hle | htop
  · have hdvdodd : Nat.card (J'.map f') ∣ Nat.card (CFSG.oddCore ↥E') :=
      Subgroup.card_dvd_of_le hle
    have hoddimg : Odd (Nat.card (J'.map f')) :=
      (ff_odd_card_oddCore ↥E').of_dvd_nat hdvdodd
    have hd : Nat.card ↥(f'.ker ⊓ J') ∣ 2 :=
      (Subgroup.card_dvd_of_le (inf_le_left : f'.ker ⊓ J' ≤ f'.ker)).trans hker2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hd1 | hd2
    · have hJ'card : Nat.card J' = Nat.card (J'.map f') := by
        rw [← hformula, hd1, mul_one]
      have hoddJ' : Odd (Nat.card J') := hJ'card.symm ▸ hoddimg
      exact hoddJ'.not_two_dvd_nat ((by norm_num : 2 ∣ 8).trans h8')
    · have hJ'card : Nat.card J' = 2 * Nat.card (J'.map f') := by
        rw [← hformula, hd2, mul_comm]
      have h4 : 4 ∣ Nat.card (J'.map f') := by
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (hJ'card ▸ h8')
      exact hoddimg.not_two_dvd_nat ((by norm_num : 2 ∣ 4).trans h4)
  · have hsurj : Function.Surjective
        ((QuotientGroup.mk' (CFSG.oddCore ↥E')).comp (J'.map f').subtype) := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥E') x
      have hy : (y : ↥E') ∈ J'.map f' ⊔ CFSG.oddCore ↥E' := by
        rw [htop]
        exact Subgroup.mem_top y
      rw [Subgroup.mem_sup_of_normal_right (s := J'.map f') (t := CFSG.oddCore ↥E')] at hy
      obtain ⟨a, ha, b, hb, hab⟩ := hy
      refine ⟨⟨a, ha⟩, ?_⟩
      show QuotientGroup.mk' (CFSG.oddCore ↥E') a = QuotientGroup.mk' (CFSG.oddCore ↥E') y
      rw [QuotientGroup.mk'_eq_mk']
      exact ⟨b, hb, hab⟩
    have hdvd1 : Nat.card (↥E' ⧸ CFSG.oddCore ↥E') ∣ Nat.card (J'.map f') :=
      Subgroup.card_dvd_of_surjective hsurj
    have hdvd2 : Nat.card (J'.map f') ∣ Nat.card J' :=
      Subgroup.card_map_dvd (H := J') (f := f')
    exact h16'' (h16.trans (hdvd1.trans hdvd2))

end CFSG.OddStandard.SmallF3.Omega
