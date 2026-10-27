module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem perp_card_of_shape {X : Type*} [Group X] (h : IsShapeTwoOneSixByFive X) :
    Nat.card X = 640 := by
  obtain ⟨N, hN, hNcard, hquot⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hquot, hNcard]
  norm_num

theorem perp_mem_pCoreOf_of_shape {X : Subgroup G} (hX : IsShapeTwoOneSixByFive ↥X) {x : G}
    (hx : x ∈ X) (hx2 : x ^ 2 = 1) : x ∈ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨N, hN, hNcard, hquot⟩ := hX
  haveI : N.Normal := hN
  have hNp : IsPGroup 2 N := IsPGroup.of_card hNcard
  have hNle : N ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hN, hNp⟩
  let x' : ↥X := ⟨x, hx⟩
  have hx'2 : x' ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  have hq1 : QuotientGroup.mk' N x' = 1 := by
    have hq2 : (QuotientGroup.mk' N x') ^ 2 = 1 := by
      rw [← map_pow, hx'2, map_one]
    have hdvd2 : orderOf (QuotientGroup.mk' N x') ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
    have hdvd5 : orderOf (QuotientGroup.mk' N x') ∣ 5 := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk' N x')
      rwa [hquot] at h
    have horder : orderOf (QuotientGroup.mk' N x') = 1 := by
      have h := Nat.dvd_gcd hdvd2 hdvd5
      rw [show Nat.gcd 2 5 = 1 by norm_num] at h
      exact Nat.dvd_one.mp h
    rwa [orderOf_eq_one_iff] at horder
  have hx'N : x' ∈ N := (QuotientGroup.eq_one_iff x').mp hq1
  have hx'p : x' ∈ CFSG.pCore 2 ↥X := hNle hx'N
  change x ∈ (CFSG.pCore 2 ↥X).map X.subtype
  exact Subgroup.mem_map.mpr ⟨x', hx'p, rfl⟩

theorem perp_Gxy_eq_Gxyz (a c : G) : Gxy a c = Gxyz a ((a * c) ^ 2) c := by
  ext g
  simp only [mem_Gxy, mem_Gxyz, mem_Gx]
  constructor
  · rintro ⟨ha, hc⟩
    exact ⟨ha,
      ((show Commute a g from ha).mul_left (show Commute c g from hc)).pow_left 2, hc⟩
  · rintro ⟨ha, _, hc⟩
    exact ⟨ha, hc⟩

theorem perp_mem_Qz_of_orb4A (hI : TwoHSInterface) {a z c : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hc : c ∈ orb4A a z a) :
    a ∈ Qz ((a * c) ^ 2) ∧ c ∈ Qz ((a * c) ^ 2) := by
  have hc' : IsConj a c ∧ IsConj z ((a * c) ^ 2) := hc
  obtain ⟨hcA, hcz⟩ := hc'
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hc2 : c ^ 2 = 1 := by
    have hco : orderOf c = 2 := perp_orderOf_of_isConj_a h hcA
    rw [← hco]
    exact pow_orderOf_eq_one c
  have hz2 : ((a * c) ^ 2) ^ 2 = 1 := by
    have hzo : orderOf ((a * c) ^ 2) = 2 := perp_orderOf_of_isConj_z h hcz
    have h := pow_orderOf_eq_one ((a * c) ^ 2)
    rw [hzo] at h
    exact h
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hcc : c * c = 1 := by simpa [pow_two] using hc2
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hca_inv : (c * a)⁻¹ = a * c := by rw [mul_inv_rev, ha_inv, hc_inv]
  have hat_eq : a * (a * c) ^ 2 = c * a * c := by
    calc a * (a * c) ^ 2 = a * ((a * c) * (a * c)) := by rw [pow_two]
      _ = (a * (a * c)) * (a * c) := (mul_assoc _ _ _).symm
      _ = ((a * a) * c) * (a * c) := by rw [← mul_assoc a a c]
      _ = (1 * c) * (a * c) := by rw [haa]
      _ = c * (a * c) := by rw [one_mul]
      _ = c * a * c := (mul_assoc c a c).symm
  have hct_eq : c * (a * c) ^ 2 = (c * a) * c * (c * a)⁻¹ := by
    rw [hca_inv]
    calc c * (a * c) ^ 2 = c * ((a * c) * (a * c)) := by rw [pow_two]
      _ = (c * (a * c)) * (a * c) := (mul_assoc _ _ _).symm
      _ = ((c * a) * c) * (a * c) := by rw [← mul_assoc c a c]
      _ = (c * a) * c * (a * c) := rfl
  have hat2 : (a * (a * c) ^ 2) ^ 2 = 1 := by
    have hcac : c * a * c = MulAut.conj c a := by rw [MulAut.conj_apply, hc_inv]
    rw [hat_eq, hcac, ← map_pow, ha2, map_one]
  have hct2 : (c * (a * c) ^ 2) ^ 2 = 1 := by
    rw [hct_eq]
    change (MulAut.conj (c * a) c) ^ 2 = 1
    rw [← map_pow, hc2, map_one]
  have hat_comm : a * (a * c) ^ 2 = (a * c) ^ 2 * a := comm_of_sq_mul ha2 hz2 hat2
  have hct_comm : c * (a * c) ^ 2 = (a * c) ^ 2 * c := comm_of_sq_mul hc2 hz2 hct2
  have hata_conj : IsConj a (a * (a * c) ^ 2) := by
    refine isConj_iff.mpr ⟨c, ?_⟩
    rw [hat_eq, hc_inv]
  have hctc_conj : IsConj c (c * (a * c) ^ 2) := by
    refine isConj_iff.mpr ⟨c * a, ?_⟩
    rw [hct_eq]
  have hcta_conj : IsConj a (c * (a * c) ^ 2) := hcA.trans hctc_conj
  exact ⟨mem_Qz_of_isConj_mul hI h hF1 (IsConj.refl a) hcz hat_comm hata_conj,
    mem_Qz_of_isConj_mul hI h hF1 hcA hcz hct_comm hcta_conj⟩

theorem perp_shape_of_mem_orb4A (hI : TwoHSInterface) {a z c : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hT3 : Vert TableIIIFacts a z) (hc : c ∈ orb4A a z a) :
    IsShapeTwoOneSixByFive ↥(Gxy a c) := by
  have hc' : IsConj a c ∧ IsConj z ((a * c) ^ 2) := hc
  obtain ⟨hcA, hcz⟩ := hc'
  obtain ⟨hQa, hQc⟩ := perp_mem_Qz_of_orb4A hI h hF1 hc
  have hz2 : orderOf ((a * c) ^ 2) = 2 := perp_orderOf_of_isConj_z h hcz
  have hzsq : ((a * c) ^ 2) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one ((a * c) ^ 2)
    rw [hz2] at h
    exact h
  have hz_ne : (a * c) ^ 2 ≠ 1 := by
    intro h1
    have : orderOf ((a * c) ^ 2) = 1 := by rw [h1, orderOf_one]
    omega
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hcne_a : c ≠ a := by
    intro hca
    apply hz_ne
    rw [hca, haa]
    simp
  have hcne_at : c ≠ a * (a * c) ^ 2 := by
    intro hca'
    apply hz_ne
    set t : G := (a * c) ^ 2 with ht
    have h1 : a * c = t := by
      rw [hca', ← mul_assoc, haa, one_mul]
    have ht2 : t ^ 2 = 1 := by rw [ht]; exact hzsq
    calc t = (a * c) ^ 2 := ht
      _ = (a * c) * (a * c) := pow_two _
      _ = t * t := by rw [h1]
      _ = t ^ 2 := (pow_two t).symm
      _ = 1 := ht2
  have hcmem : c ∈ tab3Set a ((a * c) ^ 2) a 2 := by
    show c ∈ tab3Base a ((a * c) ^ 2) a ∧ (a * c) ^ 2 = (a * c) ^ 2
    exact ⟨⟨hQc, hcA, hcne_a, hcne_at⟩, rfl⟩
  have hshape : IsShapeTwoOneSixByFive ↥(Gxyz a ((a * c) ^ 2) c) :=
    (hT3 a ((a * c) ^ 2) (IsConj.refl a) hcz).shape_4A a hQa (IsConj.refl a) c hcmem
  rw [perp_Gxy_eq_Gxyz a c]
  exact hshape

end CFSG.EvenSporadicStandard.HNRecog.Section3
