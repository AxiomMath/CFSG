module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.HData3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

theorem exists_centralizer_conj_of_isConj (hD3 : HData3 G t z z₁) {a : G}
    (ha : a ∈ centralizer ({t} : Set G)) (ha3 : orderOf a = 3) {s : G} (hs : IsConj t s)
    (hsa : s * a = a * s) : ∃ y : G, y * a = a * y ∧ y * t * y⁻¹ = s := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hs
  have ht_eq : t = g⁻¹ * s * g := by rw [← hg]; group
  have hb_mem : g⁻¹ * a * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ht_eq]
    calc g⁻¹ * a * g * (g⁻¹ * s * g)
        = g⁻¹ * (a * s) * g := by group
      _ = g⁻¹ * (s * a) * g := by rw [← hsa]
      _ = g⁻¹ * s * g * (g⁻¹ * a * g) := by group
  have hb3 : orderOf (g⁻¹ * a * g) = 3 := by
    have hsemi : SemiconjBy g⁻¹ a (g⁻¹ * a * g) := by
      rw [SemiconjBy]; group
    rw [← ha3]
    exact (SemiconjBy.orderOf_eq g⁻¹ hsemi).symm
  obtain ⟨h, hh_mem, hh⟩ := hD3.three_conj (g⁻¹ * a * g) hb_mem a ha hb3 ha3
  have hbh : h⁻¹ * a * h = g⁻¹ * a * g := by
    calc h⁻¹ * a * h
        = h⁻¹ * (h * (g⁻¹ * a * g) * h⁻¹) * h := by rw [hh]
      _ = g⁻¹ * a * g := by group
  have ht_comm : h * t = t * h := mem_centralizer_singleton_iff.mp hh_mem
  have hth : h⁻¹ * t * h = t := by
    rw [mul_assoc, ← ht_comm]; group
  refine ⟨g * h⁻¹, ?_, ?_⟩
  · have hy1 : g * h⁻¹ * a * (g * h⁻¹)⁻¹ = a := by
      calc g * h⁻¹ * a * (g * h⁻¹)⁻¹
          = g * (h⁻¹ * a * h) * g⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [hbh]
        _ = a := by group
    exact mul_inv_eq_iff_eq_mul.mp hy1
  · have hy2 : g * h⁻¹ * t * (g * h⁻¹)⁻¹ = s := by
      calc g * h⁻¹ * t * (g * h⁻¹)⁻¹
          = g * (h⁻¹ * t * h) * g⁻¹ := by group
        _ = g * t * g⁻¹ := by rw [hth]
        _ = s := hg
    exact hy2

theorem card_le_32_of_isConj (hD3 : HData3 G t z z₁) {a : G}
    (ha : a ∈ centralizer ({t} : Set G)) (ha3 : orderOf a = 3) {x : G} (hx : IsConj t x)
    (hxa : x * a = a * x) {R : Subgroup G}
    (hR : R ≤ centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G)) (hR2 : IsPGroup 2 R) :
    Nat.card R ≤ 32 := by
  obtain ⟨y, hya, hyt⟩ := exists_centralizer_conj_of_isConj hD3 ha ha3 hx hxa
  let f : G →* G := (MulAut.conj y⁻¹).toMonoidHom
  have hf : Function.Injective f := fun p q hpq => (MulAut.conj y⁻¹).injective hpq
  have hfx : f x = t := by
    show (MulAut.conj y⁻¹) x = t
    rw [MulAut.conj_apply, inv_inv, ← hyt]
    group
  have hfa : f a = a := by
    show (MulAut.conj y⁻¹) a = a
    rw [MulAut.conj_apply, inv_inv]
    calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
      _ = y⁻¹ * (y * a) := by rw [← hya]
      _ = a := by group
  have hR'le : R.map f ≤ centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G) := by
    intro r' hr'
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hr'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hm : f r ∈ (centralizer ({x} : Set G)).map f :=
        ⟨r, (Subgroup.mem_inf.mp (hR hrR)).1, rfl⟩
      have h := Subgroup.map_centralizer_le_centralizer_image ({x} : Set G) f hm
      rwa [Set.image_singleton, hfx] at h
    · have hm : f r ∈ (centralizer ({a} : Set G)).map f :=
        ⟨r, (Subgroup.mem_inf.mp (hR hrR)).2, rfl⟩
      have h := Subgroup.map_centralizer_le_centralizer_image ({a} : Set G) f hm
      rwa [Set.image_singleton, hfa] at h
  have hR'card : Nat.card (R.map f) = Nat.card R := Subgroup.card_map_of_injective (f := f) hf
  have hR'2 : IsPGroup 2 (R.map f) := hR2.map f
  have hKcard : Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G)) = 1440 :=
    hD3.card_C3 a ha ha3
  have hdvd : Nat.card (R.map f) ∣ 1440 := by
    rw [← hKcard]
    exact Subgroup.card_dvd_of_le hR'le
  have hne : Nat.card (R.map f) ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hdvd
    exact absurd hdvd (by norm_num)
  haveI : Finite ↥(R.map f) := Nat.finite_of_card_ne_zero hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hR'2.exists_card_eq
  have hk5 : k ≤ 5 := by
    have hdvd2 : 2 ^ k ∣ 2 ^ 5 * 45 := by
      have h1440 : (2:ℕ) ^ 5 * 45 = 1440 := by norm_num
      rw [← h1440, hk] at hdvd
      exact hdvd
    have hcop : Nat.Coprime (2 ^ k) 45 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; norm_num
      · rw [Nat.coprime_pow_left_iff hkpos]; norm_num
    have h25 : 2 ^ k ∣ 2 ^ 5 := hcop.dvd_of_dvd_mul_right hdvd2
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h25
  calc Nat.card R = Nat.card (R.map f) := hR'card.symm
    _ = 2 ^ k := hk
    _ ≤ 2 ^ 5 := pow_le_pow_right' (by norm_num : (1:ℕ) ≤ 2) hk5
    _ = 32 := by norm_num

theorem isConj_iff_tTG (hD : HData G t z b z₁ S Eg T T' W0 ι)
    (hconj : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) {u : G}
    (hu : u ∈ centralizer ({t} : Set G)) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    IsConj t u ↔ tTG t z z₁ u := by
  classical
  obtain ⟨vz, hzv, hzlam, hzqm⟩ := hD.coords_z
  obtain ⟨vb, hbv, hblam, hbqm⟩ := hD.coords_b
  obtain ⟨vz1, hz1v, hz1lam, hz1qm⟩ := hD.coords_z₁
  have hqp_vz : qp vz = 0 := by
    rw [show qp vz = qm vz + lam vz from rfl, hzqm, hzlam]; decide
  have hqp_vb : qp vb = 0 := by
    rw [show qp vb = qm vb + lam vb from rfl, hbqm, hblam]; decide
  have hqp_vz1 : qp vz1 = 1 := by
    rw [show qp vz1 = qm vz1 + lam vz1 from rfl, hz1qm, hz1lam]; decide
  have hqp_tv : qp tv = 1 := by decide +kernel
  have hbil_tv_vz : bil tv vz = 0 := by rw [bil_comm, ← lam_eq_bil, hzlam]
  have hqp_tv_vz : qp (tv + vz) = 1 := by
    rw [qp_add, hqp_tv, hqp_vz, hbil_tv_vz]; decide
  have htz : t * z = coordElt ι (tv + vz) := by
    rw [coordElt_add, hD.ι_tv, hzv]
  have hconj_tz : IsConj t (t * z) := by
    rw [htz]; exact (hconj (tv + vz)).mpr hqp_tv_vz
  have hconj_z1 : IsConj t z₁ := by
    rw [← hz1v]; exact (hconj vz1).mpr hqp_vz1
  constructor
  ·
    intro hu_conj
    by_cases huE : u ∈ Eg
    · by_cases hut : u = t
      · refine Or.inl ⟨1, Subgroup.one_mem _, ?_⟩
        rw [hut]; simp
      · obtain ⟨h, hh, hhz | hhtz⟩ := hD.inv_E u huE hu2 hu1 hut
        · exfalso
          have hzconj : IsConj t z := hu_conj.trans (isConj_iff.mpr ⟨h, hhz⟩)
          have hq : qp vz = 1 := (hconj vz).mp (by rw [hzv]; exact hzconj)
          rw [hqp_vz] at hq
          exact absurd hq (by decide)
        · exact Or.inr (Or.inl ⟨h, hh, hhtz⟩)
    · obtain ⟨h, hh, hhb | hhz1⟩ := hD.inv_outer u hu hu2 huE
      · exfalso
        have hbconj : IsConj t b := hu_conj.trans (isConj_iff.mpr ⟨h, hhb⟩)
        have hq : qp vb = 1 := (hconj vb).mp (by rw [hbv]; exact hbconj)
        rw [hqp_vb] at hq
        exact absurd hq (by decide)
      · exact Or.inr (Or.inr ⟨h, hh, hhz1⟩)
  ·
    rintro (⟨h, _, hh'⟩ | ⟨h, _, hh'⟩ | ⟨h, _, hh'⟩)
    · exact (isConj_iff.mpr ⟨h, hh'⟩).symm
    · exact hconj_tz.trans (isConj_iff.mpr ⟨h, hh'⟩).symm
    · exact hconj_z1.trans (isConj_iff.mpr ⟨h, hh'⟩).symm

end CFSG.EvenSporadicStandard.HNRecog.Harada
