module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.PGroup

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

theorem harada_exists_u [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hD : HData G t z b z₁ S Eg T T' W0 ι) :
    ∃ u : G, u ∈ normalizer (S : Set G) ∧ u ∉ S ∧ u ^ 2 ∈ S ∧ u * t * u⁻¹ = t * z ∧
      u * z * u⁻¹ = z ∧ Nat.card ↥(S ⊔ Subgroup.zpowers u) = 2 ^ 12 := by
  obtain ⟨Q, hQ, hSQ⟩ :=
    exists_isPGroup_gt_of_two_dvd_index hD.isPGroup_S (harada_prop_2_1 hnonab hD)
  obtain ⟨u, huQ, hun, huS, hu2⟩ := exists_mem_normalizer_sq_mem hQ hSQ
  have hcard : Nat.card ↥(S ⊔ Subgroup.zpowers u) = 2 * Nat.card S :=
    card_sup_zpowers_of_sq_mem hun huS hu2
  have hcard12 : Nat.card ↥(S ⊔ Subgroup.zpowers u) = 2 ^ 12 := by
    rw [hcard, hD.card_S]
    norm_num
  have hne : u * t * u⁻¹ ≠ t := by
    intro hfix
    have huc : u ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc u * t = (u * t * u⁻¹) * u := by group
        _ = t * u := by rw [hfix]
    have hPc : S ⊔ Subgroup.zpowers u ≤ centralizer ({t} : Set G) :=
      sup_le hD.S_le_centralizer (Subgroup.zpowers_le.mpr huc)
    have hPQ : S ⊔ Subgroup.zpowers u ≤ Q :=
      sup_le (le_of_lt hSQ) (Subgroup.zpowers_le.mpr huQ)
    have hP : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers u) := hQ.to_le hPQ
    have hK : Nat.card (centralizer ({t} : Set G)) = 2 ^ 11 * (3 ^ 2 * 5 ^ 3 * 7 * 11) := by
      rw [hD.card_H]
      ring
    have hdvd : Nat.card ↥(S ⊔ Subgroup.zpowers u) ∣ 2 ^ 11 :=
      card_dvd_of_isPGroup_le hP hPc hK (by norm_num)
    have hbad : 2 ^ 12 ∣ 2 ^ 11 := by
      rw [← hcard12]
      exact hdvd
    have hle : 2 ^ 12 ≤ 2 ^ 11 := Nat.le_of_dvd (by norm_num) hbad
    norm_num at hle
  refine ⟨u, hun, huS, hu2, ?_, ?_, hcard12⟩
  · exact HarCoreData.conj_t_eq hD.core hun hne
  · exact HarCoreData.conj_z_eq hD.core hun

theorem harada_not_isConj_t_z [Finite G] (hD : HData G t z b z₁ S Eg T T' W0 ι) {u : G}
    (hu : u ∈ normalizer (S : Set G)) (huz : u * z * u⁻¹ = z)
    (hcard : Nat.card ↥(S ⊔ Subgroup.zpowers u) = 2 ^ 12) : ¬ IsConj t z := by
  intro hconj
  rw [isConj_iff] at hconj
  obtain ⟨c, hc⟩ := hconj
  have hP : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers u) := IsPGroup.of_card hcard
  have hPc : S ⊔ Subgroup.zpowers u ≤ centralizer ({z} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [mem_centralizer_singleton_iff]
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [HarCoreData.z_central hD.core hx]
    · rw [Subgroup.zpowers_le, mem_centralizer_singleton_iff]
      calc u * z = (u * z * u⁻¹) * u := by group
        _ = z * u := by rw [huz]
  set P' : Subgroup G := (S ⊔ Subgroup.zpowers u).map (MulAut.conj c⁻¹).toMonoidHom with hP'def
  have hP' : IsPGroup 2 P' := by
    rw [hP'def]
    exact isPGroup_map_conj hP c⁻¹
  have hcard' : Nat.card P' = 2 ^ 12 := by
    rw [hP'def, Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
      (MulAut.conj c⁻¹).injective, hcard]
  have hP'c : P' ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    rw [hP'def, Subgroup.mem_map] at hx
    rcases hx with ⟨p, hp, rfl⟩
    have hpz : p * z = z * p := mem_centralizer_singleton_iff.mp (hPc hp)
    have ht : t = c⁻¹ * z * c := by rw [← hc]; group
    rw [ht]
    calc (MulAut.conj c⁻¹).toMonoidHom p * (c⁻¹ * z * c)
        = c⁻¹ * p * c * (c⁻¹ * z * c) := by
          simp only [MulAut.conj_apply, inv_inv, MulEquiv.coe_toMonoidHom]
      _ = c⁻¹ * (p * z) * c := by group
      _ = c⁻¹ * (z * p) * c := by rw [hpz]
      _ = (c⁻¹ * z * c) * (MulAut.conj c⁻¹).toMonoidHom p := by
          simp only [MulAut.conj_apply, inv_inv, MulEquiv.coe_toMonoidHom]
          group
  have hK : Nat.card (centralizer ({t} : Set G)) = 2 ^ 11 * (3 ^ 2 * 5 ^ 3 * 7 * 11) := by
    rw [hD.card_H]
    ring
  have hdvd : Nat.card P' ∣ 2 ^ 11 := card_dvd_of_isPGroup_le hP' hP'c hK (by norm_num)
  have hbad : 2 ^ 12 ∣ 2 ^ 11 := by
    rw [← hcard']
    exact hdvd
  have hle : 2 ^ 12 ≤ 2 ^ 11 := Nat.le_of_dvd (by norm_num) hbad
  norm_num at hle

theorem harada_exists_outer_conj [Finite G] (hD : HData G t z b z₁ S Eg T T' W0 ι) {u : G}
    (hu : u ∈ normalizer (S : Set G)) (hut : u * t * u⁻¹ = t * z) :
    ∃ w ∈ S, w ∉ Eg ∧ w ^ 2 = 1 ∧ IsConj t w := by
  obtain ⟨i, hiT, hi2, hiE⟩ := HarCoreData.exists_invol_conj_not_mem hD.core hu hut
  have hiS : i ∈ S := HarCoreData.T_le_S hD.core hiT
  have hiEg : i ∈ Eg := HarCoreData.T_le_Eg hD.core hiT
  have htT : t ∈ T := hD.core.t_mem
  have hzT : z ∈ T := hD.core.z1_mem
  have htEg : t ∈ Eg := HarCoreData.T_le_Eg hD.core htT
  have hzEg : z ∈ Eg := HarCoreData.T_le_Eg hD.core hzT
  have htzEg : t * z ∈ Eg := Eg.mul_mem htEg hzEg
  have hi1 : i ≠ 1 := by
    intro h
    apply hiE
    rw [h]
    simp
  have hit : i ≠ t := by
    intro h
    apply hiE
    rw [h, hut]
    exact htzEg
  have httz : IsConj t (t * z) := isConj_iff.mpr ⟨u, hut⟩
  obtain ⟨h, hh, hhi⟩ := hD.inv_E i hiEg hi2 hi1 hit
  have hht : h * t = t * h := mem_centralizer_singleton_iff.mp hh
  rcases hhi with hhi | hhi
  ·
    have hitcomm : Commute i t := hD.core.S_comm_t i hiS
    have hitS : i * t ∈ S := S.mul_mem hiS (HarCoreData.T_le_S hD.core htT)
    have hit2 : (i * t) ^ 2 = 1 := by
      rw [hitcomm.mul_pow 2, hi2, hD.core.t_sq]
      simp
    have hhconj : h * (i * t) * h⁻¹ = t * z := by
      calc h * (i * t) * h⁻¹ = (h * i * h⁻¹) * (h * t * h⁻¹) := by group
        _ = z * t := by
              rw [hhi, show h * t * h⁻¹ = t from by rw [hht]; group]
        _ = t * z := hD.core.z1_comm t htT
    have hitconj : IsConj t (i * t) :=
      httz.trans (IsConj.symm (isConj_iff.mpr ⟨h, hhconj⟩))
    refine ⟨u * (i * t) * u⁻¹, (mem_normalizer_iff.mp hu (i * t)).mp hitS, ?_, ?_, ?_⟩
    · intro hwE
      apply hiE
      have hw_eq : u * (i * t) * u⁻¹ = (u * i * u⁻¹) * (t * z) := by
        calc u * (i * t) * u⁻¹ = (u * i * u⁻¹) * (u * t * u⁻¹) := by group
          _ = (u * i * u⁻¹) * (t * z) := by rw [hut]
      have hrepr : u * i * u⁻¹ = (u * (i * t) * u⁻¹) * (t * z)⁻¹ := by
        rw [hw_eq]
        group
      rw [hrepr]
      exact Eg.mul_mem hwE (Eg.inv_mem htzEg)
    · rw [conj_pow, hit2]
      group
    · exact hitconj.trans (isConj_iff.mpr ⟨u, rfl⟩)
  ·
    have hti : IsConj t i := httz.trans (IsConj.symm (isConj_iff.mpr ⟨h, hhi⟩))
    refine ⟨u * i * u⁻¹, (mem_normalizer_iff.mp hu i).mp hiS, hiE, ?_, ?_⟩
    · rw [conj_pow, hi2]
      group
    · exact hti.trans (isConj_iff.mpr ⟨u, rfl⟩)

theorem harada_lemma_2_2 [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hD : HData G t z b z₁ S Eg T T' W0 ι) :
    ∃ u : G, u ∈ normalizer (S : Set G) ∧ u ∉ S ∧ u ^ 2 ∈ S ∧ u * t * u⁻¹ = t * z ∧
      u * z * u⁻¹ = z ∧ Nat.card ↥(S ⊔ Subgroup.zpowers u) = 2 ^ 12 ∧ ¬ IsConj t z ∧
      ∃ w ∈ S, w ∉ Eg ∧ w ^ 2 = 1 ∧ IsConj t w := by
  obtain ⟨u, hu, hu', hu2, hut, huz, hcard⟩ := harada_exists_u hnonab hD
  exact ⟨u, hu, hu', hu2, hut, huz, hcard, harada_not_isConj_t_z hD hu huz hcard,
    harada_exists_outer_conj hD hu hut⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
