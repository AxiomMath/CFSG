module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightDecomp

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

theorem mem_or_mem_or_mul_mem_of_index_le_two {X : Type*} [Group X] {C : Subgroup X}
    (hC : C.index ≤ 2) (hC0 : C.index ≠ 0) (a b : X) : a ∈ C ∨ b ∈ C ∨ a * b ∈ C := by
  rcases (show C.index = 1 ∨ C.index = 2 by omega) with h | h
  · rw [Subgroup.index_eq_one.mp h]
    exact Or.inl (Subgroup.mem_top a)
  · by_cases ha : a ∈ C
    · exact Or.inl ha
    by_cases hb : b ∈ C
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr ((Subgroup.mul_mem_iff_of_index_two h).mpr (iff_of_false ha hb)))

theorem index_centralizer_le_two_of_conj {X : Type*} [Group X] {t u : X}
    (hu : u ≠ 1) (huu : u * u = 1) (huc : ∀ a : X, a * u = u * a)
    (h : ∀ a : X, a * t * a⁻¹ = t ∨ a * t * a⁻¹ = t * u) :
    (Subgroup.centralizer ({t} : Set X)).index ≤ 2 := by
  have hmem : ∀ a : X, a ∈ Subgroup.centralizer ({t} : Set X) ↔ a * t * a⁻¹ = t := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  by_cases htop : ∀ a : X, a ∈ Subgroup.centralizer ({t} : Set X)
  · rw [show Subgroup.centralizer ({t} : Set X) = ⊤ from eq_top_iff.mpr fun a _ => htop a,
      Subgroup.index_top]
    omega
  push Not at htop
  obtain ⟨a₀, ha₀⟩ := htop
  have ha₀t : a₀ * t * a₀⁻¹ = t * u := (h a₀).resolve_left fun h' => ha₀ ((hmem a₀).mpr h')
  have htu : t * u ≠ t := fun h' => hu (mul_eq_left.mp h')
  have hconj : ∀ b : X, b * a₀ * t * (b * a₀)⁻¹ = b * t * b⁻¹ * u := by
    intro b
    calc b * a₀ * t * (b * a₀)⁻¹ = b * (a₀ * t * a₀⁻¹) * b⁻¹ := by group
      _ = b * t * (u * b⁻¹) := by rw [ha₀t]; group
      _ = b * t * b⁻¹ * u := by rw [← huc b⁻¹]; group
  refine le_of_eq (Subgroup.index_eq_two_iff.mpr ⟨a₀, fun b => ?_⟩)
  rw [hmem, hmem, hconj]
  rcases h b with hb | hb
  · rw [hb]
    exact Or.inr ⟨rfl, htu⟩
  · rw [hb, mul_assoc, huu, mul_one]
    exact Or.inl ⟨rfl, htu⟩

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)} [J.Normal]

namespace SzEightSetting

variable (hs : SzEightSetting S H z J)
  (e : (J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))
  {φ : (S : Subgroup G) →* J ⧸ Subgroup.center J} (hφ : IsInnerPart hs.central φ)
include hs e hφ

theorem exists_conj_mem_inCenterOf :
    ∃ t : (S : Subgroup G), ∃ ht : sylowBar hs.central t ∈ J,
      InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _))
        ((⟨_, ht⟩ : J) : J ⧸ Subgroup.center J) ∧
      (⟨_, ht⟩ : J) ∉ Subgroup.center J ∧ t * t = 1 ∧ IsConj (t : G) z := by
  have hq := hs.quotientData
  obtain ⟨v, hzv, hv2, hvbar⟩ := exists_isConj_mk_ne_bar hs.square.core.simple
    hs.square.core.nonabelian hs.central.2.1
  have hv2' : orderOf v = 2 := by rwa [← Subgroup.orderOf_coe]
  have hvb2 : orderOf (escapingMk z v) = 2 := escaping_orderOf_mk z hv2'
  obtain ⟨m, hm⟩ := exists_conj_mem_sylow_of_pow (sylowBarSylow hs.central) (n := 1)
    (x := escapingMk z v) (by
      rw [pow_one]
      have h := pow_orderOf_eq_one (escapingMk z v)
      rwa [hvb2] at h)
  rw [coe_sylowBarSylow] at hm
  obtain ⟨t, ht⟩ := hm
  have htb2 : orderOf (sylowBar hs.central t) = 2 := by
    rw [ht]
    simpa only [MulAut.conj_apply] using ((MulAut.conj m).orderOf_eq _).trans hvb2
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ (sylowBar_injective hs.central) t, htb2]
  have htt : t * t = 1 := by
    rw [← pow_two]
    have h2 := pow_orderOf_eq_one t
    rwa [ht2] at h2
  obtain ⟨htJ, htc⟩ := hs.inCenterOf_of_mul_self e hφ htt
  refine ⟨t, htJ, htc, ?_, htt, ?_⟩
  · rw [hs.mem_center_iff]
    rintro (h | h)
    · change sylowBar hs.central t = 1 at h
      rw [h, orderOf_one] at htb2
      exact absurd htb2 (by decide)
    · change sylowBar hs.central t = escapingBar z at h
      apply hvbar
      rw [ht] at h
      rw [show escapingMk z v = m⁻¹ * (m * escapingMk z v * m⁻¹) * m by group, h,
        (hq.commute_bar m⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
  · have hconj : IsConj (escapingMk z v) (escapingMk z ⟨t, hs.central.le_centralizer t.2⟩) := by
      change IsConj (escapingMk z v) (sylowBar hs.central t)
      rw [ht]
      exact isConj_iff.mpr ⟨m, rfl⟩
    have ht2' : orderOf (⟨t, hs.central.le_centralizer t.2⟩ :
        Subgroup.centralizer ({z} : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      exact ht2
    have h := escaping_isConj_of_isConj_mk z hv2' ht2' hconj
    exact (hzv.trans (MonoidHom.map_isConj (Subgroup.centralizer ({z} : Set G)).subtype h)).symm

omit e in
theorem conj_eq_or_eq_mul {t : (S : Subgroup G)} (htJ : sylowBar hs.central t ∈ J)
    (htc : InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _))
      ((⟨_, htJ⟩ : J) : J ⧸ Subgroup.center J)) (a : (S : Subgroup G)) :
    a * t * a⁻¹ = t ∨ a * t * a⁻¹ = t * ⟨z, hs.central.1⟩ := by
  obtain ⟨q, hqJ, -, hk⟩ := hφ.exists_mul a
  set k := sylowBar hs.central (q⁻¹ * a) with hkdef
  have hak : sylowBar hs.central a = sylowBar hs.central q * k := by
    rw [hkdef, map_mul, map_inv, mul_inv_cancel_left]
  have hkt : k * sylowBar hs.central t = sylowBar hs.central t * k :=
    (Subgroup.mem_centralizer_iff.mp hk _ htJ).symm
  have hqt : ((⟨_, hqJ⟩ : J) : J ⧸ Subgroup.center J) * ((⟨_, htJ⟩ : J) : J ⧸ _) =
      ((⟨_, htJ⟩ : J) : J ⧸ _) * ((⟨_, hqJ⟩ : J) : J ⧸ _) :=
    (htc.2 _ ⟨⟨_, hqJ⟩, hs.mem_sylowJ_sylowBar hqJ, rfl⟩).eq
  have hc : (⟨_, htJ⟩ : J)⁻¹ * (⟨_, hqJ⟩ * ⟨_, htJ⟩ * (⟨_, hqJ⟩ : J)⁻¹) ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      hqt, mul_inv_cancel_right]
  have hconj : sylowBar hs.central (a * t * a⁻¹) =
      sylowBar hs.central q * sylowBar hs.central t * (sylowBar hs.central q)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hak]
    calc sylowBar hs.central q * k * sylowBar hs.central t * (sylowBar hs.central q * k)⁻¹
        = sylowBar hs.central q * (k * sylowBar hs.central t) * k⁻¹ *
          (sylowBar hs.central q)⁻¹ := by group
      _ = _ := by rw [hkt]; group
  rcases hs.center _ hc with h | h
  · left
    apply sylowBar_injective hs.central
    rw [hconj]
    change (sylowBar hs.central t)⁻¹ * (sylowBar hs.central q * sylowBar hs.central t *
      (sylowBar hs.central q)⁻¹) = 1 at h
    rw [inv_mul_eq_one] at h
    exact h.symm
  · right
    apply sylowBar_injective hs.central
    rw [hconj, map_mul, sylowBar_self]
    change (sylowBar hs.central t)⁻¹ * (sylowBar hs.central q * sylowBar hs.central t *
      (sylowBar hs.central q)⁻¹) = escapingBar z at h
    rw [inv_mul_eq_iff_eq_mul] at h
    exact h

omit e in
theorem index_centralizer_le_two {t : (S : Subgroup G)} (htJ : sylowBar hs.central t ∈ J)
    (htc : InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _))
      ((⟨_, htJ⟩ : J) : J ⧸ Subgroup.center J)) :
    (Subgroup.centralizer ({t} : Set (S : Subgroup G))).index ≤ 2 := by
  refine index_centralizer_le_two_of_conj (u := ⟨z, hs.central.1⟩) (fun h => ?_) ?_ ?_
    (hs.conj_eq_or_eq_mul hφ htJ htc)
  · have h2 := hs.central.2.1
    rw [show z = 1 from congrArg Subtype.val h, orderOf_one] at h2
    exact absurd h2 (by decide)
  · apply Subtype.ext
    change z * z = 1
    rw [← pow_two]
    have h2 := pow_orderOf_eq_one z
    rwa [hs.central.2.1] at h2
  · intro a
    exact Subtype.ext (hs.central.2.2 a a.2)

end SzEightSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
