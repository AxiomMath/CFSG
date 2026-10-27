module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallDih
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.Foote5.HallD8

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] {D : Subgroup G} (e : D ≃* DihedralGroup 4)

@[expose] def Hz : Subgroup G := centralizer ({cen e} : Set G)

theorem mem_Hz_iff {g : G} : g ∈ Hz e ↔ g * cen e = cen e * g := mem_centralizer_singleton_iff

theorem cen_mem_Hz : cen e ∈ Hz e := (mem_Hz_iff e).mpr rfl

theorem le_Hz_of_D : D ≤ Hz e := fun _ hd => (mem_Hz_iff e).mpr (comm_cen e hd)

@[expose] def zH : Hz e := ⟨cen e, cen_mem_Hz e⟩

@[expose] def Zq : Subgroup (Hz e) := zpowers (zH e)

theorem zH_comm (h : Hz e) : h * zH e = zH e * h :=
  Subtype.ext ((mem_Hz_iff e).mp h.2)

instance Zq_normal : (Zq e).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc : Commute g (zH e ^ k) := (Commute.zpow_right (zH_comm e g) k)
    rw [hc.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k⟩

theorem orderOf_cen : orderOf (cen e) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact cen_mul_cen e) (cen_ne_one e)

theorem mem_zpowers_cen_iff {x : G} : x ∈ zpowers (cen e) ↔ x = 1 ∨ x = cen e := by
  constructor
  · rintro ⟨k, rfl⟩
    have h := zpow_mod_orderOf (cen e) k
    rw [orderOf_cen] at h
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change cen e ^ k = 1
      rw [← h, show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right
      change cen e ^ k = cen e
      rw [← h, show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem mem_Zq_iff {h : Hz e} : h ∈ Zq e ↔ (h : G) ∈ zpowers (cen e) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp [zH]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa [zH] using hk

theorem card_Zq [Finite G] : Nat.card (Zq e) = 2 := by
  rw [Zq, Nat.card_zpowers]
  rw [← orderOf_cen e]
  exact (orderOf_injective (Hz e).subtype (Hz e).subtype_injective (zH e)).symm

@[expose] noncomputable def πq : Hz e →* Hz e ⧸ Zq e := QuotientGroup.mk' (Zq e)

theorem πq_surjective : Function.Surjective (πq e) := QuotientGroup.mk'_surjective (Zq e)

theorem πq_eq_iff {a b : Hz e} : πq e a = πq e b ↔ (a : G)⁻¹ * b ∈ zpowers (cen e) := by
  rw [πq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_Zq_iff]
  rfl

theorem πq_eq_one_iff {a : Hz e} : πq e a = 1 ↔ (a : G) ∈ zpowers (cen e) := by
  rw [πq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_Zq_iff]

theorem card_map_πq_mul [Finite G] {K : Subgroup (Hz e)} (hZK : Zq e ≤ K) :
    Nat.card (K.map (πq e)) * 2 = Nat.card K := by
  set f := (πq e).comp K.subtype with hf
  have hker : f.ker = (Zq e).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, coe_subtype, πq,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hrange : f.range = K.map (πq e) := by
    rw [hf, MonoidHom.range_comp, range_subtype]
  have h := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv, card_Zq] at h
  exact h.symm

variable (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
  ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)

include hcl in
theorem le_Hz [Finite G] {T : Subgroup G} (hT2 : IsPGroup 2 T) (hDT : D ≤ T) : T ≤ Hz e := by
  intro t ht
  have h := conj_cen e (le_normalizer_of_sic e hcl hT2 hDT ht)
  rw [mem_Hz_iff]
  calc t * cen e = t * cen e * t⁻¹ * t := by group
    _ = cen e * t := by rw [h]

@[expose] noncomputable def Tq (T : Subgroup G) : Subgroup (Hz e ⧸ Zq e) :=
  (T.subgroupOf (Hz e)).map (πq e)

@[expose] noncomputable def Dq : Subgroup (Hz e ⧸ Zq e) := (D.subgroupOf (Hz e)).map (πq e)

theorem mem_of_πq_mem_Tq {T : Subgroup G} (hzT : cen e ∈ T) {h : Hz e} (hh : πq e h ∈ Tq e T) :
    (h : G) ∈ T := by
  obtain ⟨t, ht, hth⟩ := hh
  have h1 := (πq_eq_iff e).mp hth
  rcases (mem_zpowers_cen_iff e).mp h1 with h2 | h2
  · rw [inv_mul_eq_one] at h2
    rw [← h2]
    exact ht
  · have : (h : G) = t * cen e := by rw [← h2]; group
    rw [this]
    exact mul_mem ht hzT

theorem mem_of_πq_mem_Dq {h : Hz e} (hh : πq e h ∈ Dq e) : (h : G) ∈ D :=
  mem_of_πq_mem_Tq e (T := D) (cen_mem e) hh

theorem Dq_le_Tq {T : Subgroup G} (hDT : D ≤ T) : Dq e ≤ Tq e T :=
  map_mono fun _ hx => hDT hx

theorem Dq_sq {x : Hz e ⧸ Zq e} (hx : x ∈ Dq e) : x * x = 1 := by
  obtain ⟨d, hd, rfl⟩ := hx
  rw [← map_mul, πq_eq_one_iff]
  rcases mem_cases e (mem_subgroupOf.mp hd) with h | h | h
  · rw [coe_mul, h]
    exact one_mem _
  · rw [coe_mul, h, rot_mul_rot]
    exact mem_zpowers _
  · rw [coe_mul, h, inv_rot_mul_inv_rot]
    exact mem_zpowers _

theorem card_Dq [Finite G] : Nat.card (Dq e) = 4 := by
  have hZD : Zq e ≤ D.subgroupOf (Hz e) := by
    rw [Zq, zpowers_le, mem_subgroupOf]
    exact cen_mem e
  have h := card_map_πq_mul e hZD
  have hD : Nat.card (D.subgroupOf (Hz e)) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_Hz_of_D e)).toEquiv,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rw [hD] at h
  change Nat.card (Dq e) * 2 = 8 at h
  omega

include hcl in
theorem isSylowOf_Tq [Finite G] {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hDT : D ≤ T) :
    IsSylowOf 2 (Tq e T) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH := le_Hz e hcl hT.isPGroup hDT
  rw [isSylowOf_iff] at hT ⊢
  obtain ⟨-, hT2, hTi⟩ := hT
  refine ⟨le_top, ?_, ?_⟩
  · have h1 : IsPGroup 2 (T.subgroupOf (Hz e)) :=
      hT2.of_equiv (subgroupOfEquivOfLe hTH).symm
    exact h1.map _
  · rw [relIndex_top_right]
    intro h2
    apply hTi
    rw [relIndex_top_right]
    have h3 : (Tq e T).index ∣ (T.subgroupOf (Hz e)).index := index_map_dvd _ (πq_surjective e)
    have h4 : (T.subgroupOf (Hz e)).index ∣ T.index := by
      rw [← relIndex]
      exact relIndex_dvd_index_of_le hTH
    exact h2.trans (h3.trans h4)

include hcl in
theorem rightConjugate_Dq [Finite G] {T : Subgroup G} (hT2 : IsPGroup 2 T) (hDT : D ≤ T)
    (g : Hz e ⧸ Zq e) (hg : rightConjugate (Dq e) g ≤ Tq e T) : rightConjugate (Dq e) g = Dq e := by
  obtain ⟨h, rfl⟩ := πq_surjective e g
  have hTN := le_normalizer_of_sic e hcl hT2 hDT
  have hDH := le_Hz_of_D e
  have hzT : cen e ∈ T := hDT (cen_mem e)
  have hconj : ∀ d (hd : d ∈ Hz e), d ∈ D →
      πq e (h⁻¹ * ⟨d, hd⟩ * h) = (MulAut.conj (πq e h)⁻¹) (πq e ⟨d, hd⟩) := by
    intro d hd _
    simp [map_mul, map_inv]
  have hT' : ∀ d ∈ D, (h : G)⁻¹ * d * h ∈ T := by
    intro d hd
    have hmem : πq e (h⁻¹ * ⟨d, hDH hd⟩ * h) ∈ Tq e T := by
      rw [hconj d (hDH hd) hd]
      exact hg ⟨_, ⟨⟨d, hDH hd⟩, mem_subgroupOf.mpr hd, rfl⟩, rfl⟩
    have := mem_of_πq_mem_Tq e hzT hmem
    simpa using this
  have hD' : ∀ d ∈ D, (h : G)⁻¹ * d * h ∈ D := fun d hd =>
    conj_mem_of_sic_of_le e hcl hTN hT' hd
  refine eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨_, ⟨⟨d, hdH⟩, hd, rfl⟩, rfl⟩
    have hd' : d ∈ D := mem_subgroupOf.mp hd
    refine ⟨h⁻¹ * ⟨d, hdH⟩ * h, mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using hD' d hd'
    · exact hconj d hdH hd'
  · exact (card_map_of_injective (f := (MulAut.conj (πq e h)⁻¹).toMonoidHom)
      (MulAut.conj (πq e h)⁻¹).injective).ge

end CFSG.ComponentClassification.Foote5.HallD8
