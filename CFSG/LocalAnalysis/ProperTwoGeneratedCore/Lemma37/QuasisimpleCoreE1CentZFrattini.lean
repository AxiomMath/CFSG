module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZTau
public import CFSG.GroupTheory.PCore.CommutingBalance

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

section General

variable {X : Type} [Group X]

theorem conj_mem_map_subtype {H : Subgroup X} {K : Subgroup H} [K.Normal] {g a : X}
    (hg : g ∈ H) (ha : a ∈ K.map H.subtype) : g * a * g⁻¹ ∈ K.map H.subtype := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
  exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk _, rfl⟩

theorem odd_orderOf_of_mem_map_pPrimeCore [Finite X] {H : Subgroup X} {a : X}
    (ha : a ∈ (CFSG.pPrimeCore 2 H).map H.subtype) : Odd (orderOf a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hk)

theorem eq_one_of_mul_self_of_odd {a : X} (h : a * a = 1) (hodd : Odd (orderOf a)) : a = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right dvd_rfl
    (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)))

end General

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J}

omit [Finite J] in
theorem centralizer_forty_eq : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} =
    Subgroup.centralizer {((u * (x * u * x⁻¹) : J) : J ⧸ Subgroup.center J)} := by
  rw [CaseC3BCD.caseC3Word_forty]

omit [Finite J] in
theorem e1M0_le_centralizer_forty : e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)) ≤
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} := by
  rw [centralizer_forty_eq]
  exact e1M0_le_centralizer

variable (d : E1Data Q B z u T L S y x m)
include d

theorem map_pPrimeCore_e1M0_le :
    (CFSG.pPrimeCore 2 (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))).subtype ≤
      (CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})).map
        (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMC := e1M0_le_centralizer_forty (u := u) (x := x) (m := m) (y := y)
  have hN : ((e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))).subgroupOf
      (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})).Normal := by
    rw [centralizer_forty_eq]
    exact normal_e1M0 d.caseC3BCD.partC.center d.caseC3BCD.mem_iff
  have hKc : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 ((e1M0 (Subgroup.center J)
      (u * (x * u * x⁻¹))).subgroupOf (Subgroup.centralizer
        {caseC3Word (Subgroup.center J) u m y x 40}))).map ((e1M0 (Subgroup.center J)
          (u * (x * u * x⁻¹))).subgroupOf (Subgroup.centralizer
            {caseC3Word (Subgroup.center J) u m y x 40})).subtype)) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact CFSG.pPrimeCore_coprime_card
  rw [← CFSG.pPrimeCore_map_subgroupOf 2 _ _ hMC]
  exact Subgroup.map_mono (le_sSup ⟨inferInstance, hKc⟩)

theorem e1RBar_le_normalizer_map_pPrimeCore : e1RBar (Subgroup.center J) u m y x ≤
    Subgroup.normalizer (((CFSG.pPrimeCore 2 (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
      (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))).subtype : Subgroup (J ⧸ Subgroup.center J)) :
        Set (J ⧸ Subgroup.center J)) := fun _ hr =>
  mem_normalizer_of_forall_conj_mem fun _ ho =>
    conj_mem_map_subtype (d.caseC3BCD.e1RBar_le_e1M0 hr) ho

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem mem_normalizer_e1EBar_of_conj_mem {g : J ⧸ Subgroup.center J}
    (hgR : ∀ s ∈ e1RBar (Subgroup.center J) u m y x,
      g * s * g⁻¹ ∈ e1RBar (Subgroup.center J) u m y x) :
    g ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)) := by
  have hb := d.caseC3BCD
  refine mem_normalizer_of_forall_conj_mem fun t ht => ?_
  by_cases ht1 : t = 1
  · rw [ht1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  by_cases htz : t = caseC3Word (Subgroup.center J) u m y x 40
  · rw [htz, hb.conj_forty_of_normalizes hgR]
    exact hb.forty_mem_e1EBar
  exact (hb.conj_mem_e1EBar_of_typeD htype hgR ht ht1 htz).1

theorem exists_mul_of_mem_centralizer_forty
    (hRO : ∀ g ∈ e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)),
      ∀ r ∈ e1RBar (Subgroup.center J) u m y x,
        g * r * g⁻¹ ∈ e1RBar (Subgroup.center J) u m y x ⊔
          (CFSG.pPrimeCore 2 (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
            (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))).subtype)
    {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) :
    ∃ o ∈ (CFSG.pPrimeCore 2 (Subgroup.centralizer
        {caseC3Word (Subgroup.center J) u m y x 40})).map
          (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype,
      ∃ n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
        o * n = g := by
  have hb := d.caseC3BCD
  set M := e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)) with hM
  set R := e1RBar (Subgroup.center J) u m y x with hR
  set OM := (CFSG.pPrimeCore 2 M).map M.subtype with hOM
  have key : ∀ g ∈ M, ∃ o ∈ OM, ∃ n ∈ Subgroup.normalizer
      (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)), o * n = g := by
    intro g hgM
    have hHM : R ⊔ OM ≤ M := sup_le hb.e1RBar_le_e1M0 (Subgroup.map_subtype_le _)
    have hidx : ¬ 2 ∣ R.relIndex (R ⊔ OM) := fun h2 => hb.not_two_dvd_relIndex S rfl
      (dvd_trans h2 (Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hHM)))
    obtain ⟨h, hhH, hh⟩ := exists_mul_conj_mem_of_not_two_dvd hb.isPGroup_e1RBar hidx (hRO g hgM)
    have hh' : h ∈ ((R ⊔ OM : Subgroup (J ⧸ Subgroup.center J)) : Set (J ⧸ Subgroup.center J)) :=
      hhH
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ d.e1RBar_le_normalizer_map_pPrimeCore]
      at hh'
    obtain ⟨r, hr, o, ho, rfl⟩ := hh'
    have hog : ∀ s ∈ R, o * g * s * (o * g)⁻¹ ∈ R := fun s hs => by
      rw [show o * g * s * (o * g)⁻¹ = r⁻¹ * (r * o * g * s * (r * o * g)⁻¹) * r by group]
      exact R.mul_mem (R.mul_mem (R.inv_mem hr) (hh s hs)) hr
    exact ⟨o⁻¹, OM.inv_mem ho, o * g, d.mem_normalizer_e1EBar_of_conj_mem htype hog, by group⟩
  by_cases hgM : g ∈ M
  · obtain ⟨o, ho, n, hn, rfl⟩ := key g hgM
    exact ⟨o, d.map_pPrimeCore_e1M0_le ho, n, hn, rfl⟩
  · have hgC : g ∈ Subgroup.centralizer {((u * (x * u * x⁻¹) : J) : J ⧸ Subgroup.center J)} := by
      rw [← centralizer_forty_eq (m := m) (y := y)]
      exact hg
    obtain ⟨o, ho, n, hn, hon⟩ := key _ (mul_mem_e1M0_of_not_mem hb.partC.center hb.mem_iff hgC
      (hb.caseC3Word_mem_centralizer 16) hgM hb.sixteen_not_mem_e1M0)
    refine ⟨o, d.map_pPrimeCore_e1M0_le ho, n * (caseC3Word (Subgroup.center J) u m y x 16)⁻¹,
      Subgroup.mul_mem _ hn (Subgroup.inv_mem _ (d.map_le_normalizer_e1EBar
        (hb.caseC3Word_mem 16))), ?_⟩
    rw [← mul_assoc, hon, mul_inv_cancel_right]

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
