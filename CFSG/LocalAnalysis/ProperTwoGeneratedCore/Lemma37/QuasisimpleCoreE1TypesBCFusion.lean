module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUInv

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem isConj_of_mem_partCLeft {q q' : J} (hq : q ∈ partCLeft T L) (hq' : q' ∈ partCLeft T L)
    (hq1 : (q : J ⧸ Subgroup.center J) ≠ 1) (hq'1 : (q' : J ⧸ Subgroup.center J) ≠ 1) :
    IsConj (q : J ⧸ Subgroup.center J) (q' : J ⧸ Subgroup.center J) := by
  have hc := d.caseC3BCD.partC
  have hmk1 : ∀ a : J, (a : J ⧸ Subgroup.center J) = 1 ↔ a = 1 ∨ a = centralElt J := fun a => by
    rw [QuotientGroup.eq_one_iff, d.setting.mem_center_iff]
  have hne : ∀ {a : J}, (a : J ⧸ Subgroup.center J) ≠ 1 → a ≠ 1 ∧ a ≠ centralElt J :=
    fun ha => ⟨fun h1 => ha ((hmk1 _).mpr (Or.inl h1)), fun h1 => ha ((hmk1 _).mpr (Or.inr h1))⟩
  have hqq : q * q = centralElt J := hc.mul_self_of_ne hq (hne hq1).1 (hne hq1).2
  have hq'q' : q' * q' = centralElt J := hc.mul_self_of_ne hq' (hne hq'1).1 (hne hq'1).2
  have hqX : q ∈ quasiNormalizer u := mem_quasiNormalizer_of_mem_partCSylow (partCLeft_le hq)
  have hq'X : q' ∈ quasiNormalizer u :=
    mem_quasiNormalizer_of_mem_partCSylow (partCLeft_le hq')
  have hsq : ∀ {a : J} (ha : a ∈ quasiNormalizer u), a * a = centralElt J →
      quasiMk u ⟨a, ha⟩ * quasiMk u ⟨a, ha⟩ = quasiCentral u := fun ha haa => by
    rw [← map_mul, ← d.quasiMk_centralElt]
    exact congrArg (quasiMk u) (Subtype.ext haa)
  obtain ⟨ω, hωL, c, hc', hω⟩ := d.exists_conj_quasiBar_mul
    (quasiMk_mem_of_mem_partCLeft hq hqX) (quasiMk_mem_of_mem_partCLeft hq' hq'X)
    (hsq hqX hqq) (hsq hq'X hq'q')
  have hωu : ω * quasiBar u = quasiBar u * ω :=
    Subgroup.mem_centralizer_iff.mp d.quasiBar_mem_centralizer ω hωL
  have hω' : ω * quasiMk u ⟨q, hqX⟩ * ω⁻¹ = quasiMk u ⟨q', hq'X⟩ * c := by
    refine mul_left_cancel (a := quasiBar u) ?_
    calc quasiBar u * (ω * quasiMk u ⟨q, hqX⟩ * ω⁻¹)
        = quasiBar u * ω * quasiMk u ⟨q, hqX⟩ * ω⁻¹ := by group
      _ = ω * (quasiBar u * quasiMk u ⟨q, hqX⟩) * ω⁻¹ := by rw [← hωu]; group
      _ = quasiBar u * (quasiMk u ⟨q', hq'X⟩ * c) := by rw [hω]; group
  obtain ⟨ω₀, rfl⟩ := QuotientGroup.mk_surjective ω
  set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
  obtain ⟨ε₀, hε₀, hε₀mk⟩ : ∃ ε₀ : quasiNormalizer u,
      ((ε₀ : J) = 1 ∨ (ε₀ : J) = centralElt J) ∧ quasiMk u ε₀ = c := by
    rcases hc' with rfl | rfl
    · exact ⟨1, Or.inl rfl, map_one _⟩
    · exact ⟨e₀, Or.inr rfl, d.quasiMk_centralElt⟩
  have hO : (ω₀ * ⟨q, hqX⟩ * ω₀⁻¹)⁻¹ * (⟨q', hq'X⟩ * ε₀) ∈ pPrimeCore 2 (quasiNormalizer u) := by
    refine QuotientGroup.eq.mp ?_
    change quasiMk u (ω₀ * ⟨q, hqX⟩ * ω₀⁻¹) = quasiMk u (⟨q', hq'X⟩ * ε₀)
    rw [map_mul, map_mul, map_inv, map_mul, hε₀mk]
    exact hω'
  set f : quasiNormalizer u →* J ⧸ Subgroup.center J :=
    (QuotientGroup.mk' (Subgroup.center J)).comp (quasiNormalizer u).subtype with hf
  have hOdd : Odd (Nat.card ((pPrimeCore 2 (quasiNormalizer u)).map f)) :=
    (quasi_oddCore_odd u).of_dvd_nat ((pPrimeCore 2 (quasiNormalizer u)).card_map_dvd f)
  have hε : f ε₀ = 1 := by
    rcases hε₀ with h3 | h3
    · exact (hmk1 _).mpr (Or.inl h3)
    · exact (hmk1 _).mpr (Or.inr h3)
  have hfq : ∀ {a : J} (ha : a ∈ quasiNormalizer u), f ⟨a, ha⟩ = (a : J ⧸ Subgroup.center J) :=
    fun _ => rfl
  have ht : f (ω₀ * ⟨q, hqX⟩ * ω₀⁻¹) * f (ω₀ * ⟨q, hqX⟩ * ω₀⁻¹) = 1 := by
    rw [← map_mul, show ω₀ * ⟨q, hqX⟩ * ω₀⁻¹ * (ω₀ * ⟨q, hqX⟩ * ω₀⁻¹) =
      ω₀ * (⟨q, hqX⟩ * ⟨q, hqX⟩) * ω₀⁻¹ by group, map_mul, map_mul, map_inv,
      show (⟨q, hqX⟩ * ⟨q, hqX⟩ : quasiNormalizer u) = e₀ from Subtype.ext hqq,
      show f e₀ = 1 from (hmk1 _).mpr (Or.inr rfl), mul_one, mul_inv_cancel]
  have ht' : f ⟨q', hq'X⟩ * f ⟨q', hq'X⟩ = 1 := by
    rw [← map_mul, show (⟨q', hq'X⟩ * ⟨q', hq'X⟩ : quasiNormalizer u) = e₀ from
      Subtype.ext hq'q']
    exact (hmk1 _).mpr (Or.inr rfl)
  have hmem : (f (ω₀ * ⟨q, hqX⟩ * ω₀⁻¹))⁻¹ * f ⟨q', hq'X⟩ ∈
      (pPrimeCore 2 (quasiNormalizer u)).map f := by
    have h1 := Subgroup.mem_map_of_mem f hO
    rwa [map_mul, map_mul, hε, mul_one, map_inv] at h1
  obtain ⟨o, -, hot⟩ := exists_conj_eq_of_inv_mul_mem_odd hOdd ht ht' hmem
  refine isConj_iff.mpr ⟨o * f ω₀, ?_⟩
  rw [← hfq hq'X, ← hot, map_mul, map_mul, map_inv, hfq hqX]
  group

theorem isConj_of_mem_map_right_or_left {t : J ⧸ Subgroup.center J}
    (ht : t ∈ (partCRight T L).map (QuotientGroup.mk' (Subgroup.center J)) ∨
      t ∈ (partCLeft T L).map (QuotientGroup.mk' (Subgroup.center J))) (ht1 : t ≠ 1) :
    IsConj (u : J ⧸ Subgroup.center J) t := by
  have hb := d.caseC3BCD
  have huv : IsConj (u : J ⧸ Subgroup.center J) ((x * u * x⁻¹ : J) : J ⧸ Subgroup.center J) :=
    isConj_iff.mpr ⟨(x : J ⧸ Subgroup.center J), by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  have hv1 : ((x * u * x⁻¹ : J) : J ⧸ Subgroup.center J) ≠ 1 := fun h1 => hb.mk_ne_one.1 (by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [show (u : J ⧸ Subgroup.center J) = (x : J ⧸ Subgroup.center J)⁻¹ *
      ((x : J ⧸ Subgroup.center J) * (u : J ⧸ Subgroup.center J) *
        (x : J ⧸ Subgroup.center J)⁻¹) * (x : J ⧸ Subgroup.center J) by group, h1]
    group)
  rcases ht with ht | ht
  · obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ht
    have hxp : IsConj ((x * p * x⁻¹ : J) : J ⧸ Subgroup.center J)
        (QuotientGroup.mk' (Subgroup.center J) p) :=
      isConj_iff.mpr ⟨(x : J ⧸ Subgroup.center J)⁻¹, by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk'_apply]
        group⟩
    have hxp1 : ((x * p * x⁻¹ : J) : J ⧸ Subgroup.center J) ≠ 1 := fun h1 => ht1 (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
      rw [QuotientGroup.mk'_apply, show (p : J ⧸ Subgroup.center J) =
        (x : J ⧸ Subgroup.center J)⁻¹ * ((x : J ⧸ Subgroup.center J) *
          (p : J ⧸ Subgroup.center J) * (x : J ⧸ Subgroup.center J)⁻¹) *
          (x : J ⧸ Subgroup.center J) by group, h1]
      group)
    exact huv.trans ((d.isConj_of_mem_partCLeft d.v_mem_partCLeft (hb.swap_right p hp) hv1
      hxp1).trans hxp)
  · obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp ht
    exact huv.trans (d.isConj_of_mem_partCLeft d.v_mem_partCLeft hq hv1 ht1)

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
