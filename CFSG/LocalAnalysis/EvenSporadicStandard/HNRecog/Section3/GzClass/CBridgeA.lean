module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem isExtraspecialPlusByA5WrTwoWith_pCore {G : Type} [Group G] {z : G}
    (hz : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({z} : Set G))) :
    IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) := by
  obtain ⟨Q, hQn, hQW, -⟩ := exists_Qz_eq hz
  haveI : Q.Normal := hQn
  have hp : CFSG.pCore 2 ↥(Gx z) = Q := IsExtraspecialPlusByA5WrTwoWith.pCore_eq hQW
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]; exact hQW.plus
  · rw [hp]; exact hQW.centralizer_le
  · obtain ⟨e⟩ := hQW.quotient
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hp).trans e⟩

theorem nonempty_mulEquiv_Gbar {G : Type} [Group G] {a z : G} (h : IsF5Type a z) :
    Nonempty (Gbar z ≃* A5WrTwo) :=
  (isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z).quotient

theorem cIrreducible_pCore {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hOrb : GzOrbitFacts a z) : CIrreducible ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
  (cIrreducible_iff h.orderOf_z (isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z)
    rfl).mpr hOrb.irreducible

theorem barOf_eq_one_iff {G : Type} [Group G] {z : G} (x : ↥(Gx z)) :
    barOf z x = 1 ↔ (x : G) ∈ Qz z := by
  rw [QuotientGroup.eq_one_iff]
  exact (Subgroup.mem_map_iff_mem (Gx z).subtype_injective
    (K := CFSG.pCore 2 ↥(Gx z)) (x := x)).symm

theorem orderOf_barOf_five {G : Type} [Group G] {z : G} {ρ : ↥(Gx z)} (hρ : orderOf ρ = 5) :
    orderOf (barOf z ρ) = 5 := by
  have hdvd : orderOf (barOf z ρ) ∣ 5 := by
    rw [← hρ]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) ρ
  rcases Nat.prime_five.eq_one_or_self_of_dvd (orderOf (barOf z ρ)) hdvd with h1 | h5
  · exfalso
    have hmemQz : (ρ : G) ∈ Qz z := (barOf_eq_one_iff ρ).mp (orderOf_eq_one_iff.mp h1)
    have hmem : ρ ∈ CFSG.pCore 2 ↥(Gx z) :=
      (Subgroup.mem_map_iff_mem (Gx z).subtype_injective
        (K := CFSG.pCore 2 ↥(Gx z)) (x := ρ)).mp hmemQz
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx z))).exists_orderOf_eq_pow
      ⟨ρ, hmem⟩
    rw [Subgroup.orderOf_mk, hρ] at hn
    have h2 : 2 ∣ 5 := by
      by_cases hn0 : n = 0
      · subst hn0
        norm_num at hn
      · have hd := dvd_pow_self 2 hn0
        rwa [← hn] at hd
    norm_num at h2
  · exact h5

end CFSG.EvenSporadicStandard.HNRecog.Section3
