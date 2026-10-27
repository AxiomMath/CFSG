module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32Div
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem exists_lift_of_mem_fixedSubgroup [Finite X] {M : Subgroup X} {t : X}
    (htN : t ∈ normalizer (M : Set X)) (ht2 : t * t = 1) {q : ↥M ⧸ pPrimeCore 2 ↥M}
    (hq : q ∈ fixedSubgroup (TBLit.oddQuotAction M ⟨t, htN⟩)) :
    ∃ (h : X) (hhM : h ∈ M), h * t = t * h ∧
      ((⟨h, hhM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = q := by
  classical
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : TBLit.oddQuotAction M ⟨t, htN⟩ (m : ↥M ⧸ pPrimeCore 2 ↥M) = m := hq
  rw [TBLit.oddQuotAction_mk] at hq'
  have hc : (m : X)⁻¹ * (t * m * t⁻¹) ∈ coreNOf M := by
    have h2 := QuotientGroup.eq.mp hq'.symm
    exact ⟨_, h2, rfl⟩
  obtain ⟨k, hkO, hkc⟩ := exists_commute_of_mem_coset (odd_coreNOf M) ht2
    (fun o ho => (mem_normalizer_iff.mp (le_normalizer_pPrimeCore htN) o).mp ho) hc
  obtain ⟨k', hk', hk'eq⟩ := hkO
  have hkM : k ∈ M := by
    rw [← hk'eq]
    exact k'.2
  have hmkM : (m : X) * k ∈ M := mul_mem m.2 hkM
  refine ⟨(m : X) * k, hmkM, hkc.symm, ?_⟩
  have h1 : (⟨(m : X) * k, hmkM⟩ : ↥M) = m * k' :=
    Subtype.ext (by change (m : X) * k = (m : X) * (k' : X); rw [← hk'eq]; rfl)
  rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k').mpr hk', mul_one]

theorem map_pPrimeCore_le_of_card [Finite X] {M J : Subgroup X} (hJM : J ≤ M)
    (h : Nat.card ((J.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) =
      Nat.card (↥J ⧸ pPrimeCore 2 ↥J)) :
    (pPrimeCore 2 ↥J).map J.subtype ≤ (pPrimeCore 2 ↥M).map M.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK'le : (pPrimeCore 2 ↥M).subgroupOf (J.subgroupOf M) ≤
      pPrimeCore 2 ↥(J.subgroupOf M) := by
    have : (pPrimeCore 2 ↥M).Normal := pPrimeCore_normal
    refine le_sSup ⟨inferInstance, ?_⟩
    have h1 : Nat.card ↥((pPrimeCore 2 ↥M).subgroupOf (J.subgroupOf M)) ∣
        Nat.card ↥(pPrimeCore 2 ↥M) := by
      rw [← card_map_of_injective (J.subgroupOf M).subtype_injective, subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hidx : ((pPrimeCore 2 ↥M).subgroupOf (J.subgroupOf M)).index =
      (pPrimeCore 2 ↥(J.subgroupOf M)).index := by
    rw [← card_map_mk_eq_index, h]
    exact (Nat.card_congr (Sol78.coreQuotCongr (subgroupOfEquivOfLe hJM)).toEquiv).symm
  have heq : (pPrimeCore 2 ↥M).subgroupOf (J.subgroupOf M) = pPrimeCore 2 ↥(J.subgroupOf M) := by
    apply Subgroup.eq_of_le_of_card_ge hK'le
    have h1 := ((pPrimeCore 2 ↥M).subgroupOf (J.subgroupOf M)).card_mul_index
    have h2 := (pPrimeCore 2 ↥(J.subgroupOf M)).card_mul_index
    rw [hidx] at h1
    have hpos : 0 < (pPrimeCore 2 ↥(J.subgroupOf M)).index :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    exact le_of_eq (Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm))
  rintro _ ⟨o, ho, rfl⟩
  have ho' : (subgroupOfEquivOfLe hJM).symm o ∈ pPrimeCore 2 ↥(J.subgroupOf M) := by
    rw [← pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hJM).symm]
    exact ⟨o, ho, rfl⟩
  rw [← heq, mem_subgroupOf] at ho'
  exact ⟨_, ho', rfl⟩

end CFSG.ComponentClassification.SolMax.L32
