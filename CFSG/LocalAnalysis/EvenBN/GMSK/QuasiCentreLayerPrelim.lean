module

public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem qc_zpowers_relIndex_odd {H : Type} [Group H] [Finite H] {J : Subgroup H} {a : H}
    (ha : orderOf a = 2) (haJ : a ∈ centralizer (J : Set H))
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (J : Set H) → IsPGroup 2 P → Nat.card P ≤ 2) :
    ¬ 2 ∣ (zpowers a).relIndex (centralizer (J : Set H)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := centralizer (J : Set H) with hBdef
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hP2 : IsPGroup 2 ((zpowers a).subgroupOf B) :=
    hza.comap_of_injective _ B.subtype_injective
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hSle : (S : Subgroup B).map B.subtype ≤ B := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS2 : Nat.card (S : Subgroup B) ≤ 2 := by
    have h := hrank ((S : Subgroup B).map B.subtype) hSle (S.isPGroup'.map B.subtype)
    rwa [Subgroup.card_map_of_injective B.subtype_injective] at h
  have hle : zpowers a ≤ B := (zpowers_le (G := H)).2 haJ
  have hcardP : Nat.card ((zpowers a).subgroupOf B) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, ha]
  have hSP : (zpowers a).subgroupOf B = (S : Subgroup B) :=
    Subgroup.eq_of_le_of_card_ge hPS (by rw [hcardP]; exact hS2)
  rw [Subgroup.relIndex, hSP]
  exact S.not_dvd_index

theorem quasi_layer_prelim {H : Type} [Group H] [Finite H]
    (hO : CFSG.Open.standardComponentOddCore H = ⊥) {J : Subgroup H}
    (hJq : CFSG.Open.IsQuasisimple ↥J) {a : H} (ha : orderOf a = 2)
    (haJ : a ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({a} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (J : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnn : ¬ J.Normal) :
    CFSG.fittingSubgroup H = ⊥ ∧ J ≤ CFSG.layer H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : CFSG.pPrimeCore 2 H = ⊥ := pPrimeCore_eq_bot_of_oddCore_eq_bot hO
  have hJa : J ≤ centralizer ({a} : Set H) := fun j hj =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 haJ j hj)
  have hJn' : centralizer ({a} : Set H) ≤ normalizer (J : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hJa).1 hJn
  have hsyl : ¬ 2 ∣ (zpowers a).relIndex (centralizer (J : Set H)) :=
    qc_zpowers_relIndex_odd ha haJ hrank
  set L₀ := J.subgroupOf (centralizer ({a} : Set H)) with hL₀def
  have hJq' : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hJq
  have hL₀ : CFSG.IsComponent L₀ :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJa).symm hJq',
      hJn.isSubnormal⟩
  have hL₀map : L₀.map (centralizer ({a} : Set H)).subtype = J := by
    rw [hL₀def, subgroupOf_map_subtype, inf_eq_left.2 hJa]
  set B := centralizer (J : Set H) with hBdef
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hP2 : IsPGroup 2 ((zpowers a).subgroupOf B) :=
    hza.comap_of_injective _ B.subtype_injective
  have hsyl' : ¬ 2 ∣ ((zpowers a).subgroupOf B).index := by
    rwa [Subgroup.relIndex] at hsyl
  set S₀ := hP2.toSylow hsyl' with hS₀def
  have hmemS₀ : ∀ x : B, x ∈ S₀ → (x : H) = 1 ∨ (x : H) = a := fun x hx => by
    rw [hS₀def, IsPGroup.mem_toSylow] at hx
    exact CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayer.eq_one_or_eq_of_mem_zpowers ha hx
  have hO2 : CFSG.pCore 2 H = ⊥ := by
    have hcomm := CFSG.LocalAnalysis.ComponentInitial.involution_component_centralizes_two_core
      ha L₀ hL₀
    rw [hL₀map, commutator_comm] at hcomm
    have hQB : CFSG.pCore 2 H ≤ B := commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hN2 : IsPGroup 2 ((CFSG.pCore 2 H).subgroupOf B) :=
      CFSG.pCore_isPGroup.comap_of_injective _ B.subtype_injective
    have hle := hN2.le_sylow_of_normal S₀
    have hQa : ∀ q ∈ CFSG.pCore 2 H, q = 1 ∨ q = a := fun q hq =>
      hmemS₀ ⟨q, hQB hq⟩ (hle hq)
    by_contra hne
    obtain ⟨⟨q, hq⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hqa : q = a := (hQa q hq).resolve_left fun h => hq1 (Subtype.ext h)
    rw [hqa] at hq
    apply hnn
    have htop : centralizer ({a} : Set H) = ⊤ := by
      refine eq_top_iff.2 fun g _ => mem_centralizer_singleton_iff.2 ?_
      have hm : g * a * g⁻¹ ∈ CFSG.pCore 2 H :=
        (inferInstance : (CFSG.pCore 2 H).Normal).conj_mem a hq g
      rcases hQa _ hm with h | h
      · exfalso
        have h1 : a = 1 := by
          calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [h1, orderOf_one] at ha
        exact absurd ha (by norm_num)
      · calc g * a = g * a * g⁻¹ * g := by group
          _ = a * g := by rw [h]
    exact normalizer_eq_top_iff.1 (top_le_iff.1 (htop ▸ hJn'))
  have hF : CFSG.fittingSubgroup H = ⊥ := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, eq_bot_iff]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2, hO2]
    · rw [← hcore]
      have : Fact (p : ℕ).Prime := ⟨hp⟩
      refine le_sSup ⟨inferInstance, ?_⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := H))
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hJE : J ≤ CFSG.layer H :=
    CFSG.SeitzReduction.isComponent_centralizer_le_layer hcore
      (by rw [← ha]; exact pow_orderOf_eq_one a) hJa hL₀
  exact ⟨hF, hJE⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
