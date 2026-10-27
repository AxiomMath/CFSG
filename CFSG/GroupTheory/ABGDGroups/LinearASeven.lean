module

public import Mathlib
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import Certificates.Certificate7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7SylowCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.GorensteinWalter (a7t a7u a7a a7v a7s a7S a7U a7V
  aSeven_structure_fact_1_8_ii_centralizer factorization_two_2520
  card_sup_eq_mul_of_disjoint_of_le_normalizer)

theorem odd_card_of_le_normalizer_of_inf_eq_bot {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {Y : Subgroup G} (hY : (S : Subgroup G) ≤ Subgroup.normalizer (Y : Set G))
    (hYS : Y ⊓ S = ⊥) : Odd (Nat.card Y) := by
  have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer Y S hY (disjoint_iff.mpr hYS)
  have hdvd : Nat.card (S : Subgroup G) * Nat.card Y ∣
      Nat.card (S : Subgroup G) * (S : Subgroup G).index := by
    rw [mul_comm, ← hcard, Subgroup.card_mul_index]
    exact Subgroup.card_subgroup_dvd_card _
  have hYi := (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp hdvd
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact fun h2 => S.not_dvd_index (h2.trans hYi)

section Concrete

local notation "A₇" => alternatingGroup (Fin 7)

theorem card_alternatingGroup_fin_seven : Nat.card A₇ = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_a7S : Nat.card a7S = 8 := by
  have h : ∀ x : A₇, x ∈ a7S ↔ x ∈ ({1, a7v, a7v ^ 2, a7v ^ 3, a7s, a7s * a7v, a7s * a7v ^ 2,
      a7s * a7v ^ 3} : Finset A₇) := fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Iff.rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_finsetCard]
  decide +kernel

theorem exists_sylow_coe_eq_a7S :
    ∃ P : Sylow 2 A₇, (P : Subgroup A₇) = a7S :=
  ⟨Sylow.ofCard a7S (by
      rw [card_a7S, card_alternatingGroup_fin_seven, factorization_two_2520]; norm_num),
    Sylow.coe_ofCard _ _⟩

theorem a7V_le_a7S : a7V ≤ a7S := by
  intro x hx
  change x = 1 ∨ x = a7t ∨ x = a7u ∨ x = a7t * a7u at hx
  change x = 1 ∨ x = a7v ∨ x = a7v ^ 2 ∨ x = a7v ^ 3 ∨ x = a7s ∨ x = a7s * a7v ∨
    x = a7s * a7v ^ 2 ∨ x = a7s * a7v ^ 3
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

theorem a7U_le_centralizer_a7V : a7U ≤ Subgroup.centralizer (a7V : Set A₇) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hx
  change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
  rcases hx with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> decide +kernel

theorem a7S_le_normalizer_a7U : a7S ≤ Subgroup.normalizer (a7U : Set A₇) := by
  intro s hs
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  change n = 1 ∨ n = a7a ∨ n = a7a ^ 2 at hn
  change s * n * s⁻¹ = 1 ∨ s * n * s⁻¹ = a7a ∨ s * n * s⁻¹ = a7a ^ 2
  change s = 1 ∨ s = a7v ∨ s = a7v ^ 2 ∨ s = a7v ^ 3 ∨ s = a7s ∨ s = a7s * a7v ∨
    s = a7s * a7v ^ 2 ∨ s = a7s * a7v ^ 3 at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl <;> decide +kernel

theorem a7U_inf_a7S : a7U ⊓ a7S = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxS⟩
  change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hxU
  change x = 1 ∨ x = a7v ∨ x = a7v ^ 2 ∨ x = a7v ^ 3 ∨ x = a7s ∨ x = a7s * a7v ∨
    x = a7s * a7v ^ 2 ∨ x = a7s * a7v ^ 3 at hxS
  rw [Subgroup.mem_bot]
  rcases hxU with rfl | rfl | rfl
  · rfl
  · exact absurd hxS (by decide +kernel)
  · exact absurd hxS (by decide +kernel)

set_option synthInstance.maxSize 4096 in
theorem aSeven_centralizer_involution_a7V_certificate : ∀ x : A₇,
    (x * a7t = a7t * x → x ^ 12 = 1 ∧ (x ^ 3 = 1 → x = 1 ∨ x = a7a ∨ x = a7a ^ 2)) ∧
    (x * a7u = a7u * x → x ^ 12 = 1 ∧ (x ^ 3 = 1 → x = 1 ∨ x = a7a ∨ x = a7a ^ 2)) ∧
    (x * (a7t * a7u) = a7t * a7u * x →
      x ^ 12 = 1 ∧ (x ^ 3 = 1 → x = 1 ∨ x = a7a ∨ x = a7a ^ 2)) := by
  decide +kernel

theorem le_a7U_of_odd_of_a7V_le_normalizer
    {Y : Subgroup A₇} (hodd : Odd (Nat.card Y))
    (hY : a7V ≤ Subgroup.normalizer (Y : Set A₇)) : Y ≤ a7U := by
  have hV : IsKleinFour a7V := aSeven_structure_fact_1_8_ii_centralizer.2.2.2
  have hpow : ∀ v : a7V, v ^ 2 = 1 := fun v => by
    rw [← hV.exponent_two]
    exact Monoid.pow_exponent_eq_one v
  refine (CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two a7V Y hpow hV.card_four
    (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)) hY).le.trans ?_
  refine iSup₂_le fun v hv => ?_
  rintro x ⟨hxY, hxC⟩
  have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hx3 : x ^ 12 = 1 → x ^ 3 = 1 := fun h12 => by
    have hoddx : Odd (orderOf x) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hxY)
    have hdvd : orderOf x ∣ 3 * 4 := orderOf_dvd_of_pow_eq_one h12
    have hcop : Nat.Coprime (orderOf x) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_right.mpr hoddx).pow_right 2
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)
  have hv1 : (v : A₇) ≠ 1 := fun h => hv (Subtype.ext h)
  have hvV : (v : A₇) = 1 ∨ (v : A₇) = a7t ∨ (v : A₇) = a7u ∨ (v : A₇) = a7t * a7u := v.2
  obtain ⟨ht, hu, htu⟩ := aSeven_centralizer_involution_a7V_certificate x
  change x = 1 ∨ x = a7a ∨ x = a7a ^ 2
  rcases hvV with h | h | h | h
  · exact absurd h hv1
  · rw [h] at hxv
    exact (ht hxv).2 (hx3 (ht hxv).1)
  · rw [h] at hxv
    exact (hu hxv).2 (hx3 (hu hxv).1)
  · rw [h] at hxv
    exact (htu hxv).2 (hx3 (htu hxv).1)

end Concrete

section Transport

variable {H : Type} [Group H] [Finite H]

theorem exists_mulEquiv_aSeven_map_sylow_eq
    (e : H ≃* alternatingGroup (Fin 7))
    (S : Sylow 2 H) :
    ∃ φ : H ≃* alternatingGroup (Fin 7), (S : Subgroup H).map φ.toMonoidHom = a7S := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_coe_eq_a7S
  have he : Function.Surjective e.toMonoidHom := e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (S.mapSurjective he) P₀
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h : ((g • S.mapSurjective he : Sylow 2 _) : Subgroup (alternatingGroup (Fin 7))) = a7S := by
    rw [hg, hP₀]
  rw [← h]
  change _ = Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map e.toMonoidHom ↑S)
  rw [Subgroup.map_map]
  rfl

theorem map_le_a7U_of_sylow_signalizer
    (φ : H ≃* alternatingGroup (Fin 7)) {S : Sylow 2 H}
    (hφ : (S : Subgroup H).map φ.toMonoidHom = a7S) {Y : Subgroup H}
    (hY : (S : Subgroup H) ≤ Subgroup.normalizer (Y : Set H)) (hYS : Y ⊓ S = ⊥) :
    Y.map φ.toMonoidHom ≤ a7U := by
  apply le_a7U_of_odd_of_a7V_le_normalizer
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact odd_card_of_le_normalizer_of_inf_eq_bot S hY hYS
  · refine a7V_le_a7S.trans ?_
    rw [← hφ]
    exact (Subgroup.map_mono hY).trans (Subgroup.le_normalizer_map _)

omit [Finite H] in
theorem map_symm_a7S_eq (φ : H ≃* alternatingGroup (Fin 7)) {S : Sylow 2 H}
    (hφ : (S : Subgroup H).map φ.toMonoidHom = a7S) :
    a7S.map φ.symm.toMonoidHom = S := by
  rw [← hφ, Subgroup.map_map]
  convert Subgroup.map_id (S : Subgroup H)
  ext x
  simp

theorem exists_kleinFour_centralizing_sylow_signalizer
    (e : H ≃* alternatingGroup (Fin 7))
    (S : Sylow 2 H) {Y : Subgroup H} (hY : (S : Subgroup H) ≤ Subgroup.normalizer (Y : Set H))
    (hYS : Y ⊓ S = ⊥) :
    Nat.card Y ∣ 3 ∧
      ∃ V : Subgroup H, V ≤ S ∧ IsKleinFour V ∧ Y ≤ Subgroup.centralizer (V : Set H) := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_aSeven_map_sylow_eq e S
  have hYU := map_le_a7U_of_sylow_signalizer φ hφ hY hYS
  have hV : IsKleinFour a7V := aSeven_structure_fact_1_8_ii_centralizer.2.2.2
  refine ⟨?_, a7V.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective,
      ← aSeven_structure_fact_1_8_ii_centralizer.1]
    exact Subgroup.card_dvd_of_le hYU
  · rw [← map_symm_a7S_eq φ hφ]
    exact Subgroup.map_mono a7V_le_a7S
  · let ψ := a7V.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective
    exact ⟨by rw [← Nat.card_congr ψ.toEquiv]; exact hV.card_four,
      by rw [← Monoid.exponent_eq_of_mulEquiv ψ]; exact hV.exponent_two⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hyU : φ y ∈ a7U := hYU ⟨y, hy, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp (a7U_le_centralizer_a7V hyU) v hv
    apply φ.injective
    simpa using hc

theorem card_eq_three_of_maximal_sylow_signalizer
    (e : H ≃* alternatingGroup (Fin 7))
    (S : Sylow 2 H) {Y : Subgroup H} (hY : (S : Subgroup H) ≤ Subgroup.normalizer (Y : Set H))
    (hYS : Y ⊓ S = ⊥)
    (hmax : ∀ Y' : Subgroup H, (S : Subgroup H) ≤ Subgroup.normalizer (Y' : Set H) →
      Y' ⊓ S = ⊥ → Y ≤ Y' → Y' = Y) :
    Nat.card Y = 3 ∧
      ∃ V : Subgroup H, V ≤ S ∧ IsKleinFour V ∧ Y ≤ Subgroup.centralizer (V : Set H) := by
  refine ⟨?_, (exists_kleinFour_centralizing_sylow_signalizer e S hY hYS).2⟩
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_aSeven_map_sylow_eq e S
  have hYU := map_le_a7U_of_sylow_signalizer φ hφ hY hYS
  have hS := map_symm_a7S_eq φ hφ
  have h1 : (S : Subgroup H) ≤ Subgroup.normalizer ((a7U.map φ.symm.toMonoidHom : Subgroup H) :
      Set H) := by
    rw [← hS]
    exact (Subgroup.map_mono a7S_le_normalizer_a7U).trans (Subgroup.le_normalizer_map _)
  have h2 : a7U.map φ.symm.toMonoidHom ⊓ S = ⊥ := by
    rw [← hS, ← Subgroup.map_inf_eq _ _ _ φ.symm.injective, a7U_inf_a7S, Subgroup.map_bot]
  have h3 : Y ≤ a7U.map φ.symm.toMonoidHom := fun y hy =>
    ⟨φ y, hYU ⟨y, hy, rfl⟩, φ.symm_apply_apply y⟩
  rw [← hmax _ h1 h2 h3, Subgroup.card_map_of_injective φ.symm.injective]
  exact aSeven_structure_fact_1_8_ii_centralizer.1

end Transport

end CFSG.ABGDGroups
