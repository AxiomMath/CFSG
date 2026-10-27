module

import CFSG.LieType.Simplicity.Classical
import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

section ThreeComponent

open KFactsPair
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace R1511C

theorem map_pPrimeCore_eq_inf {P : Type} [Group P] [Finite P] {L : Subgroup P}
    (hL : L.IsSubnormal) :
    (CFSG.pPrimeCore 3 ↥L).map L.subtype = L ⊓ CFSG.pPrimeCore 3 P := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ 3} hL
  rwa [← CFSG.pPrimeCore_eq_piCore ↥L 3, ← CFSG.pPrimeCore_eq_piCore P 3] at h

theorem subgroupOf_pPrimeCore_eq {P : Type} [Group P] [Finite P] {L : Subgroup P}
    (hL : L.IsSubnormal) : (CFSG.pPrimeCore 3 P).subgroupOf L = CFSG.pPrimeCore 3 ↥L := by
  have h := map_pPrimeCore_eq_inf hL
  ext x
  rw [Subgroup.mem_subgroupOf]
  have h1 : L.subtype x ∈ (CFSG.pPrimeCore 3 ↥L).map L.subtype ↔ x ∈ CFSG.pPrimeCore 3 ↥L :=
    Subgroup.mem_map_iff_mem L.subtype_injective
  rw [← h1, h]
  exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩

theorem le_pPrimeCore_of_normal {G : Type} [Group G] {N : Subgroup G} (hN : N.Normal)
    (h : ¬ 3 ∣ Nat.card N) : N ≤ CFSG.pPrimeCore 3 G :=
  le_sSup ⟨hN, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h⟩

theorem not_dvd_card_pPrimeCore (G : Type) [Group G] [Finite G] :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 G) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card

theorem isLThreeTwoPow_of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsLThreeTwoPow S') : IsLThreeTwoPow S := by
  rcases h with ⟨d, hd, ⟨e'⟩⟩ | ⟨d, hd, ⟨e'⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨d, hd, ⟨e.trans e'⟩⟩

theorem isLThreeTwoPow_of_isLThreeOdd {S : Type} [Group S] (h : IsLThreeOdd S) :
    IsLThreeTwoPow S := by
  obtain ⟨n, -, h | h⟩ := h
  · obtain ⟨-, d, q, hq, hd, he⟩ := h
    exact Or.inr ⟨d, ⟨q, hq, hd⟩, he⟩
  · obtain ⟨-, d, Q, hQ, -, hd, he⟩ := h
    exact Or.inl ⟨d, ⟨Q, hQ, hd⟩, he⟩

theorem isSimpleGroup_of_isLThreeTwoPow {S : Type} [Group S] (h : IsLThreeTwoPow S) :
    IsSimpleGroup S := by
  rcases h with ⟨⟨d, hv⟩, ⟨Q, -, hd⟩, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨Q, -, hd⟩, ⟨e⟩⟩
  · simp only at hd
    subst hd
    exact (CFSG.LieType.Simplicity.fam_PSL_simplicity S _ _ _
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)).2
  · simp only at hd
    subst hd
    exact (CFSG.LieType.Simplicity.fam_PSL_simplicity S _ _ _
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)).2

theorem closure_two_elements_eq_top {G : Type} [Group G] :
    Subgroup.closure {x : ↥(pElementSubgroup 2 (⊤ : Subgroup G)) | ∃ k : ℕ, orderOf x = 2 ^ k} =
      ⊤ := by
  unfold pElementSubgroup
  have h := Subgroup.closure_preimage_eq_top
    {x : G | x ∈ (⊤ : Subgroup G) ∧ ∃ k : ℕ, orderOf x = 2 ^ k}
  refine eq_top_iff.2 (h.symm.le.trans (Subgroup.closure_mono ?_))
  rintro x ⟨-, k, hk⟩
  exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩

theorem exists_noncomm_of_simple_of_dvd {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h3 : 3 ∣ Nat.card S)
    (hgen : Subgroup.closure {x : S | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤) :
    ∃ a b : S, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨x, ⟨k, hk⟩, hx1⟩ : ∃ x : S, (∃ k : ℕ, orderOf x = 2 ^ k) ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Subgroup.closure {x : S | ∃ k : ℕ, orderOf x = 2 ^ k} ≤ ⊥ :=
      (Subgroup.closure_le ⊥).2 fun y hy => Subgroup.mem_bot.2 (hcon y hy)
    rw [hgen] at hle
    haveI : Nontrivial S := IsSimpleGroup.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    exact hab ((Subgroup.mem_bot.1 (hle (Subgroup.mem_top a))).trans
      (Subgroup.mem_bot.1 (hle (Subgroup.mem_top b))).symm)
  have hnorm : (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
    rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have htop : Subgroup.zpowers x = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
    · exact absurd (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers x)) hx1
    · exact h
  have hcard : Nat.card S = 2 ^ k := by
    rw [← hk, ← Nat.card_zpowers, htop, Subgroup.card_top]
  rw [hcard] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem isQuasisimple_of_simple_noncomm {S : Type} [Group S] [IsSimpleGroup S]
    (h : ∃ a b : S, a * b ≠ b * a) : CFSG.IsQuasisimple S := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, b, hab⟩ := h
      exact absurd ((Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top b)) a) hab
  have e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h' | h'
    · obtain ⟨a, b, hab⟩ := h
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h']
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hab
    · exact ⟨h'⟩
  · obtain ⟨a, b, hab⟩ := h
    exact ⟨e.symm a, e.symm b, fun hh => hab (e.symm.injective (by rw [map_mul, map_mul, hh]))⟩

theorem pElementSubgroup_top_normal {Y : Type} [Group Y] (p : ℕ) :
    (pElementSubgroup p (⊤ : Subgroup Y)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold pElementSubgroup at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top _, ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    refine ⟨k, ?_⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [MulAut.conj_apply, hk] using this
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem pCore_two_le_pPrimeCore_three (G : Type) [Group G] [Finite G] :
    CFSG.pCore 2 G ≤ CFSG.pPrimeCore 3 G := by
  refine le_pPrimeCore_of_normal CFSG.pCore_normal ?_
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := G) (p := 2)).exists_card_eq
  rw [hn]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem pElementSubgroup_map_equiv {Y Y' : Type*} [Group Y] [Group Y'] (ψ : Y ≃* Y') (p : ℕ)
    (A : Subgroup Y) :
    (pElementSubgroup p A).map ψ.toMonoidHom = pElementSubgroup p (A.map ψ.toMonoidHom) := by
  rw [pElementSubgroup, pElementSubgroup, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxA, k, hk⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]⟩
  · rintro ⟨⟨x, hxA, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hxA, k, ?_⟩, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk

theorem isLThreeOdd_of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsLThreeOdd S') : IsLThreeOdd S := by
  obtain ⟨n, hn, h | h⟩ := h
  · obtain ⟨h1, d, q, hq, hd, ⟨e'⟩⟩ := h
    exact ⟨n, hn, Or.inl ⟨h1, d, q, hq, hd, ⟨e.trans e'⟩⟩⟩
  · obtain ⟨h1, d, Q, hQ, hn', hd, ⟨e'⟩⟩ := h
    exact ⟨n, hn, Or.inr ⟨h1, d, Q, hQ, hn', hd, ⟨e.trans e'⟩⟩⟩

theorem hasLThreeCore_of_equiv {Y Y' : Type} [Group Y] [Group Y'] {A : Subgroup Y}
    {B : Subgroup Y'} (e : ↥A ≃* ↥B) (h : HasLThreeCore B) : HasLThreeCore A := by
  let ē : (↥A ⧸ CFSG.pCore 2 ↥A) ≃* (↥B ⧸ CFSG.pCore 2 ↥B) :=
    QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
  have hmap : (pElementSubgroup 2 (⊤ : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A))).map ē.toMonoidHom =
      pElementSubgroup 2 (⊤ : Subgroup (↥B ⧸ CFSG.pCore 2 ↥B)) := by
    rw [pElementSubgroup_map_equiv, Subgroup.map_top_of_surjective ē.toMonoidHom ē.surjective]
  exact isLThreeOdd_of_equiv
    (((pElementSubgroup 2 (⊤ : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A))).equivMapOfInjective
      ē.toMonoidHom ē.injective).trans (MulEquiv.subgroupCongr hmap)) h

theorem normal_inf_subgroupOf {Y : Type} [Group Y] (P Ls : Subgroup Y) (hnorm : Ls.Normal) :
    ((P ⊓ Ls).subgroupOf P).Normal := by
  have h : (P ⊓ Ls).subgroupOf P = Ls.subgroupOf P := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  rw [h]
  exact hnorm.subgroupOf P

end R1511C

theorem isPComponent_quot_equiv {P : Type} [Group P] [Finite P] {L : Subgroup P}
    (hL : CFSG.IsPComponent 3 L) :
    Nonempty ((↥L ⧸ CFSG.pPrimeCore 3 ↥L) ≃*
      ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 P)))) := by
  obtain ⟨-, -, hLs, -, -⟩ := hL
  have hker : ((QuotientGroup.mk' (CFSG.pPrimeCore 3 P)).subgroupMap L).ker =
      CFSG.pPrimeCore 3 ↥L := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact R1511C.subgroupOf_pPrimeCore_eq hLs
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (MonoidHom.subgroupMap_surjective _ L))⟩

end ThreeComponent

end CFSG.LocalAnalysis.RankThreeUC.S15
