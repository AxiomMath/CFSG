module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup QuotientGroup

variable {q : ℕ} {X : Type*} [Group X] {B Y L : Subgroup X}

theorem isPGroup_zpowers_of_pow_eq_one (hq : q.Prime) {N : Type*} [Group N] {g : N} {n : ℕ}
    (h : g ^ q ^ n = 1) : IsPGroup q (zpowers g) := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hq).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

theorem le_sylow_of_isPGroup_of_isNilpotent {N : Type*} [Group N] [Finite N]
    [Group.IsNilpotent N] [Fact q.Prime] (S : Sylow q N) {T : Subgroup N}
    (hT : IsPGroup q T) : T ≤ (S : Subgroup N) := by
  obtain ⟨R, hR⟩ := hT.exists_le_sylow
  have := Sylow.unique_of_normal S inferInstance
  rwa [Subsingleton.elim R S] at hR

theorem mem_sup_iff_exists_pow_mem {N : Type*} [Group N] [Finite N]
    (hq : q.Prime) {C P : Subgroup N} [C.Normal] (hnil : Group.IsNilpotent (N ⧸ C))
    (hP : Nat.card P = q ^ (Nat.card N).factorization q) {g : N} :
    g ∈ C ⊔ P ↔ ∃ n : ℕ, g ^ q ^ n ∈ C := by
  have := Fact.mk hq
  have hT : ((Sylow.mapSurjective (mk'_surjective C) (Sylow.ofCard P hP) :
      Sylow q (N ⧸ C)) : Subgroup (N ⧸ C)) = P.map (mk' C) := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_ofCard]
  have hPgroup : IsPGroup q (P.map (mk' C) : Subgroup (N ⧸ C)) := by
    rw [← hT]; exact (Sylow.mapSurjective (mk'_surjective C) (Sylow.ofCard P hP)).isPGroup'
  constructor
  · intro hg
    have hmem : mk' C g ∈ P.map (mk' C) := by
      have hsup : (C ⊔ P).map (mk' C) = P.map (mk' C) := by
        rw [Subgroup.map_sup, map_mk'_self, bot_sup_eq]
      rw [← hsup]; exact mem_map_of_mem _ hg
    obtain ⟨n, hn⟩ := hPgroup ⟨mk' C g, hmem⟩
    refine ⟨n, ?_⟩
    have h1 : mk' C (g ^ q ^ n) = 1 := by
      rw [map_pow]; exact congrArg Subtype.val hn
    rwa [← ker_mk' C, MonoidHom.mem_ker]
  · rintro ⟨n, hn⟩
    have hz : IsPGroup q (zpowers (mk' C g)) := by
      refine isPGroup_zpowers_of_pow_eq_one hq (n := n) ?_
      rw [← map_pow, ← MonoidHom.mem_ker, ker_mk' C]
      exact hn
    have hle : zpowers (mk' C g) ≤ P.map (mk' C) := by
      rw [← hT]; exact le_sylow_of_isPGroup_of_isNilpotent _ hz
    have hmem : g ∈ Subgroup.comap (mk' C) (P.map (mk' C)) := hle (mem_zpowers _)
    rwa [Subgroup.comap_map_eq, ker_mk' C, sup_comm] at hmem

theorem mem_sup_iff_mem_and_exists_pow_mem [Finite X] (hq : q.Prime) [B.Normal]
    (hBL : B ≤ L) (hnil : Group.IsNilpotent (L ⧸ B.subgroupOf L)) (hYL : Y ≤ L)
    (hY : Nat.card Y = q ^ (Nat.card L).factorization q) {x : X} :
    x ∈ B ⊔ Y ↔ x ∈ L ∧ ∃ n : ℕ, x ^ q ^ n ∈ B := by
  have hYL' : Nat.card (Y.subgroupOf L) = q ^ (Nat.card L).factorization q := by
    rw [natCard_subgroupOf_of_le hYL, hY]
  constructor
  · intro hx
    have hxL : x ∈ L := sup_le hBL hYL hx
    refine ⟨hxL, ?_⟩
    have hx' : (⟨x, hxL⟩ : L) ∈ (B ⊔ Y).subgroupOf L := mem_subgroupOf.2 hx
    rw [subgroupOf_sup hBL hYL, mem_sup_iff_exists_pow_mem hq hnil hYL'] at hx'
    obtain ⟨n, hn⟩ := hx'
    exact ⟨n, by simpa using mem_subgroupOf.1 hn⟩
  · rintro ⟨hxL, n, hn⟩
    have hx' : (⟨x, hxL⟩ : L) ∈ (B ⊔ Y).subgroupOf L := by
      rw [subgroupOf_sup hBL hYL, mem_sup_iff_exists_pow_mem hq hnil hYL']
      exact ⟨n, mem_subgroupOf.2 (by simpa using hn)⟩
    exact mem_subgroupOf.1 hx'

theorem natCard_eq_pow_factorization_of_le_of_le [Finite X] (hq : q.Prime) {P H K : Subgroup X}
    (hPH : P ≤ H) (hHK : H ≤ K) (hP : Nat.card P = q ^ (Nat.card K).factorization q) :
    Nat.card P = q ^ (Nat.card H).factorization q := by
  have hle1 : (Nat.card H).factorization q ≤ (Nat.card K).factorization q :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hHK) q
  have hdvd : q ^ (Nat.card K).factorization q ∣ Nat.card H := hP ▸ Subgroup.card_dvd_of_le hPH
  have hle2 : (Nat.card K).factorization q ≤ (Nat.card H).factorization q :=
    (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hP, le_antisymm hle1 hle2]

theorem normal_sup_of_isNilpotent_quotient [Finite X] (hq : q.Prime) [B.Normal] [L.Normal]
    (hBL : B ≤ L) (hnil : Group.IsNilpotent (L ⧸ B.subgroupOf L)) (hYL : Y ≤ L)
    (hY : Nat.card Y = q ^ (Nat.card L).factorization q) : (B ⊔ Y).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_sup_iff_mem_and_exists_pow_mem hq hBL hnil hYL hY] at hx ⊢
  obtain ⟨hxL, n, hn⟩ := hx
  exact ⟨‹L.Normal›.conj_mem x hxL g, n, by rw [conj_pow]; exact ‹B.Normal›.conj_mem _ hn g⟩

theorem sup_normalizer_eq_top_of_isNilpotent_quotient [Finite X] (hq : q.Prime) [B.Normal]
    [L.Normal] (hBL : B ≤ L) (hnil : Group.IsNilpotent (L ⧸ B.subgroupOf L)) (hYL : Y ≤ L)
    (hY : Nat.card Y = q ^ (Nat.card L).factorization q) :
    B ⊔ normalizer (Y : Set X) = ⊤ := by
  have := Fact.mk hq
  have hnorm : (B ⊔ Y).Normal := normal_sup_of_isNilpotent_quotient hq hBL hnil hYL hY
  have hYS : Nat.card Y = q ^ (Nat.card (B ⊔ Y : Subgroup X)).factorization q :=
    natCard_eq_pow_factorization_of_le_of_le hq le_sup_right (sup_le hBL hYL) hY
  have h := sup_normalizer_eq_top_of_normal (R := B ⊔ Y) (P := Y) le_sup_right hYS
  refine le_antisymm le_top ?_
  rw [← h]
  exact sup_le (sup_le le_sup_left (le_sup_right.trans (sup_le_sup_left le_normalizer B)))
    le_sup_right

theorem sup_normalizer_eq_top_of_isNilpotent_derived_quotient [Finite X] (hq : q.Prime)
    [B.Normal] (hB : B ≤ commutator X)
    (hnil : Group.IsNilpotent (commutator X ⧸ B.subgroupOf (commutator X)))
    (hY : Y ≤ commutator X)
    (hYcard : Nat.card Y = q ^ (Nat.card (commutator X)).factorization q) :
    B ⊔ normalizer (Y : Set X) = ⊤ :=
  sup_normalizer_eq_top_of_isNilpotent_quotient hq hB hnil hY hYcard

theorem coe_mul_coe_normalizer_eq_univ_of_isNilpotent_derived_quotient [Finite X] (hq : q.Prime)
    [B.Normal] (hB : B ≤ commutator X)
    (hnil : Group.IsNilpotent (commutator X ⧸ B.subgroupOf (commutator X)))
    (hY : Y ≤ commutator X)
    (hYcard : Nat.card Y = q ^ (Nat.card (commutator X)).factorization q) :
    (B : Set X) * (normalizer (Y : Set X) : Set X) = Set.univ := by
  rw [← Subgroup.normal_mul B (normalizer (Y : Set X)),
    sup_normalizer_eq_top_of_isNilpotent_derived_quotient hq hB hnil hY hYcard,
    Subgroup.coe_top]

theorem exists_mem_mul_mem_normalizer_of_isNilpotent_derived_quotient [Finite X] (hq : q.Prime)
    [B.Normal] (hB : B ≤ commutator X)
    (hnil : Group.IsNilpotent (commutator X ⧸ B.subgroupOf (commutator X)))
    (hY : Y ≤ commutator X)
    (hYcard : Nat.card Y = q ^ (Nat.card (commutator X)).factorization q) (x : X) :
    ∃ b ∈ B, ∃ n ∈ normalizer (Y : Set X), x = b * n := by
  have hx : x ∈ (B : Set X) * (normalizer (Y : Set X) : Set X) := by
    rw [coe_mul_coe_normalizer_eq_univ_of_isNilpotent_derived_quotient hq hB hnil hY hYcard]
    trivial
  obtain ⟨b, hb, n, hn, hbn⟩ := hx
  exact ⟨b, hb, n, hn, hbn.symm⟩

theorem sylow_sup_normalizer_eq_top_of_isNilpotent_derived_quotient [Finite X] [Fact q.Prime]
    [B.Normal] (hB : B ≤ commutator X)
    (hnil : Group.IsNilpotent (commutator X ⧸ B.subgroupOf (commutator X)))
    (Y : Sylow q (commutator X)) :
    B ⊔ normalizer (((Y : Subgroup (commutator X)).map (commutator X).subtype : Subgroup X) :
      Set X) = ⊤ :=
  sup_normalizer_eq_top_of_isNilpotent_derived_quotient Fact.out hB hnil
    (Subgroup.map_subtype_le _)
    (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Y.card_eq_multiplicity])

end

end CFSG.FeitThompson
