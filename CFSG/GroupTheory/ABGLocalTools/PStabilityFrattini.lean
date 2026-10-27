module

import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

open Subgroup

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem pPrimeCore_sup_normalizer_eq_top {P : Subgroup H} (hP : IsPGroup p P)
    (hn : (pPrimeCore p H ⊔ P).Normal) : pPrimeCore p H ⊔ normalizer (P : Set H) = ⊤ := by
  have hsyl : IsSylowOf p P (pPrimeCore p H ⊔ P) :=
    isSylowOf_sup_of_coprime pPrimeCore_coprime_card hP
  obtain ⟨Q, hQ⟩ := hsyl
  have h := Sylow.normalizer_sup_eq_top Q
  rw [hQ] at h
  rw [eq_top_iff, ← h]
  exact sup_le (le_sup_right) (sup_le le_sup_left (le_normalizer.trans le_sup_right))

theorem normalizer_inf_pPrimeCore_le_centralizer {P : Subgroup H} (hP : IsPGroup p P) :
    normalizer (P : Set H) ⊓ pPrimeCore p H ≤ centralizer (P : Set H) := by
  rintro x ⟨hxN, hxO⟩
  rw [mem_centralizer_iff]
  intro u hu
  have hcP : x * u * x⁻¹ * u⁻¹ ∈ P := mul_mem ((mem_normalizer_iff.mp hxN u).mp hu) (inv_mem hu)
  have hcO : x * u * x⁻¹ * u⁻¹ ∈ pPrimeCore p H := by
    have h1 : u * x⁻¹ * u⁻¹ ∈ pPrimeCore p H :=
      (pPrimeCore_normal (p := p) (G := H)).conj_mem _ (inv_mem hxO) u
    have := mul_mem hxO h1
    simpa [mul_assoc] using this
  have hbot : P ⊓ pPrimeCore p H = ⊥ := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    apply disjoint_iff.mp (disjoint_of_coprime_natCard _)
    rw [hk]
    exact (pPrimeCore_coprime_card (p := p) (G := H)).pow_left k
  have h1 : x * u * x⁻¹ * u⁻¹ = 1 := by
    have : x * u * x⁻¹ * u⁻¹ ∈ P ⊓ pPrimeCore p H := ⟨hcP, hcO⟩
    rwa [hbot, mem_bot] at this
  have h2 : x * u = u * x := by
    calc x * u = x * u * x⁻¹ * u⁻¹ * (u * x) := by group
      _ = u * x := by rw [h1, one_mul]
  exact h2.symm

omit [Finite H] [Fact p.Prime] in
theorem sup_pPrimeCore_normal {N K : Subgroup H} (hKN : N ≤ normalizer (K : Set H))
    (htop : pPrimeCore p H ⊔ N = ⊤) : (K ⊔ pPrimeCore p H).Normal := by
  have hO : (pPrimeCore p H).Normal := pPrimeCore_normal
  set f := QuotientGroup.mk' (pPrimeCore p H) with hf
  have hNtop : N.map f = ⊤ := by
    have h := congrArg (map f) htop
    rwa [Subgroup.map_sup, hf, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  have hKn : (K.map f).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hNtop]
    exact (map_mono hKN).trans (le_normalizer_map f)
  have := hKn.comap f
  rwa [comap_map_eq, hf, QuotientGroup.ker_mk'] at this

omit [Finite H] [Fact p.Prime] in
theorem inf_sup_pPrimeCore_eq {N K : Subgroup H} (hKN : K ≤ N)
    (hNO : N ⊓ pPrimeCore p H ≤ K) : N ⊓ (K ⊔ pPrimeCore p H) = K := by
  have hO : (pPrimeCore p H).Normal := pPrimeCore_normal
  apply le_antisymm _ (le_inf hKN le_sup_left)
  rintro x ⟨hxN, hxKO⟩
  have hxKO' : x ∈ ((K ⊔ pPrimeCore p H : Subgroup H) : Set H) := hxKO
  rw [mul_normal] at hxKO'
  obtain ⟨k, hk, o, ho, rfl⟩ := hxKO'
  have hoN : o ∈ N := by
    have := mul_mem (inv_mem (hKN hk)) hxN
    simpa using this
  exact mul_mem hk (hNO ⟨hoN, ho⟩)

@[expose] noncomputable def normalizerQuotientHom (P K : Subgroup H) [(K ⊔ pPrimeCore p H).Normal] :
    normalizer (P : Set H) →* H ⧸ (K ⊔ pPrimeCore p H) :=
  (QuotientGroup.mk' (K ⊔ pPrimeCore p H)).comp (normalizer (P : Set H)).subtype

theorem normalizerQuotientHom_surjective {P K : Subgroup H} [(K ⊔ pPrimeCore p H).Normal]
    (hP : IsPGroup p P) (hn : (pPrimeCore p H ⊔ P).Normal) :
    Function.Surjective (normalizerQuotientHom (p := p) P K) := by
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  have hO : (pPrimeCore p H).Normal := pPrimeCore_normal
  have hh : h ∈ (pPrimeCore p H ⊔ normalizer (P : Set H) : Subgroup H) := by
    rw [pPrimeCore_sup_normalizer_eq_top hP hn]
    exact mem_top h
  have hh' : h ∈ ((pPrimeCore p H ⊔ normalizer (P : Set H) : Subgroup H) : Set H) := hh
  rw [normal_mul] at hh'
  obtain ⟨o, ho, n, hn', rfl⟩ := hh'
  refine ⟨⟨n, hn'⟩, ?_⟩
  change (QuotientGroup.mk n : H ⧸ (K ⊔ pPrimeCore p H)) = QuotientGroup.mk (o * n)
  rw [QuotientGroup.eq]
  have h1 : n⁻¹ * o * n ∈ pPrimeCore p H := by
    simpa using (pPrimeCore_normal (p := p) (G := H)).conj_mem o ho n⁻¹
  have h2 : n⁻¹ * (o * n) = n⁻¹ * o * n := by group
  rw [h2]
  exact le_sup_right (a := K) h1

omit [Finite H] [Fact p.Prime] in
theorem normalizerQuotientHom_ker {P K : Subgroup H} [(K ⊔ pPrimeCore p H).Normal]
    (hKN : K ≤ normalizer (P : Set H)) (hNO : normalizer (P : Set H) ⊓ pPrimeCore p H ≤ K) :
    (normalizerQuotientHom (p := p) P K).ker = K.subgroupOf (normalizer (P : Set H)) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  change (QuotientGroup.mk (n : H) : H ⧸ (K ⊔ pPrimeCore p H)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro h
    have hmem : (n : H) ∈ normalizer (P : Set H) ⊓ (K ⊔ pPrimeCore p H) := ⟨n.2, h⟩
    rwa [inf_sup_pPrimeCore_eq hKN hNO] at hmem
  · intro h
    exact le_sup_left (b := pPrimeCore p H) h

@[expose] noncomputable def normalizerQuotientEquiv {P K : Subgroup H} [(K ⊔ pPrimeCore p H).Normal]
    [(K.subgroupOf (normalizer (P : Set H))).Normal] (hP : IsPGroup p P)
    (hn : (pPrimeCore p H ⊔ P).Normal) (hKN : K ≤ normalizer (P : Set H))
    (hNO : normalizer (P : Set H) ⊓ pPrimeCore p H ≤ K) :
    normalizer (P : Set H) ⧸ K.subgroupOf (normalizer (P : Set H)) ≃*
      H ⧸ (K ⊔ pPrimeCore p H) :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerQuotientHom_ker hKN hNO).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (normalizerQuotientHom_surjective hP hn))

theorem normalizerQuotientEquiv_apply {P K : Subgroup H} [(K ⊔ pPrimeCore p H).Normal]
    [(K.subgroupOf (normalizer (P : Set H))).Normal] (hP : IsPGroup p P)
    (hn : (pPrimeCore p H ⊔ P).Normal) (hKN : K ≤ normalizer (P : Set H))
    (hNO : normalizer (P : Set H) ⊓ pPrimeCore p H ≤ K) (n : normalizer (P : Set H)) :
    normalizerQuotientEquiv hP hn hKN hNO (n : normalizer (P : Set H) ⧸ _) =
      ((n : H) : H ⧸ (K ⊔ pPrimeCore p H)) :=
  rfl

end CFSG.ABGLocalTools
