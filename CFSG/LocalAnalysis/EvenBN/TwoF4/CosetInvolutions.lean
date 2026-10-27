module

public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CommutatorMap

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {t s : G} (ht : t * t = 1) (hs : s ∈ zpowers t) :
    s = 1 ∨ s = t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

structure FreeSeries (t : G) {r : ℕ} (V : Fin (r + 1) → Subgroup G) : Prop where
  bot : V 0 = ⊥
  le_succ : ∀ i : Fin r, V i.castSucc ≤ V i.succ
  le_normalizer : ∀ i : Fin r, V i.succ ≤ normalizer (V i.castSucc : Set G)
  mem_normalizer : ∀ i, t ∈ normalizer (V i : Set G)
  mul_self_mem : ∀ i : Fin r, ∀ x ∈ V i.succ, x * x ∈ V i.castSucc
  exists_commutator : ∀ i : Fin r, ∀ x ∈ V i.succ, t⁻¹ * x⁻¹ * t * x ∈ V i.castSucc →
    ∃ y ∈ V i.succ, x⁻¹ * (y⁻¹ * (t⁻¹ * y * t)) ∈ V i.castSucc

theorem isElementaryAbelian_quotient_of_mul_self_mem {K L : Subgroup G}
    [(L.subgroupOf K).Normal] (h : ∀ x ∈ K, x * x ∈ L) :
    IsElementaryAbelian 2 (K ⧸ L.subgroupOf K) := by
  have hsq : ∀ q : K ⧸ L.subgroupOf K, q ^ 2 = 1 := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, pow_two]
    exact h k k.2
  exact { is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
            (fun g => orderOf_dvd_of_pow_eq_one (hsq g)) a b).eq⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

namespace FreeSeries

variable {t : G} {r : ℕ} {V : Fin (r + 1) → Subgroup G}

theorem isElementaryAbelian (h : FreeSeries t V) (i : Fin r)
    [((V i.castSucc).subgroupOf (V i.succ)).Normal] :
    IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ)) :=
  isElementaryAbelian_quotient_of_mul_self_mem (h.mul_self_mem i)

theorem fixed_eq_range (h : FreeSeries t V) (ht : t * t = 1) (i : Fin r)
    [((V i.castSucc).subgroupOf (V i.succ)).Normal] :
    {q | sectionRightConj (h.mem_normalizer i.succ) (h.mem_normalizer i.castSucc) q = q} =
      Set.range fun q =>
        q⁻¹ * sectionRightConj (h.mem_normalizer i.succ) (h.mem_normalizer i.castSucc) q := by
  have := h.isElementaryAbelian i
  have hinv : ∀ u : V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ), u⁻¹ = u :=
    fun u => inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian_two u)
  ext q
  constructor
  · intro hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk := (sectionRightConj_mk_eq_iff (h.mem_normalizer i.succ)
      (h.mem_normalizer i.castSucc) k).mp hq
    obtain ⟨y, hy, hky⟩ := h.exists_commutator i k k.2 hk
    have hyt : t⁻¹ * y * t ∈ V i.succ := inv_mul_mul_mem_of_mem_normalizer (h.mem_normalizer _) hy
    refine ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
    beta_reduce
    rw [sectionRightConj_mk (h.mem_normalizer i.succ) (h.mem_normalizer i.castSucc) ⟨y, hy⟩
      ⟨t⁻¹ * y * t, hyt⟩ rfl, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, eq_comm,
      QuotientGroup.eq, mem_subgroupOf]
    exact hky
  · rintro ⟨p, rfl⟩
    change sectionRightConj (h.mem_normalizer i.succ) (h.mem_normalizer i.castSucc)
      (p⁻¹ * sectionRightConj (h.mem_normalizer i.succ) (h.mem_normalizer i.castSucc) p) =
        p⁻¹ * sectionRightConj (h.mem_normalizer i.succ) (h.mem_normalizer i.castSucc) p
    rw [map_mul, map_inv, Common.sectionRightConj_sectionRightConj _ _ ht]
    simp only [hinv]
    exact mul_comm' _ _

theorem exists_conj_eq (h : FreeSeries t V) (ht : t * t = 1) (i : Fin (r + 1)) {y : G}
    (hy : y ∈ V i) (hsq : t * y * (t * y) = 1) : ∃ x ∈ V i, t * y = x⁻¹ * t * x := by
  induction i using Fin.induction generalizing y with
  | zero =>
    rw [h.bot, mem_bot] at hy
    subst hy
    exact ⟨1, one_mem _, by group⟩
  | succ i ih =>
    have : ((V i.castSucc).subgroupOf (V i.succ)).Normal :=
      (normal_subgroupOf_iff_le_normalizer (h.le_succ i)).mpr (h.le_normalizer i)
    have := h.isElementaryAbelian i
    exact coset_conj_of_section (h.le_succ i) (h.mem_normalizer i.succ)
      (h.mem_normalizer i.castSucc) ht (h.fixed_eq_range ht i) (fun l hl hl2 => ih hl hl2) hy hsq

theorem involution_coset_eq (h : FreeSeries t V) (ht : orderOf t = 2) :
    {x | (∃ y ∈ V (Fin.last r), x = t * y) ∧ orderOf x = 2} =
      {x | ∃ y ∈ V (Fin.last r), x = y⁻¹ * t * y} := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hx⟩
    have hx2 : t * y * (t * y) = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    exact h.exists_conj_eq ht2 _ hy hx2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨t⁻¹ * y⁻¹ * t * y,
      mul_mem (inv_mul_mul_mem_of_mem_normalizer (h.mem_normalizer _) (inv_mem hy)) hy,
      by group⟩, ?_⟩
    have h1 := MulEquiv.orderOf_eq (MulAut.conj y⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [h1, ht]

theorem sectionCentralizer_eq [Finite G] (h : FreeSeries t V) (ht : t * t = 1) :
    sectionCentralizer (zpowers t ⊔ V (Fin.last r)) (V (Fin.last r)) =
      V (Fin.last r) ⊔ (normalizer (V (Fin.last r) : Set G) ⊓ centralizer ({t} : Set G)) := by
  have htX : t ∈ normalizer (V (Fin.last r) : Set G) := h.mem_normalizer _
  apply le_antisymm
  · intro g hg
    rw [mem_sectionCentralizer_zpowers_sup_iff htX] at hg
    obtain ⟨hgX, hgt⟩ := hg
    have hsq : t * (t⁻¹ * g⁻¹ * t * g) * (t * (t⁻¹ * g⁻¹ * t * g)) = 1 := by
      calc t * (t⁻¹ * g⁻¹ * t * g) * (t * (t⁻¹ * g⁻¹ * t * g)) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [ht]; group
    obtain ⟨x, hx, hxe⟩ := h.exists_conj_eq ht _ hgt hsq
    have h1 : g⁻¹ * t * g = x⁻¹ * t * x := by rw [← hxe]; group
    have hc : g * x⁻¹ ∈ normalizer (V (Fin.last r) : Set G) ⊓ centralizer ({t} : Set G) := by
      refine ⟨mul_mem hgX (Subgroup.le_normalizer (inv_mem hx)), ?_⟩
      show g * x⁻¹ ∈ centralizer ({t} : Set G)
      rw [mem_centralizer_singleton_iff]
      calc g * x⁻¹ * t = g * (x⁻¹ * t * x) * x⁻¹ := by group
        _ = g * (g⁻¹ * t * g) * x⁻¹ := by rw [h1]
        _ = t * (g * x⁻¹) := by group
    have hg : g = (g * x⁻¹) * x := by group
    rw [hg]
    exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
  · refine sup_le (fun x hx => ?_) (fun c hc => ?_)
    · rw [mem_sectionCentralizer_zpowers_sup_iff htX]
      exact ⟨Subgroup.le_normalizer hx,
        mul_mem (inv_mul_mul_mem_of_mem_normalizer htX (inv_mem hx)) hx⟩
    · rw [mem_sectionCentralizer_zpowers_sup_iff htX]
      refine ⟨hc.1, ?_⟩
      have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hc.2
      have h1 : t⁻¹ * c⁻¹ * t * c = 1 := by
        calc t⁻¹ * c⁻¹ * t * c = t⁻¹ * c⁻¹ * (t * c) := by group
          _ = 1 := by rw [← hct]; group
      rw [h1]
      exact one_mem _

end FreeSeries

theorem miyamoto_lemma_1_3 [Finite G] {t : G} (ht : orderOf t = 2) {r : ℕ}
    {V : Fin (r + 1) → Subgroup G} (h : FreeSeries t V) :
    {x | (∃ y ∈ V (Fin.last r), x = t * y) ∧ orderOf x = 2} =
        {x | ∃ y ∈ V (Fin.last r), x = y⁻¹ * t * y} ∧
      sectionCentralizer (zpowers t ⊔ V (Fin.last r)) (V (Fin.last r)) =
        V (Fin.last r) ⊔ (normalizer (V (Fin.last r) : Set G) ⊓ centralizer ({t} : Set G)) :=
  ⟨h.involution_coset_eq ht,
    h.sectionCentralizer_eq (by rw [← pow_two, ← ht, pow_orderOf_eq_one])⟩

end CFSG.LocalAnalysis.EvenBN.TwoF4
