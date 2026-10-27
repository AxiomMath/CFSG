module

public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.Group

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}

def primeTIset (W₁ W₂ : Subgroup L) : Set L :=
  ((W₁ ⊔ W₂ : Subgroup L) : Set L) \ (W₂ : Set L)

def cyclicTIset (W₁ W₂ : Subgroup L) : Set L :=
  ((W₁ ⊔ W₂ : Subgroup L) : Set L) \ ((W₁ : Set L) ∪ (W₂ : Set L))

@[simp] theorem mem_primeTIset {z : L} :
    z ∈ primeTIset W₁ W₂ ↔ z ∈ W₁ ⊔ W₂ ∧ z ∉ W₂ := Iff.rfl

@[simp] theorem mem_cyclicTIset {z : L} :
    z ∈ cyclicTIset W₁ W₂ ↔ z ∈ W₁ ⊔ W₂ ∧ z ∉ W₁ ∧ z ∉ W₂ := by
  simp only [cyclicTIset, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]

theorem cyclicTIset_subset_primeTIset : cyclicTIset W₁ W₂ ⊆ primeTIset W₁ W₂ :=
  fun _ hz => ⟨(mem_cyclicTIset.1 hz).1, (mem_cyclicTIset.1 hz).2.2⟩

theorem primeTIset_subset_coe : primeTIset W₁ W₂ ⊆ ((W₁ ⊔ W₂ : Subgroup L) : Set L) :=
  fun _ hz => hz.1

theorem cyclicTIset_subset_coe : cyclicTIset W₁ W₂ ⊆ ((W₁ ⊔ W₂ : Subgroup L) : Set L) :=
  cyclicTIset_subset_primeTIset.trans primeTIset_subset_coe

theorem one_notMem_primeTIset : (1 : L) ∉ primeTIset W₁ W₂ := fun hz => hz.2 (one_mem W₂)

theorem one_notMem_cyclicTIset : (1 : L) ∉ cyclicTIset W₁ W₂ :=
  fun hz => one_notMem_primeTIset (cyclicTIset_subset_primeTIset hz)

section Transporter

variable {S : Set L} {W : Subgroup L} (hS : S.Nonempty) (h1 : (1 : L) ∉ S)
  (htr : ∀ z ∈ S, ∀ g : L, g⁻¹ * z * g ∈ S ↔ g ∈ W)

include hS htr

theorem setOf_conj_image_eq_self_of_transporter :
    {g : L | (fun x => g⁻¹ * x * g) '' S = S} = (W : Set L) := by
  ext g
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  refine ⟨fun hg => ?_, fun hg => Set.eq_of_subset_of_subset ?_ ?_⟩
  · obtain ⟨z, hz⟩ := hS
    exact (htr z hz g).1 (hg ▸ Set.mem_image_of_mem _ hz)
  · rintro y ⟨z, hz, rfl⟩
    exact (htr z hz g).2 hg
  · intro y hy
    refine ⟨g * y * g⁻¹, ?_, by group⟩
    simpa using (htr y hy g⁻¹).2 (inv_mem hg)

theorem normalizer_eq_of_transporter : Subgroup.normalizer S = W := by
  ext g
  rw [Subgroup.mem_set_normalizer_iff'']
  refine ⟨fun hg => ?_, fun hg y => ⟨fun hy => (htr y hy g).2 hg, fun hy => ?_⟩⟩
  · obtain ⟨z, hz⟩ := hS
    exact (htr z hz g).1 ((hg z).1 hz)
  · have h2 := (htr _ hy g⁻¹).2 (inv_mem hg)
    have he : g⁻¹⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [he] at h2

omit hS in
theorem conj_image_inter_eq_empty_of_transporter {g : L} (hg : g ∉ W) :
    (fun x => g⁻¹ * x * g) '' S ∩ S = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨⟨z, hz, rfl⟩, hy⟩
  exact hg ((htr z hz g).1 hy)

include h1 in
theorem isTIWithNormalizer_of_transporter : IsTIWithNormalizer S W where
  nonempty := hS
  one_notMem := h1
  normalizer_eq := normalizer_eq_of_transporter hS htr
  disjoint_conj_image g hg := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, z, hz, rfl⟩
    have hgi : g⁻¹ ∉ W := fun hc => hg (by simpa using inv_mem hc)
    exact hgi ((htr z hz g⁻¹).1 (by simpa using hy))

end Transporter

structure IsPrimeCyclicTIHyp (K W₁ W₂ : Subgroup L) : Prop where
  normal : K.Normal
  mul_eq_univ : (K : Set L) * (W₁ : Set L) = Set.univ
  inf_eq_bot : K ⊓ W₁ = ⊥
  coprime_natCard : (Nat.card K).Coprime (Nat.card W₁)
  left_ne_bot : W₁ ≠ ⊥
  right_ne_bot : W₂ ≠ ⊥
  isCyclic_left : IsCyclic W₁
  isCyclic_right : IsCyclic W₂
  right_le : W₂ ≤ K
  centralizer_eq : ∀ x ∈ W₁, x ≠ 1 → K ⊓ centralizer {x} = W₂
  odd_natCard : Odd (Nat.card W₁ * Nat.card W₂)

namespace IsPrimeCyclicTIHyp

variable (h : IsPrimeCyclicTIHyp K W₁ W₂)

include h

theorem inf_left_right_eq_bot : W₁ ⊓ W₂ = ⊥ := by
  rw [eq_bot_iff, ← h.inf_eq_bot]
  exact le_inf (inf_le_right.trans h.right_le) inf_le_left

theorem coprime_natCard_left_right : (Nat.card W₁).Coprime (Nat.card W₂) :=
  h.coprime_natCard.symm.coprime_dvd_right (card_dvd_of_le h.right_le)

theorem commute_left_right : ∀ x ∈ W₁, ∀ y ∈ W₂, Commute x y := by
  intro x hx y hy
  rcases eq_or_ne x 1 with rfl | hx1
  · exact Commute.one_left y
  · have hmem : y ∈ K ⊓ centralizer ({x} : Set L) := by
      rw [h.centralizer_eq x hx hx1]; exact hy
    exact (mem_centralizer_singleton_iff.1 (mem_inf.1 hmem).2).symm

theorem coe_sup_eq_mul : ((W₁ ⊔ W₂ : Subgroup L) : Set L) = (W₁ : Set L) * (W₂ : Set L) :=
  coe_mul_of_left_le_normalizer_right _ _ fun x hx => centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun y hy => (h.commute_left_right x hx y hy).symm.eq)

theorem exists_mul_eq_of_mem_sup {z : L} (hz : z ∈ W₁ ⊔ W₂) :
    ∃ x ∈ W₁, ∃ y ∈ W₂, x * y = z := by
  rw [← SetLike.mem_coe, h.coe_sup_eq_mul] at hz
  obtain ⟨x, hx, y, hy, hxy⟩ := hz
  exact ⟨x, hx, y, hy, hxy⟩

theorem exists_decomp (g : L) : ∃ k ∈ K, ∃ w ∈ W₁, k * w = g := by
  have hg : g ∈ (K : Set L) * (W₁ : Set L) := by rw [h.mul_eq_univ]; trivial
  obtain ⟨k, hk, w, hw, hkw⟩ := hg
  exact ⟨k, hk, w, hw, hkw⟩

theorem exists_pow_proj : ∃ a : ℕ, ∀ z ∈ W₁ ⊔ W₂, z ^ a ∈ W₁ ∧ (z ^ a = 1 ↔ z ∈ W₂) := by
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder h.coprime_natCard_left_right 1 0
  refine ⟨a, fun z hz => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := h.exists_mul_eq_of_mem_sup hz
  have hxa : x ^ a = x := by
    rw [pow_eq_pow_iff_modEq.2 (ha1.of_dvd (Subgroup.orderOf_dvd_natCard W₁ hx)), pow_one]
  have hya : y ^ a = 1 := by
    rw [pow_eq_pow_iff_modEq.2 (ha2.of_dvd (Subgroup.orderOf_dvd_natCard W₂ hy)), pow_zero]
  have hzz : (x * y) ^ a = x := by
    rw [(h.commute_left_right x hx y hy).mul_pow, hxa, hya, mul_one]
  rw [hzz]
  refine ⟨hx, ⟨fun hx1 => by rw [hx1, one_mul]; exact hy, fun hmem => ?_⟩⟩
  have hxW₂ : x ∈ W₂ := by
    have hxe : x = x * y * y⁻¹ := by group
    rw [hxe]; exact W₂.mul_mem hmem (W₂.inv_mem hy)
  have hb := mem_inf.2 ⟨hx, hxW₂⟩
  rw [h.inf_left_right_eq_bot] at hb
  exact mem_bot.1 hb

theorem exists_zpowers_eq_sup : ∃ c : L, zpowers c = W₁ ⊔ W₂ := by
  obtain ⟨a, ha⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top W₁).1 h.isCyclic_left
  obtain ⟨b, hb⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top W₂).1 h.isCyclic_right
  have haW : a ∈ W₁ := ha ▸ mem_zpowers a
  have hbW : b ∈ W₂ := hb ▸ mem_zpowers b
  have hcomm : Commute a b := h.commute_left_right a haW b hbW
  have hda : orderOf a ∣ Nat.card W₁ := Subgroup.orderOf_dvd_natCard W₁ haW
  have hdb : orderOf b ∣ Nat.card W₂ := Subgroup.orderOf_dvd_natCard W₂ hbW
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder h.coprime_natCard_left_right 1 0
  obtain ⟨m, hm1, hm2⟩ := Nat.chineseRemainder h.coprime_natCard_left_right 0 1
  refine ⟨a * b, le_antisymm (zpowers_le.2 (mul_mem_sup haW hbW)) (sup_le ?_ ?_)⟩
  · rw [← ha, zpowers_le]
    refine mem_zpowers_iff.2 ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, hcomm.mul_pow, pow_eq_pow_iff_modEq.2 (hn1.of_dvd hda),
      pow_eq_pow_iff_modEq.2 (hn2.of_dvd hdb), pow_one, pow_zero, mul_one]
  · rw [← hb, zpowers_le]
    refine mem_zpowers_iff.2 ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast, hcomm.mul_pow, pow_eq_pow_iff_modEq.2 (hm1.of_dvd hda),
      pow_eq_pow_iff_modEq.2 (hm2.of_dvd hdb), pow_one, pow_zero, one_mul]

theorem isCyclic_sup : IsCyclic (W₁ ⊔ W₂ : Subgroup L) :=
  (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).2 h.exists_zpowers_eq_sup

theorem commute_of_mem_sup {u v : L} (hu : u ∈ W₁ ⊔ W₂) (hv : v ∈ W₁ ⊔ W₂) : Commute u v := by
  obtain ⟨c, hc⟩ := h.exists_zpowers_eq_sup
  rw [← hc] at hu hv
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
  exact (Commute.refl c).zpow_zpow i j

theorem conj_eq_self_of_mem_sup {z g : L} (hz : z ∈ W₁ ⊔ W₂) (hg : g ∈ W₁ ⊔ W₂) :
    g⁻¹ * z * g = z := by
  rw [mul_assoc, (h.commute_of_mem_sup hz hg).eq, inv_mul_cancel_left]

theorem mem_sup_of_conj_mem_primeTIset {z : L} (hz : z ∈ primeTIset W₁ W₂) {g : L}
    (hzg : g⁻¹ * z * g ∈ primeTIset W₁ W₂) : g ∈ W₁ ⊔ W₂ := by
  obtain ⟨a, ha⟩ := h.exists_pow_proj
  obtain ⟨hzW, hzW₂⟩ := hz
  obtain ⟨hzgW, -⟩ := hzg
  set x := z ^ a with hxdef
  have hxW₁ : x ∈ W₁ := (ha z hzW).1
  have hx1 : x ≠ 1 := fun hc => hzW₂ ((ha z hzW).2.1 hc)
  have hconj : (g⁻¹ * z * g) ^ a = g⁻¹ * x * g := by
    simpa [hxdef] using conj_pow (a := g⁻¹) (b := z) (i := a)
  have hxgW₁ : g⁻¹ * x * g ∈ W₁ := by rw [← hconj]; exact (ha _ hzgW).1
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp g
  have hxk : k⁻¹ * x * k ∈ W₁ := by
    have hrw : k⁻¹ * x * k = w * ((k * w)⁻¹ * x * (k * w)) * w⁻¹ := by group
    rw [hrw]
    exact W₁.mul_mem (W₁.mul_mem hw hxgW₁) (W₁.inv_mem hw)
  have hK := h.normal
  have hmemK : (k⁻¹ * x * k) * x⁻¹ ∈ K := by
    have hrw : (k⁻¹ * x * k) * x⁻¹ = k⁻¹ * (x * k * x⁻¹) := by group
    rw [hrw]
    exact K.mul_mem (K.inv_mem hk) (hK.conj_mem k hk x)
  have hxkx : k⁻¹ * x * k = x := by
    have hmem : (k⁻¹ * x * k) * x⁻¹ ∈ K ⊓ W₁ :=
      mem_inf.2 ⟨hmemK, W₁.mul_mem hxk (W₁.inv_mem hxW₁)⟩
    rw [h.inf_eq_bot] at hmem
    exact mul_inv_eq_one.1 (mem_bot.1 hmem)
  have hkW₂ : k ∈ W₂ := by
    rw [← h.centralizer_eq x hxW₁ hx1]
    refine mem_inf.2 ⟨hk, mem_centralizer_singleton_iff.2 ?_⟩
    calc k * x = k * (k⁻¹ * x * k) := by rw [hxkx]
    _ = x * k := by group
  exact mul_mem (mem_sup_right hkW₂) (mem_sup_left hw)

theorem conj_mem_primeTIset_iff {z : L} (hz : z ∈ primeTIset W₁ W₂) (g : L) :
    g⁻¹ * z * g ∈ primeTIset W₁ W₂ ↔ g ∈ W₁ ⊔ W₂ := by
  refine ⟨h.mem_sup_of_conj_mem_primeTIset hz, fun hg => ?_⟩
  rw [h.conj_eq_self_of_mem_sup hz.1 hg]; exact hz

theorem conj_eq_self_of_mem_primeTIset {z : L} (hz : z ∈ primeTIset W₁ W₂) {g : L}
    (hg : g⁻¹ * z * g ∈ primeTIset W₁ W₂) : g⁻¹ * z * g = z :=
  h.conj_eq_self_of_mem_sup hz.1 (h.mem_sup_of_conj_mem_primeTIset hz hg)

theorem conj_mem_cyclicTIset_iff {z : L} (hz : z ∈ cyclicTIset W₁ W₂) (g : L) :
    g⁻¹ * z * g ∈ cyclicTIset W₁ W₂ ↔ g ∈ W₁ ⊔ W₂ := by
  refine ⟨fun hzg => h.mem_sup_of_conj_mem_primeTIset (cyclicTIset_subset_primeTIset hz)
    (cyclicTIset_subset_primeTIset hzg), fun hg => ?_⟩
  rw [h.conj_eq_self_of_mem_sup (mem_cyclicTIset.1 hz).1 hg]; exact hz

theorem nonempty_cyclicTIset : (cyclicTIset W₁ W₂).Nonempty := by
  obtain hb | ⟨x, hx, hx1⟩ := W₁.bot_or_exists_ne_one
  · exact absurd hb h.left_ne_bot
  obtain hb | ⟨y, hy, hy1⟩ := W₂.bot_or_exists_ne_one
  · exact absurd hb h.right_ne_bot
  refine ⟨x * y, mem_cyclicTIset.2 ⟨mul_mem_sup hx hy, ?_, ?_⟩⟩
  · intro hmem
    have hy' : y ∈ W₁ ⊓ W₂ := mem_inf.2 ⟨by
      have he : y = x⁻¹ * (x * y) := by group
      rw [he]; exact W₁.mul_mem (W₁.inv_mem hx) hmem, hy⟩
    rw [h.inf_left_right_eq_bot] at hy'
    exact hy1 (mem_bot.1 hy')
  · intro hmem
    have hx' : x ∈ W₁ ⊓ W₂ := mem_inf.2 ⟨hx, by
      have he : x = x * y * y⁻¹ := by group
      rw [he]; exact W₂.mul_mem hmem (W₂.inv_mem hy)⟩
    rw [h.inf_left_right_eq_bot] at hx'
    exact hx1 (mem_bot.1 hx')

theorem nonempty_primeTIset : (primeTIset W₁ W₂).Nonempty :=
  h.nonempty_cyclicTIset.mono cyclicTIset_subset_primeTIset

theorem isTIWithNormalizer_primeTIset : IsTIWithNormalizer (primeTIset W₁ W₂) (W₁ ⊔ W₂) :=
  isTIWithNormalizer_of_transporter h.nonempty_primeTIset one_notMem_primeTIset
    fun _ hz g => h.conj_mem_primeTIset_iff hz g

theorem isTIWithNormalizer_cyclicTIset : IsTIWithNormalizer (cyclicTIset W₁ W₂) (W₁ ⊔ W₂) :=
  isTIWithNormalizer_of_transporter h.nonempty_cyclicTIset one_notMem_cyclicTIset
    fun _ hz g => h.conj_mem_cyclicTIset_iff hz g

theorem setOf_conj_image_primeTIset_eq_self :
    {g : L | (fun x => g⁻¹ * x * g) '' primeTIset W₁ W₂ = primeTIset W₁ W₂}
      = ((W₁ ⊔ W₂ : Subgroup L) : Set L) :=
  setOf_conj_image_eq_self_of_transporter h.nonempty_primeTIset
    fun _ hz g => h.conj_mem_primeTIset_iff hz g

theorem setOf_conj_image_cyclicTIset_eq_self :
    {g : L | (fun x => g⁻¹ * x * g) '' cyclicTIset W₁ W₂ = cyclicTIset W₁ W₂}
      = ((W₁ ⊔ W₂ : Subgroup L) : Set L) :=
  setOf_conj_image_eq_self_of_transporter h.nonempty_cyclicTIset
    fun _ hz g => h.conj_mem_cyclicTIset_iff hz g

theorem conj_image_primeTIset_inter_eq_empty {g : L} (hg : g ∉ W₁ ⊔ W₂) :
    (fun x => g⁻¹ * x * g) '' primeTIset W₁ W₂ ∩ primeTIset W₁ W₂ = ∅ :=
  conj_image_inter_eq_empty_of_transporter (fun _ hz g => h.conj_mem_primeTIset_iff hz g) hg

theorem conj_image_cyclicTIset_inter_eq_empty {g : L} (hg : g ∉ W₁ ⊔ W₂) :
    (fun x => g⁻¹ * x * g) '' cyclicTIset W₁ W₂ ∩ cyclicTIset W₁ W₂ = ∅ :=
  conj_image_inter_eq_empty_of_transporter (fun _ hz g => h.conj_mem_cyclicTIset_iff hz g) hg

end IsPrimeCyclicTIHyp

end

end CFSG.FeitThompson
