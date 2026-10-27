module

public import CFSG.FeitThompson.Representations.ExtraspecialQuotientAlternatingForm
import Mathlib.FieldTheory.Finiteness

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Submodule

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {p : ℕ} {P : Type u} [Group P]

namespace IsExtraspecial

def projHom (h : IsExtraspecial p P) : P →* Multiplicative h.QuotientCenter where
  toFun x := Multiplicative.ofAdd (h.proj x)
  map_one' := by rw [h.proj_one]; rfl
  map_mul' x y := by rw [h.proj_mul]; rfl

@[simp]
theorem projHom_apply (h : IsExtraspecial p P) (x : P) :
    h.projHom x = Multiplicative.ofAdd (h.proj x) := (rfl)

theorem projHom_surjective (h : IsExtraspecial p P) : Function.Surjective h.projHom :=
  Multiplicative.ofAdd.surjective.comp h.proj_surjective

theorem ker_projHom (h : IsExtraspecial p P) : h.projHom.ker = Subgroup.center P := by
  ext x
  rw [MonoidHom.mem_ker, projHom_apply,
    show ((1 : Multiplicative h.QuotientCenter)) = Multiplicative.ofAdd 0 from rfl,
    Equiv.apply_eq_iff_eq, h.proj_eq_zero_iff]

theorem index_center (h : IsExtraspecial p P) :
    (Subgroup.center P).index = Nat.card h.QuotientCenter := by
  rw [← h.ker_projHom, Subgroup.index_ker, MonoidHom.range_eq_top.2 h.projHom_surjective]
  exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => Subgroup.mem_top x))).trans
    (Nat.card_congr Multiplicative.toAdd)

def preimage (h : IsExtraspecial p P) (L : Submodule (ZMod p) h.QuotientCenter) : Subgroup P :=
  (AddSubgroup.toSubgroup L.toAddSubgroup).comap h.projHom

theorem mem_preimage_iff (h : IsExtraspecial p P) {L : Submodule (ZMod p) h.QuotientCenter}
    {x : P} : x ∈ h.preimage L ↔ h.proj x ∈ L := Iff.rfl

theorem center_le_preimage (h : IsExtraspecial p P) (L : Submodule (ZMod p) h.QuotientCenter) :
    Subgroup.center P ≤ h.preimage L := fun x hx => by
  rw [mem_preimage_iff, h.proj_eq_zero_iff.2 hx]; exact L.zero_mem

@[simp]
theorem preimage_bot (h : IsExtraspecial p P) : h.preimage ⊥ = Subgroup.center P := by
  ext x; rw [mem_preimage_iff, Submodule.mem_bot, h.proj_eq_zero_iff]

@[simp]
theorem preimage_top (h : IsExtraspecial p P) : h.preimage ⊤ = ⊤ := by
  ext x; simp [mem_preimage_iff]

theorem preimage_mono (h : IsExtraspecial p P) {L M : Submodule (ZMod p) h.QuotientCenter}
    (hLM : L ≤ M) : h.preimage L ≤ h.preimage M := fun _ hx =>
  h.mem_preimage_iff.2 (hLM (h.mem_preimage_iff.1 hx))

instance (h : IsExtraspecial p P) (L : Submodule (ZMod p) h.QuotientCenter) :
    (h.preimage L).Normal :=
  Subgroup.Normal.comap (Subgroup.normal_of_isMulCommutative _) _

theorem index_preimage_mul_natCard (h : IsExtraspecial p P)
    (L : Submodule (ZMod p) h.QuotientCenter) :
    (h.preimage L).index * Nat.card L = Nat.card h.QuotientCenter := by
  rw [preimage, Subgroup.index_comap_of_surjective _ h.projHom_surjective]
  have h1 : Nat.card (AddSubgroup.toSubgroup L.toAddSubgroup) = Nat.card L :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun _ => Iff.rfl)
  rw [← h1, mul_comm, Subgroup.card_mul_index]
  exact Nat.card_congr Multiplicative.toAdd

theorem relIndex_center_preimage (h : IsExtraspecial p P)
    (L : Submodule (ZMod p) h.QuotientCenter) :
    (Subgroup.center P).relIndex (h.preimage L) = Nat.card L := by
  have := h.finite
  have hkey := Subgroup.relIndex_mul_index (h.center_le_preimage L)
  rw [h.index_center, ← h.index_preimage_mul_natCard L] at hkey
  have hne : (h.preimage L).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by rw [hkey]; ring)

section SelfOrthogonal

variable (h : IsExtraspecial p P) {z : P} (hz : Subgroup.zpowers z = Subgroup.center P)
  (hzo : orderOf z = p)

theorem commute_iff_commForm_proj_eq_zero {x y : P} :
    Commute x y ↔ h.commForm hz hzo (h.proj x) (h.proj y) = 0 := by
  have := NeZero.of_pos h.prime.pos
  rw [commForm_apply_proj_eq_iff hz hzo, ZMod.val_zero, pow_zero, eq_comm,
    commutatorElement_eq_one_iff_commute]

theorem commute_of_mem_preimage {L : Submodule (ZMod p) h.QuotientCenter}
    (hL : (h.commForm hz hzo).orthogonal L = L) {x y : P} (hx : x ∈ h.preimage L)
    (hy : y ∈ h.preimage L) : Commute x y := by
  have hyo : h.proj y ∈ (h.commForm hz hzo).orthogonal L := by
    rw [hL]; exact h.mem_preimage_iff.1 hy
  exact (commute_iff_commForm_proj_eq_zero h hz hzo).2
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hyo _ (h.mem_preimage_iff.1 hx))

theorem isMulCommutative_preimage {L : Submodule (ZMod p) h.QuotientCenter}
    (hL : (h.commForm hz hzo).orthogonal L = L) : IsMulCommutative (h.preimage L) :=
  ⟨⟨fun a b => Subtype.ext (commute_of_mem_preimage h hz hzo hL a.2 b.2)⟩⟩

theorem centralizer_preimage {L : Submodule (ZMod p) h.QuotientCenter}
    (hL : (h.commForm hz hzo).orthogonal L = L) :
    Subgroup.centralizer (h.preimage L : Set P) = h.preimage L := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_preimage_iff, ← hL, LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    obtain ⟨y, rfl⟩ := h.proj_surjective v
    have hc : Commute y x := Subgroup.mem_centralizer_iff.1 hx y (h.mem_preimage_iff.2 hv)
    exact (commute_iff_commForm_proj_eq_zero h hz hzo).1 hc
  · exact Subgroup.mem_centralizer_iff.2 fun y hy => commute_of_mem_preimage h hz hzo hL hy hx

end SelfOrthogonal

theorem exists_abelian_normal_polarization (h : IsExtraspecial p P) :
    ∃ (n : ℕ) (B : Subgroup P), 1 ≤ n ∧ IsMulCommutative B ∧ B.Normal ∧
      Subgroup.center P ≤ B ∧ Nat.card P = p ^ (2 * n + 1) ∧ B.index = p ^ n ∧
      (Subgroup.center P).relIndex B = p ^ n ∧ Subgroup.centralizer (B : Set P) = B := by
  have := Fact.mk h.prime
  have := h.finite
  have := h.nontrivial_quotientCenter
  have : Module.Finite (ZMod p) h.QuotientCenter := Module.Finite.of_finite
  have : FiniteDimensional (ZMod p) h.QuotientCenter := inferInstance
  obtain ⟨z, hz, hzo⟩ := h.exists_zpowers_eq_center
  obtain ⟨n, b, hb⟩ := exists_isSymplecticBasis (h.commForm hz hzo) (commForm_isAlt hz hzo)
    (commForm_separatingLeft hz hzo)
  set L := span (ZMod p) (Set.range (b ∘ Sum.inl)) with hLdef
  have hL : (h.commForm hz hzo).orthogonal L = L := hb.orthogonal_span_range_comp_inl
  have hdimL : finrank (ZMod p) L = n := hb.finrank_span_range_comp_inl
  have hn1 : 1 ≤ n := by
    have hpos : 0 < finrank (ZMod p) h.QuotientCenter := Module.finrank_pos
    have := hb.finrank_eq
    omega
  have hcardL : Nat.card L = p ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := L), Nat.card_zmod, hdimL]
  have hcardQ : Nat.card h.QuotientCenter = p ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := h.QuotientCenter), Nat.card_zmod,
      hb.finrank_eq]
  refine ⟨n, h.preimage L, hn1, isMulCommutative_preimage h hz hzo hL, inferInstance,
    h.center_le_preimage L, ?_, ?_, ?_, centralizer_preimage h hz hzo hL⟩
  ·
    rw [← Subgroup.card_mul_index (Subgroup.center P), h.card_center, h.index_center, hcardQ,
      pow_succ, mul_comm]
  ·
    have hkey := h.index_preimage_mul_natCard L
    rw [hcardL, hcardQ] at hkey
    have hp : (p : ℕ) ^ n ≠ 0 := pow_ne_zero _ h.prime.pos.ne'
    refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp) ?_
    rw [hkey, ← pow_add]
    ring_nf
  · rw [h.relIndex_center_preimage L, hcardL]

end IsExtraspecial

end

end CFSG.FeitThompson
