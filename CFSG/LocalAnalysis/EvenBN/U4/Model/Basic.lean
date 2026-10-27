module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Coordinates
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Centre

variable [CharP K 2]

theorem add_bar_ne_zero {ω : K} (hω : h.bar ω ≠ ω) : ω + h.bar ω ≠ 0 :=
  fun e => hω ((add_bar_eq_zero_iff h).1 e)

theorem eq_zero_of_trace_mul {c ω : K} (hω : h.bar ω ≠ ω) (h1 : c + h.bar c = 0)
    (h2 : ω * h.bar c + h.bar ω * c = 0) : c = 0 := by
  have hc : h.bar c = c := (add_bar_eq_zero_iff h).1 h1
  rw [hc] at h2
  have : (ω + h.bar ω) * c = 0 := by linear_combination h2
  exact (mul_eq_zero.1 this).resolve_left (add_bar_ne_zero h hω)

theorem centerIn_miyamotoP : CFSG.centerIn (miyamotoP h) = miyamotoZ h := by
  have hbb := h.bar_bar
  apply le_antisymm
  · rintro g ⟨hgP, hgC⟩
    obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hgP
    have hcomm : ∀ a' b' c' d' : K, h.bar b' = b' →
        d' + h.bar d' + a' * h.bar c' + h.bar a' * c' = 0 →
        ⁅miyamotoXGL h a b c d, miyamotoXGL h a' b' c' d'⁆ = 1 := by
      intro a' b' c' d' hb' hd'
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.1 hgC _ ((miyamotoXGL_mem_P h).2 ⟨hb', hd'⟩)).symm
    have e1 := hcomm 1 0 0 0 (map_zero _) (by simp)
    have e2 := hcomm 0 1 0 0 (map_one _) (by simp)
    rw [miyamotoXGL_commutator h hb (map_zero _), ← miyamotoXGL_zero h, miyamotoXGL_inj] at e1
    rw [miyamotoXGL_commutator h hb (map_one _), ← miyamotoXGL_zero h, miyamotoXGL_inj] at e2
    have hb0 : b = 0 := by simpa using e1.2.2.1
    have ha0 : a = 0 := by simpa using e2.2.2.1
    subst hb0 ha0
    obtain ⟨ω, hω⟩ := h.exists_bar_ne
    have e3 := hcomm 1 0 0 0 (map_zero _) (by simp)
    have e4 := hcomm ω 0 0 0 (map_zero _) (by simp)
    rw [miyamotoXGL_commutator h (map_zero _) (map_zero _), ← miyamotoXGL_zero h,
      miyamotoXGL_inj] at e3 e4
    have e3' := e3.2.2.2
    have e4' := e4.2.2.2
    simp at e3' e4'
    have hc0 : c = 0 := eq_zero_of_trace_mul h hω (by linear_combination e3')
      (by linear_combination e4')
    subst hc0
    exact (miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, rfl, (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩
  · rintro _ ⟨d, hd, rfl⟩
    refine ⟨miyamotoZ_le_P h ⟨d, hd, rfl⟩, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨a', b', c', d', hb', -, rfl⟩ := (mem_P h).1 hy
    rw [← commutatorElement_eq_one_iff_mul_comm, miyamotoXGL_commutator h hb' (map_zero _),
      ← miyamotoXGL_zero h, miyamotoXGL_inj]
    refine ⟨rfl, rfl, by simp, by simp⟩

theorem centerIn_miyamotoA2 : CFSG.centerIn (miyamotoA2 h) = miyamotoZ h := by
  apply le_antisymm
  · rintro g ⟨hgA, hgC⟩
    obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hgA
    have hcomm : ∀ a' c' : K, ⁅miyamotoXGL h a 0 c d, miyamotoXGL h a' 0 c' (h.bar a' * c')⁆ =
        1 := by
      intro a' c'
      rw [commutatorElement_eq_one_iff_mul_comm]
      refine (mem_centralizer_iff.1 hgC _ ((miyamotoXGL_mem_A2 h).2 ⟨rfl, ?_⟩)).symm
      have hbb := h.bar_bar
      grind
    obtain ⟨ω, hω⟩ := h.exists_bar_ne
    have e1 := hcomm 0 1
    have e2 := hcomm 0 ω
    have e3 := hcomm 1 0
    have e4 := hcomm ω 0
    rw [miyamotoXGL_commutator h (map_zero _) (map_zero _), ← miyamotoXGL_zero h,
      miyamotoXGL_inj] at e1 e2 e3 e4
    have e1' := e1.2.2.2
    have e2' := e2.2.2.2
    have e3' := e3.2.2.2
    have e4' := e4.2.2.2
    simp at e1' e2' e3' e4'
    have ha0 : a = 0 := eq_zero_of_trace_mul h hω (by linear_combination e1')
      (by linear_combination e2')
    have hc0 : c = 0 := eq_zero_of_trace_mul h hω (by linear_combination e3')
      (by linear_combination e4')
    subst ha0 hc0
    exact (miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, rfl, (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩
  · intro g hg
    have hP := (centerIn_miyamotoP h).ge hg
    exact ⟨(miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A2 h) hg,
      fun y hy => hP.2 y (miyamotoA2_le_P h hy)⟩

theorem miyamotoXGL_commutator_A2 (a c d a' c' d' : K) :
    ⁅miyamotoXGL h a 0 c d, miyamotoXGL h a' 0 c' d'⁆ =
      miyamotoXGL h 0 0 0 (h.bar a * c' + a * h.bar c' + h.bar a' * c + a' * h.bar c) := by
  rw [miyamotoXGL_commutator h (map_zero _) (map_zero _), miyamotoXGL_inj]
  refine ⟨rfl, rfl, by ring, by ring⟩

theorem commutator_miyamotoA2 : ⁅miyamotoA2 h, miyamotoA2 h⁆ = miyamotoZ h := by
  have hbb := h.bar_bar
  apply le_antisymm
  · rw [commutator_le]
    intro g hg g' hg'
    obtain ⟨a, c, d, -, rfl⟩ := (mem_A2 h).1 hg
    obtain ⟨a', c', d', -, rfl⟩ := (mem_A2 h).1 hg'
    rw [miyamotoXGL_commutator_A2, miyamotoXGL_mem_Z]
    exact ⟨rfl, rfl, rfl, by grind⟩
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨c', hc'⟩ := h.traceLin_surjective ⟨s, hs⟩
    have hc's : c' + h.bar c' = s := congrArg Subtype.val hc'
    have key := commutator_mem_commutator (miyamotoRootA_le_A2 h ⟨1, rfl⟩)
      (miyamotoZ2_le_A2 h ((miyamotoRootC_le_Z2 h) ⟨c', rfl⟩))
    rwa [miyamotoXGL_commutator_A2, show h.bar 1 * c' + 1 * h.bar c' + h.bar 0 * 0 + 0 * h.bar 0
      = s by simp [hc's]] at key

theorem commutator_miyamotoP : ⁅miyamotoP h, miyamotoP h⁆ = miyamotoZ2 h := by
  have hbb := h.bar_bar
  apply le_antisymm
  · rw [commutator_le]
    intro g hg g' hg'
    obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 hg
    obtain ⟨a', b', c', d', hb', -, rfl⟩ := (mem_P h).1 hg'
    rw [miyamotoXGL_commutator h hb hb', miyamotoXGL_mem_Z2]
    refine ⟨rfl, rfl, ?_⟩
    simp only [map_add, map_mul, hbb, hb, hb']
    ring
  · intro g hg
    obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hg
    have h1 : miyamotoXGL h 0 0 c d = ⁅miyamotoXGL h c 0 0 0, miyamotoXGL h 0 1 0 0⁆ *
        miyamotoXGL h 0 0 0 (d + c * h.bar c) := by
      rw [miyamotoXGL_commutator h (map_zero _) (map_one _)]
      refine (miyamotoXGL_mul_eq h (map_zero _) (by ring) (by ring) (by ring) ?_).symm
      grind
    rw [h1]
    refine mul_mem (commutator_mem_commutator ((miyamotoRootA_le_A2 h).trans
      (miyamotoA2_le_P h) ⟨c, rfl⟩) ((miyamotoRootB_le_A1 h).trans (miyamotoA1_le_P h)
      ⟨1, map_one _, rfl⟩)) ?_
    refine (commutator_mono (miyamotoA2_le_P h) (miyamotoA2_le_P h)) ?_
    rw [commutator_miyamotoA2]
    exact ⟨d + c * h.bar c, by grind, rfl⟩

end Centre

section SecondCentre

variable [CharP K 2]

theorem mem_Z2_iff_commutator_mem {g : GL (Fin 4) K} :
    g ∈ miyamotoZ2 h ↔ g ∈ miyamotoP h ∧ ∀ y ∈ miyamotoP h, ⁅g, y⁆ ∈ miyamotoZ h := by
  have hbb := h.bar_bar
  constructor
  · intro hg
    refine ⟨((miyamotoZ2_le_A1 h).trans (miyamotoA1_le_P h)) hg, fun y hy => ?_⟩
    obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hg
    obtain ⟨a', b', c', d', hb', -, rfl⟩ := (mem_P h).1 hy
    rw [miyamotoXGL_commutator h (map_zero _) hb', miyamotoXGL_mem_Z]
    refine ⟨rfl, rfl, by ring, ?_⟩
    simp only [map_add, map_mul, hbb, hb', map_zero]
    ring
  · rintro ⟨hgP, hg⟩
    obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hgP
    have e1 := hg _ ((miyamotoXGL_mem_P h).2 ⟨map_zero h.bar, by simp⟩ : miyamotoXGL h 1 0 0 0 ∈ _)
    have e2 := hg _ ((miyamotoXGL_mem_P h).2 ⟨map_one h.bar, by simp⟩ : miyamotoXGL h 0 1 0 0 ∈ _)
    rw [miyamotoXGL_commutator h hb (map_zero _), miyamotoXGL_mem_Z] at e1
    rw [miyamotoXGL_commutator h hb (map_one _), miyamotoXGL_mem_Z] at e2
    have hb0 : b = 0 := by simpa using e1.2.2.1
    have ha0 : a = 0 := by simpa using e2.2.2.1
    subst hb0 ha0
    exact (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩

theorem isElementaryAbelian_two_of_forall {G : Type*} [Group G] {H : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hsq : ∀ x ∈ H, x * x = 1) :
    CFSG.IsElementaryAbelian 2 H := CFSG.IsElementaryAbelian.two_of_forall_mul_self hcomm hsq

theorem miyamotoXGL_mul_A1 {b c d b' c' d' : K} (hb : h.bar b = b) :
    miyamotoXGL h 0 b c d * miyamotoXGL h 0 b' c' d' = miyamotoXGL h 0 (b + b') (c + c') (d + d') :=
  miyamotoXGL_mul_eq h hb (by ring) rfl (by ring) (by simp)

theorem isElementaryAbelian_miyamotoA1 : CFSG.IsElementaryAbelian 2 (miyamotoA1 h) := by
  refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨b, c, d, hb, -, rfl⟩ := (mem_A1 h).1 hx
    obtain ⟨b', c', d', hb', -, rfl⟩ := (mem_A1 h).1 hy
    rw [miyamotoXGL_mul_A1 h hb, miyamotoXGL_mul_A1 h hb', add_comm b, add_comm c, add_comm d]
  · obtain ⟨b, c, d, hb, -, rfl⟩ := (mem_A1 h).1 hx
    rw [miyamotoXGL_mul_A1 h hb, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, miyamotoXGL_zero]

theorem isElementaryAbelian_miyamotoZ : CFSG.IsElementaryAbelian 2 (miyamotoZ h) := by
  have hA := isElementaryAbelian_miyamotoA1 h
  have hZA : miyamotoZ h ≤ miyamotoA1 h := (miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A1 h)
  refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · exact congrArg Subtype.val (mul_comm' (⟨x, hZA hx⟩ : miyamotoA1 h) ⟨y, hZA hy⟩)
  · have := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := miyamotoA1 h) (p := 2) x (hZA hx)
    rwa [sq] at this

end SecondCentre

section Orders

theorem card_eq_of_param {G X : Type*} [Group G] {H : Subgroup G} (φ : X → G)
    (hφ : Function.Injective φ) (hH : ∀ g, g ∈ H ↔ ∃ x, φ x = g) : Nat.card H = Nat.card X := by
  have hrange : Set.range φ = (H : Set G) := by
    ext g
    rw [SetLike.mem_coe, hH, Set.mem_range]
  rw [← SetLike.coe_sort_coe, ← hrange, Nat.card_range_of_injective hφ]

variable [CharP K 2]

theorem card_miyamotoP : Nat.card (miyamotoP h) = (2 ^ f) ^ 6 := by
  have hbb := h.bar_bar
  have key := card_eq_of_param (H := miyamotoP h)
    (fun v : K × h.fixedField × K × h.fixedField =>
      miyamotoXGL h v.1 v.2.1 v.2.2.1 (v.2.2.2 + h.bar v.1 * v.2.2.1)) ?_ ?_
  · rw [key, Nat.card_prod, Nat.card_prod, Nat.card_prod, h.card_eq_sq, h.card_fixedField]
    ring
  · intro v v' hv
    obtain ⟨h1, h2, h3, h4⟩ := (miyamotoXGL_inj h).1 hv
    rw [h1, h3, add_left_inj] at h4
    exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Prod.ext h3 (Subtype.ext h4)))
  · intro g
    constructor
    · intro hg
      obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
      refine ⟨(a, ⟨b, hb⟩, c, ⟨d + h.bar a * c, ?_⟩), ?_⟩
      · change h.bar (d + h.bar a * c) = d + h.bar a * c
        grind
      · simp only
        congr 1
        grind
    · rintro ⟨⟨a, b, c, e⟩, rfl⟩
      have hb : h.bar (b : K) = b := b.2
      have he : h.bar (e : K) = e := e.2
      refine (miyamotoXGL_mem_P h).2 ⟨hb, ?_⟩
      simp only [map_add, map_mul, hbb, he]
      grind

theorem card_miyamotoA1 : Nat.card (miyamotoA1 h) = (2 ^ f) ^ 4 := by
  have key := card_eq_of_param (H := miyamotoA1 h)
    (fun v : h.fixedField × K × h.fixedField => miyamotoXGL h 0 v.1 v.2.1 v.2.2) ?_ ?_
  · rw [key, Nat.card_prod, Nat.card_prod, h.card_eq_sq, h.card_fixedField]
    ring
  · intro v v' hv
    obtain ⟨-, h2, h3, h4⟩ := (miyamotoXGL_inj h).1 hv
    exact Prod.ext (Subtype.ext h2) (Prod.ext h3 (Subtype.ext h4))
  · intro g
    constructor
    · intro hg
      obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hg
      exact ⟨(⟨b, hb⟩, c, ⟨d, hd⟩), rfl⟩
    · rintro ⟨⟨b, c, d⟩, rfl⟩
      exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, b.2, d.2⟩

theorem card_miyamotoA2 : Nat.card (miyamotoA2 h) = (2 ^ f) ^ 5 := by
  have hbb := h.bar_bar
  have key := card_eq_of_param (H := miyamotoA2 h)
    (fun v : K × K × h.fixedField => miyamotoXGL h v.1 0 v.2.1 (v.2.2 + h.bar v.1 * v.2.1)) ?_ ?_
  · rw [key, Nat.card_prod, Nat.card_prod, h.card_eq_sq, h.card_fixedField]
    ring
  · intro v v' hv
    obtain ⟨h1, -, h3, h4⟩ := (miyamotoXGL_inj h).1 hv
    rw [h1, h3, add_left_inj] at h4
    exact Prod.ext h1 (Prod.ext h3 (Subtype.ext h4))
  · intro g
    constructor
    · intro hg
      obtain ⟨a, c, d, hd, rfl⟩ := (mem_A2 h).1 hg
      refine ⟨(a, c, ⟨d + h.bar a * c, ?_⟩), ?_⟩
      · change h.bar (d + h.bar a * c) = d + h.bar a * c
        grind
      · simp only
        congr 1
        grind
    · rintro ⟨⟨a, c, e⟩, rfl⟩
      have he : h.bar (e : K) = e := e.2
      refine (miyamotoXGL_mem_A2 h).2 ⟨rfl, ?_⟩
      simp only [map_add, map_mul, hbb, he]
      grind

theorem card_miyamotoZ2 : Nat.card (miyamotoZ2 h) = (2 ^ f) ^ 3 := by
  have key := card_eq_of_param (H := miyamotoZ2 h)
    (fun v : K × h.fixedField => miyamotoXGL h 0 0 v.1 v.2) ?_ ?_
  · rw [key, Nat.card_prod, h.card_eq_sq, h.card_fixedField]
    ring
  · intro v v' hv
    obtain ⟨-, -, h3, h4⟩ := (miyamotoXGL_inj h).1 hv
    exact Prod.ext h3 (Subtype.ext h4)
  · intro g
    constructor
    · intro hg
      obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hg
      exact ⟨(c, ⟨d, hd⟩), rfl⟩
    · rintro ⟨⟨c, d⟩, rfl⟩
      exact (miyamotoXGL_mem_Z2 h).2 ⟨rfl, rfl, d.2⟩

omit [CharP K 2] in
theorem ncard_fixed : {d : K | h.bar d = d}.ncard = 2 ^ f := by
  rw [← h.card_fixedField, ← Nat.card_coe_set_eq]
  rfl

omit [CharP K 2] in
theorem card_miyamotoZ : Nat.card (miyamotoZ h) = 2 ^ f := by
  have key := card_eq_of_param (H := miyamotoZ h)
    (fun v : h.fixedField => miyamotoXGL h 0 0 0 v) ?_ ?_
  · rw [key, h.card_fixedField]
  · intro d d' hv
    exact Subtype.ext ((miyamotoXGL_inj h).1 hv).2.2.2
  · intro g
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.2, rfl⟩

omit [CharP K 2] in
theorem card_miyamotoRootA : Nat.card (miyamotoRootA h) = (2 ^ f) ^ 2 := by
  have key := card_eq_of_param (H := miyamotoRootA h) (fun a : K => miyamotoXGL h a 0 0 0)
    (fun a a' hv => ((miyamotoXGL_inj h).1 hv).1) fun g => ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩,
      fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  rw [key, h.card_eq_sq]

omit [CharP K 2] in
theorem card_miyamotoRootB : Nat.card (miyamotoRootB h) = 2 ^ f := by
  have key := card_eq_of_param (H := miyamotoRootB h)
    (fun b : h.fixedField => miyamotoXGL h 0 b 0 0)
    (fun b b' hv => Subtype.ext ((miyamotoXGL_inj h).1 hv).2.1) fun g =>
      ⟨fun ⟨b, hb, hg⟩ => ⟨⟨b, hb⟩, hg.symm⟩, fun ⟨b, hg⟩ => ⟨b, b.2, hg.symm⟩⟩
  rw [key, h.card_fixedField]

omit [CharP K 2] in
theorem card_miyamotoRootC : Nat.card (miyamotoRootC h) = (2 ^ f) ^ 2 := by
  have key := card_eq_of_param (H := miyamotoRootC h) (fun c : K => miyamotoXGL h 0 0 c 0)
    (fun c c' hv => ((miyamotoXGL_inj h).1 hv).2.2.1) fun g => ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩,
      fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  rw [key, h.card_eq_sq]

end Orders

section Sylow

theorem miyamotoJ4_conjTranspose : ((miyamotoJ4 K).map h.bar)ᵀ = miyamotoJ4 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoJ4]

omit h in
theorem miyamotoJ4_mul_self : miyamotoJ4 K * miyamotoJ4 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]

omit h in
theorem det_miyamotoJ4_ne_zero : (miyamotoJ4 K).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (miyamotoJ4_mul_self (K := K))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem card_gramSU_miyamotoJ4 :
    (Nat.card (gramSU h (miyamotoJ4 K)) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 6 *
        ((((2 ^ f : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ f : ℕ) : ℤ) ^ 3 + 1) * (((2 ^ f : ℕ) : ℤ) ^ 4 - 1)) ∧
      2 ^ (Nat.card (gramSU h (miyamotoJ4 K))).factorization 2 = (2 ^ f) ^ 6 := by
  have hdim : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  have := CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (miyamotoJ4_conjTranspose h))
    (gramForm_separatingLeft h det_miyamotoJ4_ne_zero) hdim (by norm_num)
  rw [card_gramSU]
  refine ⟨?_, this.2.2.2.2.2.2⟩
  rw [this.2.1, show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem finite_gramSU_miyamotoJ4 : Finite (gramSU h (miyamotoJ4 K)) := by
  have := h.finite
  infer_instance

theorem exists_sylow_miyamotoP [CharP K 2] : ∃ S : Sylow 2 (gramSU h (miyamotoJ4 K)),
    (S : Subgroup (gramSU h (miyamotoJ4 K))) =
      (miyamotoP h).subgroupOf (gramSU h (miyamotoJ4 K)) := by
  have := finite_gramSU_miyamotoJ4 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ((miyamotoP h).subgroupOf (gramSU h (miyamotoJ4 K))) =
      2 ^ (Nat.card (gramSU h (miyamotoJ4 K))).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (miyamotoUnipotent_le_SU h false false)).toEquiv,
      card_miyamotoP, (card_gramSU_miyamotoJ4 h).2]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

end Sylow

section Pull

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem mem_miyamotoPull {M : Subgroup (GL (Fin 4) K)} {x : G} :
    x ∈ miyamotoPull h L η M ↔ ∃ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ M ∧
      ((η.symm g : L) : G) = x := by
  simp only [miyamotoPull, mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨η.symm g, ⟨g, hg, rfl⟩, rfl⟩

theorem symm_mem_miyamotoPull_iff {M : Subgroup (GL (Fin 4) K)} {g : gramSU h (miyamotoJ4 K)} :
    ((η.symm g : L) : G) ∈ miyamotoPull h L η M ↔ (g : GL (Fin 4) K) ∈ M := by
  rw [mem_miyamotoPull]
  constructor
  · rintro ⟨g', hg', e⟩
    rwa [η.symm.injective (Subtype.ext e)] at hg'
  · exact fun hg => ⟨g, hg, rfl⟩

theorem miyamotoPull_le (M : Subgroup (GL (Fin 4) K)) : miyamotoPull h L η M ≤ L := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := (mem_miyamotoPull h L η).1 hx
  exact (η.symm g).2

theorem miyamotoPull_mono {M N : Subgroup (GL (Fin 4) K)} (hMN : M ≤ N) :
    miyamotoPull h L η M ≤ miyamotoPull h L η N := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
  exact (symm_mem_miyamotoPull_iff h L η).2 (hMN hg)

theorem miyamotoPull_inf (M N : Subgroup (GL (Fin 4) K)) :
    miyamotoPull h L η (M ⊓ N) = miyamotoPull h L η M ⊓ miyamotoPull h L η N := by
  refine le_antisymm (le_inf (miyamotoPull_mono h L η inf_le_left)
    (miyamotoPull_mono h L η inf_le_right)) fun x ⟨hM, hN⟩ => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hM
  exact (symm_mem_miyamotoPull_iff h L η).2 ⟨hg, (symm_mem_miyamotoPull_iff h L η).1 hN⟩

theorem card_miyamotoPull {M : Subgroup (GL (Fin 4) K)} (hM : M ≤ gramSU h (miyamotoJ4 K)) :
    Nat.card (miyamotoPull h L η M) = Nat.card M := by
  rw [miyamotoPull, card_map_of_injective L.subtype_injective,
    card_map_of_injective η.symm.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hM).toEquiv

theorem miyamotoPull_commutator {M N : Subgroup (GL (Fin 4) K)}
    (hM : M ≤ gramSU h (miyamotoJ4 K)) (hN : N ≤ gramSU h (miyamotoJ4 K)) :
    miyamotoPull h L η ⁅M, N⁆ = ⁅miyamotoPull h L η M, miyamotoPull h L η N⁆ := by
  have hsub : ∀ {H : Subgroup (GL (Fin 4) K)}, H ≤ gramSU h (miyamotoJ4 K) →
      (H.subgroupOf (gramSU h (miyamotoJ4 K))).map (gramSU h (miyamotoJ4 K)).subtype = H :=
    fun hH => by rw [subgroupOf_map_subtype, inf_eq_left.2 hH]
  have key : ⁅M, N⁆.subgroupOf (gramSU h (miyamotoJ4 K)) =
      ⁅M.subgroupOf (gramSU h (miyamotoJ4 K)), N.subgroupOf (gramSU h (miyamotoJ4 K))⁆ := by
    rw [← comap_map_eq_self_of_injective (gramSU h (miyamotoJ4 K)).subtype_injective
      ⁅M.subgroupOf (gramSU h (miyamotoJ4 K)), N.subgroupOf (gramSU h (miyamotoJ4 K))⁆,
      map_commutator, hsub hM, hsub hN]
    rfl
  rw [miyamotoPull, miyamotoPull, miyamotoPull, key, map_commutator, map_commutator]

theorem miyamotoPull_inf_centralizer (M : Subgroup (GL (Fin 4) K)) {N : Subgroup (GL (Fin 4) K)}
    (hN : N ≤ gramSU h (miyamotoJ4 K)) :
    miyamotoPull h L η (M ⊓ centralizer (N : Set (GL (Fin 4) K))) =
      miyamotoPull h L η M ⊓ centralizer (miyamotoPull h L η N : Set G) := by
  ext x
  rw [mem_inf, mem_miyamotoPull, mem_miyamotoPull]
  constructor
  · rintro ⟨g, ⟨hgM, hgC⟩, rfl⟩
    refine ⟨⟨g, hgM, rfl⟩, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hy
    have e : k * g = g * k := Subtype.ext (mem_centralizer_iff.1 hgC _ hk)
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e]
  · rintro ⟨⟨g, hgM, rfl⟩, hC⟩
    refine ⟨g, ⟨hgM, mem_centralizer_iff.2 fun k hk => ?_⟩, rfl⟩
    have := mem_centralizer_iff.1 hC _
      ((symm_mem_miyamotoPull_iff h L η (g := ⟨k, hN hk⟩)).2 hk)
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (η.symm.injective (Subtype.ext this))

theorem centerIn_miyamotoPull {M : Subgroup (GL (Fin 4) K)} (hM : M ≤ gramSU h (miyamotoJ4 K)) :
    CFSG.centerIn (miyamotoPull h L η M) = miyamotoPull h L η (CFSG.centerIn M) :=
  (miyamotoPull_inf_centralizer h L η M hM).symm

theorem isElementaryAbelian_miyamotoPull {M : Subgroup (GL (Fin 4) K)}
    [CFSG.IsElementaryAbelian 2 M] : CFSG.IsElementaryAbelian 2 (miyamotoPull h L η M) := by
  refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
    obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hy
    have e : g * k = k * g := Subtype.ext (by
      simpa using congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : M) ⟨k, hk⟩))
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e]
  · obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
    have h2 : (g : GL (Fin 4) K) ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian _ hg
    have e : g * g = 1 := Subtype.ext (by rw [coe_mul, ← sq, h2, coe_one])
    rw [← L.coe_mul, ← map_mul, e, map_one, L.coe_one]

theorem card_miyamotoPG : Nat.card (miyamotoPG h L η) = (2 ^ f) ^ 6 := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η (miyamotoUnipotent_le_SU h false false), card_miyamotoP]

theorem card_miyamotoA1G : Nat.card (miyamotoA1G h L η) = (2 ^ f) ^ 4 := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η (miyamotoUnipotent_le_SU h true false), card_miyamotoA1]

theorem card_miyamotoA2G : Nat.card (miyamotoA2G h L η) = (2 ^ f) ^ 5 := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η (miyamotoUnipotent_le_SU h false true), card_miyamotoA2]

theorem card_miyamotoZG : Nat.card (miyamotoPull h L η (miyamotoZ h)) = 2 ^ f := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η ((miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)),
    card_miyamotoZ]

theorem isElementaryAbelian_miyamotoA1G : CFSG.IsElementaryAbelian 2 (miyamotoA1G h L η) := by
  have : CharP K 2 := h.charP
  have := isElementaryAbelian_miyamotoA1 h
  exact isElementaryAbelian_miyamotoPull h L η

theorem miyamotoA1G_inf_miyamotoA2G :
    miyamotoA1G h L η ⊓ miyamotoA2G h L η = miyamotoPull h L η (miyamotoZ2 h) := by
  have : CharP K 2 := h.charP
  rw [← miyamotoPull_inf, miyamotoA1_inf_miyamotoA2]

theorem centerIn_miyamotoPG :
    CFSG.centerIn (miyamotoPG h L η) = miyamotoPull h L η (miyamotoZ h) := by
  have : CharP K 2 := h.charP
  rw [centerIn_miyamotoPull h L η (miyamotoUnipotent_le_SU h false false), centerIn_miyamotoP]

theorem commutator_miyamotoA2G :
    ⁅miyamotoA2G h L η, miyamotoA2G h L η⁆ = miyamotoPull h L η (miyamotoZ h) := by
  have : CharP K 2 := h.charP
  rw [← miyamotoPull_commutator h L η (miyamotoUnipotent_le_SU h false true)
    (miyamotoUnipotent_le_SU h false true), commutator_miyamotoA2]

theorem exists_sylow_miyamotoPG :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (miyamotoPG h L η).subgroupOf L := by
  have : CharP K 2 := h.charP
  have := finite_gramSU_miyamotoJ4 h
  have : Finite L := Finite.of_equiv _ η.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ((miyamotoPG h L η).subgroupOf L) = 2 ^ (Nat.card L).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (miyamotoPull_le h L η _)).toEquiv, card_miyamotoPG,
      Nat.card_congr η.toEquiv, (card_gramSU_miyamotoJ4 h).2]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

end Pull

section PullBack

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem miyamotoPull_le_miyamotoPull_iff {M N : Subgroup (GL (Fin 4) K)}
    (hM : M ≤ gramSU h (miyamotoJ4 K)) :
    miyamotoPull h L η M ≤ miyamotoPull h L η N ↔ M ≤ N := by
  refine ⟨fun hle g hg => ?_, miyamotoPull_mono h L η⟩
  have := hle ((symm_mem_miyamotoPull_iff h L η (g := ⟨g, hM hg⟩)).2 hg)
  exact (symm_mem_miyamotoPull_iff h L η).1 this

theorem exists_eq_miyamotoPull {B : Subgroup G} (hB : B ≤ L) :
    ∃ M : Subgroup (GL (Fin 4) K), M ≤ gramSU h (miyamotoJ4 K) ∧ miyamotoPull h L η M = B := by
  refine ⟨((B.subgroupOf L).map η.toMonoidHom).map (gramSU h (miyamotoJ4 K)).subtype,
    fun _ ⟨g, _, e⟩ => e ▸ g.2, ?_⟩
  ext x
  rw [mem_miyamotoPull]
  constructor
  · rintro ⟨g, ⟨g', ⟨y, hy, rfl⟩, e⟩, rfl⟩
    have : g = η y := Subtype.ext e.symm
    rw [this, MulEquiv.symm_apply_apply]
    exact hy
  · intro hx
    refine ⟨η ⟨x, hB hx⟩, ⟨η ⟨x, hB hx⟩, ⟨⟨x, hB hx⟩, hx, rfl⟩, rfl⟩, ?_⟩
    rw [MulEquiv.symm_apply_apply]

theorem commute_miyamotoPull_iff {M : Subgroup (GL (Fin 4) K)}
    (hM : M ≤ gramSU h (miyamotoJ4 K)) :
    (∀ x ∈ miyamotoPull h L η M, ∀ y ∈ miyamotoPull h L η M, x * y = y * x) ↔
      ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  constructor
  · intro hc x hx y hy
    have e := hc _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨x, hM hx⟩)).2 hx)
      _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨y, hM hy⟩)).2 hy)
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul] at e
    exact congrArg Subtype.val (η.symm.injective (Subtype.ext e))
  · intro hc x hx y hy
    obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
    obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hy
    have e : g * k = k * g := Subtype.ext (hc _ hg _ hk)
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e]

end PullBack

end CFSG.LocalAnalysis.EvenBN.U4
