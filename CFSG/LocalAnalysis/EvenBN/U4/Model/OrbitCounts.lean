module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OrbitsTwo

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Counting

theorem ncard_mul_eq_of_ne {ε : h.fixedField} (hε : ε ≠ 0) :
    {p : h.fixedField × h.fixedField | p.1 * p.2 = ε}.ncard = 2 ^ f - 1 := by
  have := h.finite
  have hset : {p : h.fixedField × h.fixedField | p.1 * p.2 = ε} =
      (fun b => (b, ε / b)) '' {b | b ≠ 0} := by
    ext ⟨b, d⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq]
    constructor
    · intro e
      have hb : b ≠ 0 := by
        rintro rfl
        rw [zero_mul] at e
        exact hε e.symm
      exact ⟨b, hb, rfl, by rw [← e]; field_simp⟩
    · rintro ⟨b', hb', rfl, rfl⟩
      field_simp
  rw [hset, Set.ncard_image_of_injective _ (fun x y e => (Prod.mk.inj e).1)]
  have : {b : h.fixedField | b ≠ 0} = Set.univ \ {0} := by
    ext b
    simp
  rw [this, Set.ncard_sdiff (by simp), Set.ncard_univ, Set.ncard_singleton, h.card_fixedField]

theorem ncard_mul_eq_zero :
    {p : h.fixedField × h.fixedField | p.1 * p.2 = 0}.ncard = 2 * 2 ^ f - 1 := by
  have := h.finite
  have hset : {p : h.fixedField × h.fixedField | p.1 * p.2 = 0} =
      {p | p.1 = 0} ∪ {p | p.2 = 0} := by
    ext p
    simp [mul_eq_zero]
  have h1 : ({p : h.fixedField × h.fixedField | p.1 = 0}).ncard = 2 ^ f := by
    rw [show {p : h.fixedField × h.fixedField | p.1 = 0} = (fun d => ((0 : h.fixedField), d)) ''
      Set.univ by ext ⟨b, d⟩; simp [eq_comm],
      Set.ncard_image_of_injective _ (fun x y e => (Prod.mk.inj e).2), Set.ncard_univ,
      h.card_fixedField]
  have h2 : ({p : h.fixedField × h.fixedField | p.2 = 0}).ncard = 2 ^ f := by
    rw [show {p : h.fixedField × h.fixedField | p.2 = 0} = (fun b => (b, (0 : h.fixedField))) ''
      Set.univ by ext ⟨b, d⟩; simp [eq_comm],
      Set.ncard_image_of_injective _ (fun x y e => (Prod.mk.inj e).1), Set.ncard_univ,
      h.card_fixedField]
  have h3 : ({p : h.fixedField × h.fixedField | p.1 = 0} ∩ {p | p.2 = 0}).ncard = 1 := by
    rw [show {p : h.fixedField × h.fixedField | p.1 = 0} ∩ {p | p.2 = 0} = {(0, 0)} by
      ext ⟨b, d⟩; simp, Set.ncard_singleton]
  have := Set.ncard_union_add_ncard_inter {p : h.fixedField × h.fixedField | p.1 = 0}
    {p | p.2 = 0}
  rw [hset]
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega

theorem ncard_norm_eq_of_ne {ε : h.fixedField} (hε : ε ≠ 0) :
    {c : K | h.normHom c = ε}.ncard = 2 ^ f + 1 := by
  have := h.finite
  obtain ⟨c₀, hc₀⟩ := h.normHom_surjective ε
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    apply hε
    rw [← hc₀]
    exact Subtype.ext (by simp [UnitaryFieldData.norm])
  have hset : {c : K | h.normHom c = ε} =
      (fun u : (Units.map h.normHom).ker => c₀ * ((u : Kˣ) : K)) '' Set.univ := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        apply hε
        rw [← hc]
        exact Subtype.ext (by simp [UnitaryFieldData.norm])
      refine ⟨⟨Units.mk0 (c / c₀) (div_ne_zero hc0 hc₀0), ?_⟩, by simp; field_simp⟩
      rw [UnitaryFieldData.mem_ker_normUnits]
      have h1 := congrArg Subtype.val hc
      have h2 := congrArg Subtype.val hc₀
      simp only [UnitaryFieldData.coe_normHom] at h1 h2
      have hε0 : (ε : K) ≠ 0 := fun e => hε (Subtype.ext e)
      simp only [Units.val_mk0, UnitaryFieldData.norm, map_div₀] at h1 h2 ⊢
      rw [div_mul_div_comm, h1, h2, div_self hε0]
    · rintro ⟨u, rfl⟩
      apply Subtype.ext
      have hu := (UnitaryFieldData.mem_ker_normUnits h).1 u.2
      have h2 := congrArg Subtype.val hc₀
      simp only [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at hu h2 ⊢
      rw [map_mul, mul_mul_mul_comm, hu, mul_one, h2]
  rw [hset, Set.ncard_image_of_injective _ (fun u v e => Subtype.ext (Units.ext
    (mul_left_cancel₀ hc₀0 e))), Set.ncard_univ, h.card_ker_normUnits_and_surjective.1]

theorem ncard_norm_eq_zero : {c : K | h.normHom c = 0}.ncard = 1 := by
  rw [show {c : K | h.normHom c = 0} = {0} by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hc
      have := congrArg Subtype.val hc
      simp only [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm, ZeroMemClass.coe_zero,
        mul_eq_zero, map_eq_zero, or_self] at this
      exact this
    · rintro rfl
      exact Subtype.ext (by simp [UnitaryFieldData.norm]), Set.ncard_singleton]

@[expose] def miyamotoQEquiv (δ : h.fixedField) :
    {p : h.fixedField × K × h.fixedField // h.normHom p.2.1 + p.1 * p.2.2 = δ} ≃
      Σ c : K, {r : h.fixedField × h.fixedField // r.1 * r.2 = δ - h.normHom c} where
  toFun p := ⟨p.1.2.1, ⟨(p.1.1, p.1.2.2), by have := p.2; simp only; linear_combination this⟩⟩
  invFun s := ⟨(s.2.1.1, s.1, s.2.1.2), by have := s.2.2; simp only; linear_combination this⟩
  left_inv p := rfl
  right_inv s := rfl

theorem ncard_normHom_add_mul_eq (δ : h.fixedField) :
    {p : h.fixedField × K × h.fixedField | h.normHom p.2.1 + p.1 * p.2.2 = δ}.ncard =
      (2 ^ f) ^ 2 * (2 ^ f - 1) + 2 ^ f * {c : K | h.normHom c = δ}.ncard := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have := Fintype.ofFinite h.fixedField
  rw [← Nat.card_coe_set_eq, Set.coe_ofPred, Nat.card_congr (miyamotoQEquiv h δ), Nat.card_sigma]
  have hfib : ∀ c : K, Nat.card {r : h.fixedField × h.fixedField // r.1 * r.2 = δ - h.normHom c} =
      (2 ^ f - 1) + (if h.normHom c = δ then 2 ^ f else 0) := by
    intro c
    rw [← Set.coe_ofPred, Nat.card_coe_set_eq]
    by_cases hc : h.normHom c = δ
    · rw [hc, sub_self, ncard_mul_eq_zero]
      simp only [↓reduceIte]
      have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    · rw [ncard_mul_eq_of_ne h (sub_ne_zero.2 (Ne.symm hc))]
      simp [hc]
  simp only [hfib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, h.card_eq_sq, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul, mul_comm (Finset.card _)]
  congr 2
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext c
  simp

theorem ncard_normHom_add_mul_eq_zero :
    {p : h.fixedField × K × h.fixedField | h.normHom p.2.1 + p.1 * p.2.2 = 0}.ncard =
      (2 ^ f) ^ 2 * (2 ^ f - 1) + 2 ^ f := by
  rw [ncard_normHom_add_mul_eq, ncard_norm_eq_zero, mul_one]

theorem ncard_normHom_add_mul_eq_of_ne {δ : h.fixedField} (hδ : δ ≠ 0) :
    {p : h.fixedField × K × h.fixedField | h.normHom p.2.1 + p.1 * p.2.2 = δ}.ncard =
      (2 ^ f) ^ 2 * (2 ^ f - 1) + 2 ^ f * (2 ^ f + 1) := by
  rw [ncard_normHom_add_mul_eq, ncard_norm_eq_of_ne h hδ]

end Counting

section OrbitsA1

variable [CharP K 2]

theorem ncard_A1_Q_eq (δ : h.fixedField) :
    {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = δ}.ncard =
      {p : h.fixedField × K × h.fixedField | h.normHom p.2.1 + p.1 * p.2.2 = δ}.ncard := by
  have hset : {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = δ} =
      (fun p : h.fixedField × K × h.fixedField => miyamotoXGL h 0 p.1 p.2.1 p.2.2) ''
        {p | h.normHom p.2.1 + p.1 * p.2.2 = δ} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hx, hQ⟩
      obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hx
      refine ⟨(⟨b, hb⟩, c, ⟨d, hd⟩), Subtype.ext ?_, rfl⟩
      rw [miyamotoQA1_miyamotoXGL] at hQ
      simpa [UnitaryFieldData.norm] using hQ
    · rintro ⟨⟨b, c, d⟩, hp, rfl⟩
      refine ⟨(miyamotoXGL_mem_A1 h).2 ⟨rfl, b.2, d.2⟩, ?_⟩
      rw [miyamotoQA1_miyamotoXGL]
      have := congrArg Subtype.val hp
      simpa [UnitaryFieldData.norm] using this
  rw [hset, Set.ncard_image_of_injective]
  intro p p' e
  obtain ⟨-, e2, e3, e4⟩ := (miyamotoXGL_inj h).1 e
  exact Prod.ext (Subtype.ext e2) (Prod.ext e3 (Subtype.ext e4))

theorem ncard_A1_Q_eq_zero :
    {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0}.ncard = (2 ^ f) ^ 2 * (2 ^ f - 1) + 2 ^ f := by
  have := ncard_A1_Q_eq h 0
  simp only [ZeroMemClass.coe_zero] at this
  rw [this, ncard_normHom_add_mul_eq_zero]

theorem ncard_miyamotoA1 : (miyamotoA1 h : Set (GL (Fin 4) K)).ncard = (2 ^ f) ^ 4 := by
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_miyamotoA1]

theorem ncard_orbit_z1_N1 :
    {y | ∃ n ∈ miyamotoN1 h, n⁻¹ * miyamotoZ1 K * n = y}.ncard =
      (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
  have := h.finite
  rw [miyamoto_orbit_z1_N1 h]
  have hset : {x | x ∈ miyamotoA1 h ∧ x ≠ 1 ∧ miyamotoQA1 h x = 0} =
      {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} \ {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  have h1 : (1 : GL (Fin 4) K) ∈ {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} :=
    ⟨one_mem _, by rw [← miyamotoXGL_zero h, miyamotoQA1_miyamotoXGL]; simp⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem h1, ncard_A1_Q_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

theorem ncard_orbit_z1 :
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * miyamotoZ1 K * g = y}.ncard =
      (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
  rw [miyamoto_orbit_z1_I1N1 h, ← miyamoto_orbit_z1_N1 h, ncard_orbit_z1_N1]

theorem ncard_orbit_z2_N1 :
    {y | ∃ n ∈ miyamotoN1 h, n⁻¹ * LocalAnalysis.miyamotoZ2 K * n = y}.ncard =
      2 ^ f * ((2 ^ f) ^ 2 + 1) := by
  rw [miyamoto_orbit_z2_N1 h]
  have := ncard_A1_Q_eq h 1
  simp only [OneMemClass.coe_one] at this
  rw [this, ncard_normHom_add_mul_eq_of_ne h one_ne_zero]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  ring

theorem ncard_orbit_z2 :
    {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h, g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y}.ncard =
      (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) := by
  have := h.finite
  rw [miyamoto_orbit_z2_I1N1 h]
  have hset : {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x ≠ 0} =
      (miyamotoA1 h : Set (GL (Fin 4) K)) \ {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe]
    tauto
  have hsub : {x | x ∈ miyamotoA1 h ∧ miyamotoQA1 h x = 0} ⊆ (miyamotoA1 h : Set (GL (Fin 4) K)) :=
    fun x hx => hx.1
  rw [hset, Set.ncard_sdiff hsub (Set.toFinite _), ncard_miyamotoA1, ncard_A1_Q_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  have e : (k + 1) ^ 4 = (k + 1) ^ 2 * k + (k + 1) + k * (k + 1) * ((k + 1) ^ 2 + 1) := by ring
  omega

end OrbitsA1

section OrbitsA2

variable [CharP K 2]

@[expose] def miyamotoA2Coord (x : GL (Fin 4) K) : K × K :=
  ((x : Matrix (Fin 4) (Fin 4) K) 1 0, (x : Matrix (Fin 4) (Fin 4) K) 2 0)

@[expose] def miyamotoTraceEquiv :
    {v : K × K // h.bar v.1 * v.2 + v.1 * h.bar v.2 = 0} ≃
      Σ a : K, {c : K // h.bar a * c + a * h.bar c = 0} where
  toFun v := ⟨v.1.1, ⟨v.1.2, v.2⟩⟩
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ncard_trace_zero :
    {v : K × K | h.bar v.1 * v.2 + v.1 * h.bar v.2 = 0}.ncard =
      (2 ^ f) ^ 2 + ((2 ^ f) ^ 2 - 1) * 2 ^ f := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  rw [← Nat.card_coe_set_eq, Set.coe_ofPred, Nat.card_congr (miyamotoTraceEquiv h),
    Nat.card_sigma]
  have hfib : ∀ a : K, Nat.card {c : K // h.bar a * c + a * h.bar c = 0} =
      if a = 0 then (2 ^ f) ^ 2 else 2 ^ f := by
    intro a
    rw [← Set.coe_ofPred, Nat.card_coe_set_eq]
    by_cases ha : a = 0
    · subst ha
      simp only [map_zero, zero_mul, add_zero, Set.ofPred_true, Set.ncard_univ, ↓reduceIte]
      exact h.card_eq_sq
    · rw [ncard_trace_mul_eq_zero h ha]
      simp [ha]
  simp only [hfib]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
    show (Finset.univ.filter fun a : K => a = 0) = {0} by ext; simp, Finset.card_singleton,
    one_mul, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, h.card_eq_sq]

theorem ncard_involution_coords :
    {v : K × K | v ≠ 0 ∧ h.bar v.1 * v.2 + v.1 * h.bar v.2 = 0}.ncard =
      (2 ^ f + 1) * ((2 ^ f) ^ 2 - 1) := by
  have := h.finite
  have hset : {v : K × K | v ≠ 0 ∧ h.bar v.1 * v.2 + v.1 * h.bar v.2 = 0} =
      {v : K × K | h.bar v.1 * v.2 + v.1 * h.bar v.2 = 0} \ {0} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [hset, Set.ncard_sdiff_singleton_of_mem (by simp), ncard_trace_zero]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hk]
  have e1 : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    omega
  rw [e1]
  have e2 : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
  rw [e2]
  ring_nf
  omega

theorem ncard_noninvolution_coords :
    {v : K × K | h.bar v.1 * v.2 + v.1 * h.bar v.2 ≠ 0}.ncard =
      (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have := h.finite
  have := Fintype.ofFinite K
  have hset : {v : K × K | h.bar v.1 * v.2 + v.1 * h.bar v.2 ≠ 0} =
      Set.univ \ {v : K × K | h.bar v.1 * v.2 + v.1 * h.bar v.2 = 0} := by
    ext v
    simp
  rw [hset, Set.ncard_sdiff (Set.subset_univ _) (Set.toFinite _), Set.ncard_univ, Nat.card_prod,
    h.card_eq_sq, ncard_trace_zero]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ f = k + 1 := ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  have e2 : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
  rw [e2, Nat.add_sub_cancel]
  ring_nf
  omega

theorem miyamotoA2Coord_eq_iff {x y : GL (Fin 4) K} (hx : x ∈ miyamotoA2 h)
    (hy : y ∈ miyamotoA2 h) : miyamotoA2Coord x = miyamotoA2Coord y ↔ x⁻¹ * y ∈ miyamotoZ h := by
  obtain ⟨a, c, d, -, rfl⟩ := (mem_A2 h).1 hx
  obtain ⟨a', c', d', -, rfl⟩ := (mem_A2 h).1 hy
  have hxy := mul_mem (inv_mem hx) hy
  rw [miyamotoXGL_inv h (map_zero _), miyamotoXGL_mul h (map_zero _)] at hxy ⊢
  rw [show (0 : K) + 0 = 0 by ring] at hxy ⊢
  rw [miyamotoXGL_mem_Z_iff_of_mem_A2 h hxy]
  simp only [miyamotoA2Coord, coe_miyamotoXGL, miyamotoX_one_zero, miyamotoX_two_zero,
    Prod.mk.injEq, zero_mul, add_zero]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨CharTwo.add_self_eq_zero _, CharTwo.add_self_eq_zero _⟩
  · rintro ⟨e1, e2⟩
    exact ⟨by linear_combination e1 - a' * CharTwo.two_eq_zero (R := K),
      by linear_combination e2 - c' * CharTwo.two_eq_zero (R := K)⟩

theorem miyamoto_two_two_two_orbits {x : GL (Fin 4) K} (hx : x ∈ miyamotoA2 h)
    (hxZ : x ∉ miyamotoZ h) :
    (x * x = 1 → miyamotoA2Coord '' {y | ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, g⁻¹ * x * g = y} =
        {v : K × K | v ≠ 0 ∧ h.bar v.1 * v.2 + v.1 * h.bar v.2 = 0}) ∧
      (x * x ≠ 1 → miyamotoA2Coord '' {y | ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, g⁻¹ * x * g = y} =
        {v : K × K | h.bar v.1 * v.2 + v.1 * h.bar v.2 ≠ 0}) := by
  have hN := miyamotoI2_sup_N2_le_normalizer h
  have hconj : ∀ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, g⁻¹ * x * g ∈ miyamotoA2 h ∧
      g⁻¹ * x * g ∉ miyamotoZ h ∧ (g⁻¹ * x * g * (g⁻¹ * x * g) = 1 ↔ x * x = 1) := by
    intro g hg
    refine ⟨(mem_normalizer_iff''.1 (hN hg).1 x).1 hx, fun hZ => hxZ ?_, ?_⟩
    · exact (mem_normalizer_iff''.1 (hN hg).2 x).2 hZ
    · rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group]
      constructor
      · intro e
        calc x * x = g * (g⁻¹ * (x * x) * g) * g⁻¹ := by group
          _ = 1 := by rw [e]; group
      · intro e
        rw [e]
        group
  have hcoord : ∀ {y : GL (Fin 4) K}, y ∈ miyamotoA2 h → (y ∉ miyamotoZ h ↔
      miyamotoA2Coord y ≠ 0) ∧ (y * y = 1 ↔ h.bar (miyamotoA2Coord y).1 * (miyamotoA2Coord y).2 +
        (miyamotoA2Coord y).1 * h.bar (miyamotoA2Coord y).2 = 0) := by
    intro y hy
    obtain ⟨a, c, d, -, rfl⟩ := (mem_A2 h).1 hy
    simp only [miyamotoA2Coord, coe_miyamotoXGL, miyamotoX_one_zero, miyamotoX_two_zero]
    refine ⟨?_, ?_⟩
    · rw [miyamotoXGL_mem_Z_iff_of_mem_A2 h hy, Ne, Prod.ext_iff]
      simp
    · rw [miyamotoXGL_A2_mul_self, ← miyamotoXGL_zero h, miyamotoXGL_inj]
      simp
  have hlift : ∀ v : K × K, v ≠ 0 → ∃ y ∈ miyamotoA2 h, miyamotoA2Coord y = v := by
    intro v _
    obtain ⟨e, he⟩ := h.traceLin_surjective
      ⟨h.bar v.1 * v.2 + v.1 * h.bar v.2, by
        rw [UnitaryFieldData.mem_fixedField, map_add, map_mul, map_mul, h.bar_bar, h.bar_bar]
        ring⟩
    have he' : e + h.bar e = h.bar v.1 * v.2 + v.1 * h.bar v.2 := congrArg Subtype.val he
    refine ⟨miyamotoXGL h v.1 0 v.2 e, (miyamotoXGL_mem_A2 h).2 ⟨rfl, ?_⟩, rfl⟩
    linear_combination he' + (v.1 * h.bar v.2 + h.bar v.1 * v.2) * CharTwo.two_eq_zero (R := K)
  have orbit : ∀ (S : Set (K × K)), (∀ y ∈ miyamotoA2 h, y ∉ miyamotoZ h →
      ((y * y = 1 ↔ x * x = 1) ↔ miyamotoA2Coord y ∈ S)) → (∀ v ∈ S, v ≠ 0) →
      miyamotoA2Coord '' {y | ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, g⁻¹ * x * g = y} = S := by
    intro S hS hS0
    ext v
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨hA, hZ, hiff⟩ := hconj g hg
      exact (hS _ hA hZ).1 hiff
    · intro hv
      obtain ⟨y, hy, rfl⟩ := hlift v (hS0 v hv)
      have hyZ : y ∉ miyamotoZ h := (hcoord hy).1.2 (hS0 _ hv)
      obtain ⟨g, hg, hz⟩ := exists_I2_sup_N2_conj_mod_Z h hx hy hxZ hyZ
        ((hS y hy hyZ).2 hv).symm
      refine ⟨g⁻¹ * x * g, ⟨g, hg, rfl⟩, ?_⟩
      exact ((miyamotoA2Coord_eq_iff h (hconj g hg).1 hy).2 hz)
  refine ⟨fun hx2 => orbit _ (fun y hy hyZ => ?_) (fun v hv => hv.1),
    fun hx2 => orbit _ (fun y hy hyZ => ?_) (fun v hv e => hv (by rw [e]; simp))⟩
  · simp only [Set.mem_ofPred_eq, hx2, iff_true]
    exact ⟨fun e => ⟨(hcoord hy).1.1 hyZ, (hcoord hy).2.1 e⟩, fun e => (hcoord hy).2.2 e.2⟩
  · simp only [Set.mem_ofPred_eq, hx2, iff_false]
    exact ⟨fun e e' => e ((hcoord hy).2.2 e'), fun e e' => e ((hcoord hy).2.1 e')⟩

theorem ncard_orbit_involution {x : GL (Fin 4) K} (hx : x ∈ miyamotoA2 h)
    (hxZ : x ∉ miyamotoZ h) (hx2 : x * x = 1) :
    (miyamotoA2Coord '' {y | ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, g⁻¹ * x * g = y}).ncard =
      (2 ^ f + 1) * ((2 ^ f) ^ 2 - 1) := by
  rw [(miyamoto_two_two_two_orbits h hx hxZ).1 hx2, ncard_involution_coords]

theorem ncard_orbit_noninvolution {x : GL (Fin 4) K} (hx : x ∈ miyamotoA2 h)
    (hx2 : x * x ≠ 1) :
    (miyamotoA2Coord '' {y | ∃ g ∈ miyamotoI2 h ⊔ miyamotoN2 h, g⁻¹ * x * g = y}).ncard =
      (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hxZ : x ∉ miyamotoZ h := fun hZ => hx2 (by
    obtain ⟨d, hd, rfl⟩ := hZ
    rw [miyamotoXGL_A2_mul_self]
    simp [miyamotoXGL_zero])
  rw [(miyamoto_two_two_two_orbits h hx hxZ).2 hx2, ncard_noninvolution_coords]

end OrbitsA2

end CFSG.LocalAnalysis.EvenBN.U4
