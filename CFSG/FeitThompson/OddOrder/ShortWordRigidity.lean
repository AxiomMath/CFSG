module

public import CFSG.FeitThompson.OddOrder.PrimeFieldScalarNormOneUnits

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Subgroup

variable {G : Type*} [Group G] {p q : ℕ} {F : Type*} [Field F]

def primeLine (Pe : Multiplicative F →* G) : Subgroup G :=
  (AddSubgroup.toSubgroup (⊥ : Subfield F).toAddSubgroup).map Pe

theorem mem_primeLine {Pe : Multiplicative F →* G} {g : G} :
    g ∈ primeLine Pe ↔ ∃ c ∈ (⊥ : Subfield F), Pe (ofAdd c) = g := by
  simp only [primeLine, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨toAdd w, hw, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨ofAdd c, hc, rfl⟩

theorem apply_ofAdd_mem_primeLine (Pe : Multiplicative F →* G) {c : F}
    (hc : c ∈ (⊥ : Subfield F)) : Pe (ofAdd c) ∈ primeLine Pe :=
  mem_primeLine.2 ⟨c, hc, rfl⟩

theorem primeLine_le_range (Pe : Multiplicative F →* G) : primeLine Pe ≤ Pe.range := by
  rintro g hg
  obtain ⟨c, -, rfl⟩ := mem_primeLine.1 hg
  exact ⟨ofAdd c, rfl⟩

theorem conj_apply_ofAdd_of_act (Pe : Multiplicative F →* G) {g : G} {u : Fˣ}
    (hact : ∀ z : F, g⁻¹ * Pe (ofAdd z) * g = Pe (ofAdd (z * (u : F)))) (z : F) :
    g * Pe (ofAdd z) * g⁻¹ = Pe (ofAdd (z * (u : F)⁻¹)) := by
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hz : z * (u : F)⁻¹ * (u : F) = z := by field_simp
  have h := hact (z * (u : F)⁻¹)
  rw [hz] at h
  rw [← h]; group

theorem apply_ofAdd_mul_mul_apply_ofAdd (Pe : Multiplicative F →* G) {g : G} {u : Fˣ}
    (hact : ∀ z : F, g⁻¹ * Pe (ofAdd z) * g = Pe (ofAdd (z * (u : F)))) (c₁ c₂ : F) :
    Pe (ofAdd c₁) * g * Pe (ofAdd c₂) = Pe (ofAdd (c₁ + c₂ * (u : F)⁻¹)) * g := by
  have h := conj_apply_ofAdd_of_act Pe hact c₂
  calc Pe (ofAdd c₁) * g * Pe (ofAdd c₂)
      = Pe (ofAdd c₁) * (g * Pe (ofAdd c₂) * g⁻¹) * g := by group
    _ = Pe (ofAdd c₁) * Pe (ofAdd (c₂ * (u : F)⁻¹)) * g := by rw [h]
    _ = Pe (ofAdd (c₁ + c₂ * (u : F)⁻¹)) * g := by rw [← map_mul, ← ofAdd_add]

theorem eq_zero_or_eq_one_of_add_mul_inv_eq_zero (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {c₁ c₂ : F} (hc₁ : c₁ ∈ (⊥ : Subfield F)) (hc₂ : c₂ ∈ (⊥ : Subfield F))
    {u : Fˣ} (hu : u ∈ normOneUnits F) (hzero : c₁ + c₂ * (u : F)⁻¹ = 0) :
    (c₁ = 0 ∧ c₂ = 0) ∨ (u = 1 ∧ c₁ + c₂ = 0) := by
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  by_cases hc : c₁ = 0
  · subst hc
    rw [zero_add] at hzero
    exact Or.inl ⟨rfl, (mul_eq_zero.1 hzero).resolve_right (inv_ne_zero hu0)⟩
  · have h2 : c₁ * (u : F) + c₂ = 0 := by
      have e : (c₁ + c₂ * (u : F)⁻¹) * (u : F) = c₁ * (u : F) + c₂ := by field_simp
      rw [← e, hzero, zero_mul]
    have hu1 : (u : F) = -c₂ / c₁ := by rw [eq_div_iff hc]; linear_combination h2
    have hbot : u ∈ botSubfieldUnits F :=
      mem_botSubfieldUnits.2 (by rw [hu1]; exact div_mem (neg_mem hc₂) hc₁)
    have hone : u = 1 :=
      Subgroup.disjoint_def.mp (disjoint_botSubfieldUnits_normOneUnits hp hcard hcop) hbot hu
    refine Or.inr ⟨hone, ?_⟩
    rw [hone] at hzero
    simpa using hzero

theorem eq_one_of_mul_mul_mem_range (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe)
    (Ue : normOneUnits F →* G) (hdisj : Disjoint Pe.range Ue.range)
    (hact : ∀ (z : F) (v : normOneUnits F),
      (Ue v)⁻¹ * Pe (ofAdd z) * Ue v = Pe (ofAdd (z * ((v : Fˣ) : F))))
    {c₁ c₂ : F} (hc₁ : c₁ ∈ (⊥ : Subfield F)) (hc₂ : c₂ ∈ (⊥ : Subfield F))
    {u : normOneUnits F} (hmem : Pe (ofAdd c₁) * Ue u * Pe (ofAdd c₂) ∈ Ue.range) :
    (Pe (ofAdd c₁) = 1 ∧ Pe (ofAdd c₂) = 1) ∨
      (Ue u = 1 ∧ Pe (ofAdd c₁) * Pe (ofAdd c₂) = 1) := by
  set w : F := c₁ + c₂ * ((u : Fˣ) : F)⁻¹ with hw
  have hsplit : Pe (ofAdd c₁) * Ue u * Pe (ofAdd c₂) = Pe (ofAdd w) * Ue u :=
    apply_ofAdd_mul_mul_apply_ofAdd Pe (fun z => hact z u) c₁ c₂
  have hPw : Pe (ofAdd w) ∈ Ue.range := by
    have he : Pe (ofAdd w) = Pe (ofAdd c₁) * Ue u * Pe (ofAdd c₂) * (Ue u)⁻¹ := by
      rw [hsplit]; group
    rw [he]; exact mul_mem hmem (inv_mem ⟨u, rfl⟩)
  have hone : Pe (ofAdd w) = 1 := Subgroup.disjoint_def.mp hdisj ⟨ofAdd w, rfl⟩ hPw
  have hzero : w = 0 := by
    have h0 : Pe (ofAdd w) = Pe (ofAdd (0 : F)) := by rw [hone, ofAdd_zero, map_one]
    simpa using hPe h0
  rcases eq_zero_or_eq_one_of_add_mul_inv_eq_zero hp hcard hcop hc₁ hc₂ u.2 hzero with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  · exact Or.inr ⟨by rw [show u = 1 from Subtype.ext h1, map_one],
      by rw [← map_mul, ← ofAdd_add, h2]; simp⟩

theorem eq_one_of_mul_mul_mem (hp : p.Prime) (_hq : q.Prime) (_hqp : q < p)
    (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) {P U : Subgroup G}
    (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U) (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (v : normOneUnits F),
      (Ue v : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue v : G) = (Pe (ofAdd (z * ((v : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (_hH : H = P ⊔ U)
    (_hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (_hs : s = (Pe (ofAdd (1 : F)) : G))
    (_hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (_hQp : Nat.Coprime (Nat.card Q) p)
    (_hQnorm : P₀ ≤ normalizer (Q : Set G)) (_hy : y ∈ Q)
    (_hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹).toMonoidHom) (_hP₁U : P₁ ≤ normalizer (U : Set G))
    (_ht : t = y⁻¹ * s * y)
    {r₁ r₂ : G} (hr₁ : r₁ ∈ primeLine (P.subtype.comp Pe.toMonoidHom))
    (hr₂ : r₂ ∈ primeLine (P.subtype.comp Pe.toMonoidHom)) {u : G} (hu : u ∈ U)
    (hmem : r₁ * u * r₂ ∈ U) :
    (r₁ = 1 ∧ r₂ = 1) ∨ (u = 1 ∧ r₁ * r₂ = 1) := by
  set Pe' : Multiplicative F →* G := P.subtype.comp Pe.toMonoidHom with hPe'
  set Ue' : normOneUnits F →* G := U.subtype.comp Ue.toMonoidHom with hUe'
  have hPrange : Pe'.range = P := by
    ext x
    simp only [hPe', MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ (Pe a).2, fun hx => ⟨Pe.symm ⟨x, hx⟩, by simp⟩⟩
  have hUrange : Ue'.range = U := by
    ext x
    simp only [hUe', MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, coe_subtype]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ (Ue a).2, fun hx => ⟨Ue.symm ⟨x, hx⟩, by simp⟩⟩
  have hPeinj : Function.Injective Pe' := P.subtype_injective.comp Pe.injective
  obtain ⟨c₁, hc₁, rfl⟩ := mem_primeLine.1 hr₁
  obtain ⟨c₂, hc₂, rfl⟩ := mem_primeLine.1 hr₂
  have hu' : u ∈ Ue'.range := by rw [hUrange]; exact hu
  obtain ⟨v, rfl⟩ := hu'
  refine eq_one_of_mul_mul_mem_range hp hcard hcop Pe' hPeinj Ue' ?_ hact hc₁ hc₂ ?_
  · rw [hPrange, hUrange, disjoint_iff]; exact hPU
  · rw [hUrange]; exact hmem

end

end CFSG.FeitThompson
