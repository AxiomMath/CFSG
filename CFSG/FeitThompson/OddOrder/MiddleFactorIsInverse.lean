module

public import CFSG.FeitThompson.OddOrder.ConjugateAffineIntersection
import CFSG.FeitThompson.OddOrder.ShortWordRigidity

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Subgroup

variable {p q : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

theorem conj_inv_mem_map_conj_inv {A : Subgroup G} {g a : G} (ha : a ∈ A) :
    g⁻¹ * a * g ∈ A.map (MulAut.conj g⁻¹ : G →* G) := by
  rw [mem_map_conj_inv, show g * (g⁻¹ * a * g) * g⁻¹ = a from by group]
  exact ha

namespace AppendixCSetup

variable [Finite F] (S : AppendixCSetup p q F G)

theorem exists_mem_bot_of_mem_P₀ {r : G} (hr : r ∈ S.P₀) :
    ∃ c ∈ (⊥ : Subfield F), S.pt (ofAdd c) = r := by
  rw [S.P₀_def, Subgroup.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact ⟨toAdd w, hw, by rw [ofAdd_toAdd]⟩

theorem exists_normOneUnitsHom : ∃ Ue : normOneUnits F →* G, Ue.range = S.U ∧
    ∀ (z : F) (v : normOneUnits F), (Ue v)⁻¹ * S.pt (ofAdd z) * Ue v
      = S.pt (ofAdd (z * ((v : Fˣ) : F))) := by
  set e : normOneUnits F ≃* rootsOfUnity (normExponent p q) F :=
    MulEquiv.subgroupCongr
      (rootsOfUnity_normExponent_eq_normOneUnits S.p_prime S.card_field).symm with he
  have hcoe : ∀ v : normOneUnits F, ((e v : Fˣ) : F) = ((v : Fˣ) : F) := by
    intro v; rw [he]; norm_cast
  refine ⟨S.ut.comp e.toMonoidHom, ?_, ?_⟩
  · ext x
    simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply]
    rw [S.U_def]
    exact ⟨fun ⟨v, hv⟩ => ⟨e v, hv⟩, fun ⟨w, hw⟩ => ⟨e.symm w, by simpa using hw⟩⟩
  · intro z v
    have h := S.conj_pt z (e v)
    rw [hcoe] at h
    exact h

theorem eq_one_of_conj_mem_U {r u : G} (hr : r ∈ S.P₀) (hu : u ∈ S.U)
    (hmem : r⁻¹ * u * r ∈ S.U) : r = 1 ∨ u = 1 := by
  obtain ⟨Ue, hUrange, hact⟩ := S.exists_normOneUnitsHom
  obtain ⟨c, hc, hcr⟩ := S.exists_mem_bot_of_mem_P₀ hr
  have hdisj : Disjoint S.pt.range Ue.range := by
    rw [hUrange, ← S.P_def]; exact disjoint_iff.mpr S.P_inf_U
  obtain ⟨w, rfl⟩ : ∃ w, Ue w = u := by rw [← MonoidHom.mem_range, hUrange]; exact hu
  have hinv : S.pt (ofAdd (-c)) = r⁻¹ := by rw [← hcr, ← map_inv, ← ofAdd_neg]
  have hmem' : S.pt (ofAdd (-c)) * Ue w * S.pt (ofAdd c) ∈ Ue.range := by
    rw [hinv, hcr, hUrange]; exact hmem
  have hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) :=
    normExponent_def p q ▸ S.coprime_normExponent
  rcases eq_one_of_mul_mul_mem_range S.p_prime S.card_field hcop S.pt S.pt_injective Ue hdisj
    hact (neg_mem hc) hc hmem' with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact Or.inl (hcr ▸ h2)
  · exact Or.inr h1

theorem eq_inv_s_of_mul_inv_eq [Finite G] {Q : Subgroup G} (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : S.P₀ ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ Q)
    (hP₁U : S.P₀.map (MulAut.conj y⁻¹ : G →* G) ≤ normalizer (S.U : Set G))
    {r₁ r₃ : G} (hr₁ : r₁ ∈ S.P₀) (hr₃ : r₃ ∈ S.P₀) (hr₁1 : r₁ ≠ 1)
    (heq : r₁ * ((y⁻¹ * S.s * y) * (y⁻¹ * r₁ * y))⁻¹
      = ((y⁻¹ * r₃ * y) * (y⁻¹ * S.s * y))⁻¹ * r₃) :
    r₁ = S.s⁻¹ := by
  by_contra hne
  have hsr₁ : S.s * r₁ ≠ 1 := fun h => hne (by rw [← inv_eq_iff_mul_eq_one] at h; rw [← h])
  set v : G := ((y⁻¹ * S.s * y) * (y⁻¹ * r₁ * y))⁻¹ with hv
  have hveq : v = y⁻¹ * (S.s * r₁)⁻¹ * y := by rw [hv]; group
  have hvP₁ : v ∈ S.P₀.map (MulAut.conj y⁻¹ : G →* G) := by
    rw [hveq]
    exact conj_inv_mem_map_conj_inv (inv_mem (mul_mem S.s_mem_P₀ hr₁))
  have hv1 : v ≠ 1 := by
    intro h
    refine hsr₁ ?_
    have h2 : y⁻¹ * (S.s * r₁)⁻¹ * y = 1 := by rw [← hveq]; exact h
    calc S.s * r₁ = (y * (y⁻¹ * (S.s * r₁)⁻¹ * y) * y⁻¹)⁻¹ := by group
      _ = 1 := by rw [h2]; group
  set w : G := ((y⁻¹ * r₃ * y) * (y⁻¹ * S.s * y))⁻¹ with hw
  have hwP₁ : w ∈ S.P₀.map (MulAut.conj y⁻¹ : G →* G) := by
    rw [show w = y⁻¹ * (r₃ * S.s)⁻¹ * y from by rw [hw]; group]
    exact conj_inv_mem_map_conj_inv (inv_mem (mul_mem hr₃ S.s_mem_P₀))
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 S.U_ne_bot
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  set X : G := v⁻¹ * (r₁⁻¹ * u * r₁) * v with hX
  have hXeq : X = r₃⁻¹ * (w⁻¹ * u * w) * r₃ := by
    calc X = (r₁ * v)⁻¹ * u * (r₁ * v) := by rw [hX]; group
      _ = (w * r₃)⁻¹ * u * (w * r₃) := by rw [heq]
      _ = r₃⁻¹ * (w⁻¹ * u * w) * r₃ := by group
  have hXH : X ∈ S.H := by
    rw [hXeq]
    have h1 : w⁻¹ * u * w ∈ S.U := (Subgroup.mem_set_normalizer_iff''.mp (hP₁U hwP₁) u).mp hu
    exact mul_mem (mul_mem (inv_mem (S.P₀_le_H hr₃)) (S.U_le_H h1)) (S.P₀_le_H hr₃)
  have hXHv : X ∈ S.H.map (MulAut.conj v⁻¹ : G →* G) := by
    rw [mem_map_conj_inv, hX, show v * (v⁻¹ * (r₁⁻¹ * u * r₁) * v) * v⁻¹ = r₁⁻¹ * u * r₁ from
      by group]
    exact mul_mem (mul_mem (inv_mem (S.P₀_le_H hr₁)) (S.U_le_H hu)) (S.P₀_le_H hr₁)
  have hXU : X ∈ S.U := by
    rw [← H_inf_map_conj_inv_eq_U hQp hQnorm hy hP₁U hvP₁ hv1]
    exact Subgroup.mem_inf.2 ⟨hXH, hXHv⟩
  have hconj : r₁⁻¹ * u * r₁ ∈ S.U :=
    (Subgroup.mem_set_normalizer_iff''.mp (hP₁U hvP₁) (r₁⁻¹ * u * r₁)).mpr hXU
  rcases S.eq_one_of_conj_mem_U hr₁ hu hconj with h | h
  · exact hr₁1 h
  · exact hu1' h

theorem eq_inv_s_of_mul_inv_eq_of_appendixC [Finite G] {Q : Subgroup G}
    (_hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hQp : Nat.Coprime (Nat.card Q) p)
    (hQnorm : S.P₀ ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ Q)
    (_hycomm : y ∈ ⁅Q, S.P₀⁆)
    {P₁ : Subgroup G} (hP₁ : P₁ = S.P₀.map (MulAut.conj y⁻¹ : G →* G))
    (hP₁U : P₁ ≤ normalizer (S.U : Set G))
    {t : G} (ht : t = y⁻¹ * S.s * y)
    {r₁ r₃ t₁ t₃ : G} (hr₁ : r₁ ∈ S.P₀) (hr₃ : r₃ ∈ S.P₀) (hr₁1 : r₁ ≠ 1)
    (ht₁ : t₁ = y⁻¹ * r₁ * y) (ht₃ : t₃ = y⁻¹ * r₃ * y)
    (heq : r₁ * (t * t₁)⁻¹ = (t₃ * t)⁻¹ * r₃) :
    r₁ = S.s⁻¹ :=
  eq_inv_s_of_mul_inv_eq S hQp hQnorm hy (hP₁ ▸ hP₁U) hr₁ hr₃ hr₁1
    (by rw [← ht, ← ht₁, ← ht₃]; exact heq)

end AppendixCSetup

end

end CFSG.FeitThompson
