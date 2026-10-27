module

public import CFSG.ClassicalGroups.A6Klein.Abstract
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalGroups.A6Klein

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.A6Facts.Core
open CFSG.CGT.Timmesfeld75 CFSG.GroupTheory CFSG.Open

theorem exists_two_gens {V : Subgroup K0} (h : 2 < Nat.card V) :
    ∃ a b : K0, a ∈ V ∧ b ∈ V ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have h1 : 2 < (V : Set K0).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h1
  by_cases hx1 : x = 1
  · exact ⟨y, z, hy, hz, fun h => hxy (hx1.trans h.symm), fun h => hxz (hx1.trans h.symm), hyz⟩
  · by_cases hy1 : y = 1
    · exact ⟨x, z, hx, hz, hx1, fun h => hyz (hy1.trans h.symm), hxz⟩
    · exact ⟨x, y, hx, hy, hx1, hy1, hxy⟩

theorem kleinC_of {a b : K0} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (haa : a * a = 1)
    (hbb : b * b = 1) (hcomm : a * b = b * a) : kleinC (kap a) (kap b) = true := by
  simp only [kleinC, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h
    apply ha1
    apply kap_injective
    rw [kap_one]
    exact h
  · intro h
    apply hb1
    apply kap_injective
    rw [kap_one]
    exact h
  · intro h
    exact hab (kap_injective h)
  · rw [← kap_mul, haa, kap_one]
  · rw [← kap_mul, hbb, kap_one]
  · rw [← kap_mul, ← kap_mul, hcomm]

theorem exists_inv_data_psl29 (V : Subgroup K0) (hV : IsElemAbelian 2 V) (h4 : 2 < Nat.card V) :
    ∃ (x : K0) (Λ : Subgroup K0), ¬ IsPGroup 2 ↥(V ⊔ conjSubgroup x V) ∧
      conjSubgroup x V ≤ Λ ∧ Λ ≠ ⊤ ∧
      ∀ α : MulAut K0, (∀ v ∈ V, α v = v) → Λ.map α.toMonoidHom ≤ Λ := by
  obtain ⟨a, b, haV, hbV, ha1, hb1, hab⟩ := exists_two_gens h4
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := hV.2 v hv
    rwa [pow_two] at this
  have hcommV : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := fun u hu v hv => elemAbelian_mul_comm hV hu hv
  have hk := kleinC_of ha1 hb1 hab (hsq a haV) (hsq b hbV) (hcommV a haV b hbV)
  obtain ⟨G, hG, hGa⟩ : ∃ G ∈ pslPairs, cjp G (kap a) = a0 := by
    have h1 := List.all_eq_true.mp inv_conj (kap a) (kap_mem a)
    have hne : (kap a != cid && cmul (kap a) (kap a) == cid) = true := by
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      refine ⟨fun h => ha1 (kap_injective (by rw [kap_one]; exact h)), ?_⟩
      rw [← kap_mul, hsq a haV, kap_one]
    rw [hne, Bool.not_true, Bool.false_or] at h1
    obtain ⟨G, hG, hGe⟩ := List.any_eq_true.mp h1
    exact ⟨G, hG, beq_iff_eq.mp hGe⟩
  obtain ⟨c, rfl⟩ := mem_pslPairs hG
  rw [cjp_kap] at hGa
  set V' := conjSubgroup c V with hV'
  set a' := c * a * c⁻¹ with ha'
  set b' := c * b * c⁻¹ with hb'
  have hsq' : ∀ v ∈ V', v * v = 1 := by
    intro v hv
    rw [hV', mem_conjSubgroup] at hv
    have := hsq _ hv
    calc v * v = c * ((c⁻¹ * v * c) * (c⁻¹ * v * c)) * c⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hcomm' : ∀ u ∈ V', ∀ v ∈ V', u * v = v * u := by
    intro u hu v hv
    rw [hV', mem_conjSubgroup] at hu hv
    have := hcommV _ hu _ hv
    calc u * v = c * ((c⁻¹ * u * c) * (c⁻¹ * v * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * v * c) * (c⁻¹ * u * c)) * c⁻¹ := by rw [this]
      _ = v * u := by group
  have ha'V : a' ∈ V' := by
    rw [hV', mem_conjSubgroup]
    simpa [ha', mul_assoc] using haV
  have hb'V : b' ∈ V' := by
    rw [hV', mem_conjSubgroup]
    simpa [hb', mul_assoc] using hbV
  have hne1 : a' ≠ 1 := by
    intro h
    apply ha1
    have : a = c⁻¹ * (c * a * c⁻¹) * c := by group
    rw [this, ← ha', h]
    group
  have hne2 : b' ≠ 1 := by
    intro h
    apply hb1
    have : b = c⁻¹ * (c * b * c⁻¹) * c := by group
    rw [this, ← hb', h]
    group
  have hne3 : a' ≠ b' := by
    intro h
    apply hab
    have h' : c * a * c⁻¹ = c * b * c⁻¹ := h
    simpa using h'
  have hk' := kleinC_of hne1 hne2 hne3 (hsq' _ ha'V) (hsq' _ hb'V) (hcomm' _ ha'V _ hb'V)
  have hkA : kap a' = a0 := hGa
  rw [hkA] at hk'
  have hc' : checkKlein a0 (kap b') = true := by
    have := List.all_eq_true.mp checkAll (kap b') (kap_mem b')
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h | h
    · rw [hk'] at h
      exact absurd h (by decide)
    · exact h
  have hV'mem : ∀ v, v ∈ V' ↔ v = 1 ∨ v = a' ∨ v = b' ∨ v = a' * b' := by
    intro v
    constructor
    · intro hv
      have h1 := List.all_eq_true.mp kleinClosed_std (kap b') (kap_mem b')
      rw [hk'] at h1
      simp only [Bool.not_true, Bool.false_or] at h1
      have h2 := List.all_eq_true.mp h1 (kap v) (kap_mem v)
      have hcond : (cmul (kap v) (kap v) == cid && cmul (kap v) a0 == cmul a0 (kap v) &&
          cmul (kap v) (kap b') == cmul (kap b') (kap v)) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [← kap_mul, hsq' v hv, kap_one]
        · rw [← hkA, ← kap_mul, ← kap_mul, hcomm' _ hv _ ha'V]
        · rw [← kap_mul, ← kap_mul, hcomm' _ hv _ hb'V]
      rw [hcond, Bool.not_true, Bool.false_or] at h2
      rw [← hkA] at h2
      exact (inV_kap_iff a' b' v).mp h2
    · rintro (h | h | h | h)
      · rw [h]; exact V'.one_mem
      · rw [h]; exact ha'V
      · rw [h]; exact hb'V
      · rw [h]; exact V'.mul_mem ha'V hb'V
  have hc'' : checkKlein (kap a') (kap b') = true := by rw [hkA]; exact hc'
  have hk'' : kleinC (kap a') (kap b') = true := by rw [hkA]; exact hk'
  obtain ⟨x, Λ, h1, h2, h3, h4'⟩ := exists_inv_data_of_check V' hV'mem hk'' hc''
  exact transfer_inv_data (MulAut.conj c) V x Λ h1 h2 h3 h4'

end CFSG.ClassicalGroups.A6Klein
