module

public import CFSG.GH74.GLS.SP.Local.SPLCtC3

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtX

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G} {T T₀ T₁ : Subgroup G} {y : G}

omit [Finite G] in
theorem SPLCtT.y_norm_T₀ (hT : SPLCtT D T T₀ T₁ y) : ∀ a ∈ T₀, y * a * y⁻¹ ∈ T₀ :=
  fun a ha => hT.T₀_norm y hT.y_mem a ha

omit [Finite G] in
theorem SPLCtT.mem_Y (hs : SPLSetup D.toSPLNot0) (hT : SPLCtT D T T₀ T₁ y) {g : G}
    (hg : g ∈ T₀ ⊔ zpowers y) : ∃ t₀ ∈ T₀, g = t₀ ∨ g = t₀ * y := by
  have hnorm : zpowers y ≤ normalizer (T₀ : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => hT.y_norm_T₀ a ha
    · intro ha
      have h1 := hT.T₀_norm y⁻¹ (T.inv_mem hT.y_mem) _ ha
      have e : y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a := by group
      rwa [e] at h1
  obtain ⟨n, hn, k, hk, hgnk⟩ := sup_decomp_of_le_normalizer hnorm hg
  have hy2 : orderOf y = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hT.y_sq) ?_
    intro h1
    apply hT.y_not_mem hs
    rw [h1]; exact one_mem _
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hk
  rcases zpow_cases_two' hy2 j with h | h
  · exact ⟨n, hn, Or.inl (by rw [hgnk, h, mul_one])⟩
  · exact ⟨n, hn, Or.inr (by rw [hgnk, h])⟩

omit [Finite G] in
theorem SPLCtT.Y_inf_T₁ (hs : SPLSetup D.toSPLNot0) (hT : SPLCtT D T T₀ T₁ y) :
    (T₀ ⊔ zpowers y) ⊓ T₁ = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgY, hgT₁⟩
  rw [Subgroup.mem_bot]
  obtain ⟨t₀, ht₀, h | h⟩ := hT.mem_Y hs hgY
  · have : g ∈ T₀ ⊓ T₁ := ⟨h ▸ ht₀, hgT₁⟩
    rw [hT.T₀_inf_T₁, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply hT.y_not_mem hs
    have : y = t₀⁻¹ * g := by rw [h]; group
    rw [this]
    exact Subgroup.mul_mem_sup (T₀.inv_mem ht₀) hgT₁

omit [Finite G] in
theorem exists_x (hs : SPLSetup D.toSPLNot0) (hT : SPLCtT D T T₀ T₁ y) :
    ∃ x : G, x ∈ T₀ ⊔ zpowers y ∧ orderOf x = 2 ^ (D.n - 1) ∧ x ^ (2 ^ (D.n - 2)) = D.t ∧
      D.z * x * D.z⁻¹ = x⁻¹ ∧ zpowers x ⊔ zpowers D.z = T₀ ⊔ zpowers y ∧
      x ∉ zpowers (x ^ 2) ⊔ zpowers D.z ∧ T₀ = zpowers (x ^ 2) ⊔ zpowers D.z := by
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hYT : T₀ ⊔ zpowers y ≤ T := sup_le (T₀_le_T D hT) (zpowers_le.mpr hT.y_mem)
  have htc : ∀ a ∈ T₀ ⊔ zpowers y, D.t * a = a * D.t := fun a ha => (hT.t_central a (hYT ha)).symm
  have hzt : D.z ≠ D.t := fun h => hs.syl.t_nconj (h ▸ IsConj.refl _)
  obtain ⟨x, hxY, hxo, hxt, hzx, hYgen, hxn⟩ := dihedral_rotation hn3 (T₀ ⊔ zpowers y)
    hT.T₀y_dih D.t D.z (Subgroup.mem_sup_left hT.t_T₀) (Subgroup.mem_sup_left hT.z_T₀)
    hs.syl.t_ord htc hs.syl.z_inv hzt
  refine ⟨x, hxY, hxo, hxt, hzx, hYgen, hxn, ?_⟩
  exact dihedral_index_two_sub hn3 (T₀ ⊔ zpowers y) T₀ le_sup_left hT.T₀y_dih hT.T₀_dih x D.z hxo
    hzx hYgen hT.z_T₀ hs.syl.z_inv

theorem x_sq_cen_A (hs : SPLSetup D.toSPLNot0) (hT : SPLCtT D T T₀ T₁ y) {x : G} (hxT : x ∈ T)
    (hzx : D.z * x * D.z⁻¹ = x⁻¹) : ∀ a ∈ D.Act, x ^ 2 * a = a * x ^ 2 := by
  intro a ha
  have hxCt : x ∈ D.Ct := hT.T_le hxT
  have hb : x⁻¹ * a * x ∈ D.Act := by
    have := Act_normal D x⁻¹ (D.Ct.inv_mem hxCt) a ha
    simpa using this
  have h1 := Act_inv D hs _ hb
  have hzxinv : D.z * x⁻¹ * D.z⁻¹ = x := by
    have : (D.z * x * D.z⁻¹)⁻¹ = D.z * x⁻¹ * D.z⁻¹ := by group
    rw [← this, hzx, inv_inv]
  have hxzx : x * D.z * x⁻¹ = x ^ 2 * D.z := by
    have e1 : x * D.z * x⁻¹ = x * (D.z * x⁻¹ * D.z⁻¹) * D.z := by group
    rw [e1, hzxinv, pow_two]
  have h2 : (x ^ 2 * D.z) * a * (x ^ 2 * D.z)⁻¹ = a⁻¹ := by
    calc (x ^ 2 * D.z) * a * (x ^ 2 * D.z)⁻¹ = (x * D.z * x⁻¹) * a * (x * D.z * x⁻¹)⁻¹ := by
          rw [hxzx]
      _ = x * (D.z * (x⁻¹ * a * x) * D.z⁻¹) * x⁻¹ := by group
      _ = x * (x⁻¹ * a * x)⁻¹ * x⁻¹ := by rw [h1]
      _ = a⁻¹ := by group
  have h3 : (x ^ 2 * D.z) * a * (x ^ 2 * D.z)⁻¹ = x ^ 2 * a⁻¹ * (x ^ 2)⁻¹ := by
    calc (x ^ 2 * D.z) * a * (x ^ 2 * D.z)⁻¹ = x ^ 2 * (D.z * a * D.z⁻¹) * (x ^ 2)⁻¹ := by group
      _ = x ^ 2 * a⁻¹ * (x ^ 2)⁻¹ := by rw [Act_inv D hs a ha]
  have h4 : x ^ 2 * a⁻¹ * (x ^ 2)⁻¹ = a⁻¹ := h3.symm.trans h2
  have h5 : x ^ 2 * a⁻¹ = a⁻¹ * x ^ 2 := by
    calc x ^ 2 * a⁻¹ = (x ^ 2 * a⁻¹ * (x ^ 2)⁻¹) * x ^ 2 := by group
      _ = a⁻¹ * x ^ 2 := by rw [h4]
  have h6 : Commute (x ^ 2) a⁻¹ := h5
  simpa using h6.inv_right.eq

end CtX

end CFSG.GH74.GLS.SP.Local
