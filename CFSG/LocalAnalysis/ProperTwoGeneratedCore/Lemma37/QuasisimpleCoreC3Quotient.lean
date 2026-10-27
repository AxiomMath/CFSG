module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePB1
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePCases

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

namespace CaseC3

theorem conj_self (h : CaseC3 T Q P₁ e u y) : y * u * y⁻¹ = u ∨ y * u * y⁻¹ = u * e := by
  have hc := h.partC
  have hmem : y * u * y⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp (h.le_normalizer h.mem) u).mp (Subgroup.mem_zpowers u)
  have hne := hc.self_ne
  rcases hc.mem_zpowers_self hmem with h1 | h1 | h1 | h1
  · exfalso
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hne.1 h1
  · exact Or.inl h1
  · exfalso
    rw [← hc.conj_centralElt y] at h1
    exact hne.2 (mul_left_cancel (mul_right_cancel h1))
  · exact Or.inr h1

theorem mem_of_conj_right (h : CaseC3 T Q P₁ e u y) {p : G} (hp : p ∈ P₁)
    (hfix : y * p * y⁻¹ = p ∨ y * p * y⁻¹ = p * e) : p = 1 ∨ p = e ∨ p = u ∨ p = u * e := by
  have hc := h.partC
  obtain ⟨φ⟩ := h.quaternion_right
  by_contra hne
  push Not at hne
  obtain ⟨hp1, hpe, hpu, hpue⟩ := hne
  have heP := hc.mem_right
  have he2 := hc.order
  have hpp := quaternion_mul_self_of_ne φ heP he2 hp hp1 hpe
  have hcen := hc.center
  have hee := hc.centralElt_mul_self
  have hu' := h.conj_self
  have he' : y * e * y⁻¹ = e ∨ y * e * y⁻¹ = e * e := Or.inl (hc.conj_centralElt y)
  have hF : ∀ w ∈ P₁, y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e := by
    intro w hw
    rcases quaternion_enum φ heP he2 hc.self_mem hp hw hc.sq hpp hpu hpue with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left
      group
    · exact he'
    · exact hu'
    · exact conj_mul_mod_central hcen hee hu' he'
    · exact hfix
    · exact conj_mul_mod_central hcen hee hfix he'
    · exact conj_mul_mod_central hcen hee hu' hfix
    · exact conj_mul_mod_central hcen hee (conj_mul_mod_central hcen hee hu' hfix) he'
  obtain ⟨m, hm, hm1, hm2⟩ := h.moved
  rcases hF m hm with h' | h'
  · exact hm1 h'
  · exact hm2 h'

theorem exists_inv_conj_left (h : CaseC3 T Q P₁ e u y) :
    ∃ v ∈ Q, v * v = e ∧ y * v * y⁻¹ = v⁻¹ ∧
      ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
        w = 1 ∨ w = e ∨ w = v ∨ w = v * e :=
  h.partC.exists_inv_conj h.mem h.not_mem (by rw [h.mul_self]; exact h.partC.mem_right)

end CaseC3

namespace PartC

theorem sup (hc : PartC T Q P₁ e u) : PartC (Q ⊔ P₁) Q P₁ e u where
  isPGroup := hc.isPGroup.to_le hc.sup_le
  left_le := le_sup_left
  right_le := le_sup_right
  quaternion := hc.quaternion
  commute := hc.commute
  mem_inf := hc.mem_inf
  order := hc.order
  center := hc.center
  mem_left := hc.mem_left
  mem_right := hc.mem_right
  self_mem := hc.self_mem
  sq := hc.sq
  unique := hc.unique
  normal_left := fun t ht q hq => hc.normal_left t (hc.sup_le ht) q hq
  normal_right := fun t ht p hp => hc.normal_right t (hc.sup_le ht) p hp
  involution_mem := fun _ ht _ => ht
  inv_mul_mem := fun _ ha _ _ ha' _ => absurd ha ha'
  outer := fun _ hy hy' => absurd hy hy'

variable (Z : Subgroup G) [Z.Normal]

omit [Z.Normal] in
theorem le_sup_of_mem_iff (hc : PartC T Q P₁ e u) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    Z ≤ Q ⊔ P₁ := fun x hx => by
  rcases (hZ x).mp hx with rfl | rfl
  · exact (Q ⊔ P₁).one_mem
  · exact Subgroup.mem_sup_left hc.mem_left

theorem mk_mem_map_iff_of_le {H : Subgroup G} (hZH : Z ≤ H) (x : G) :
    (x : G ⧸ Z) ∈ H.map (QuotientGroup.mk' Z) ↔ x ∈ H := by
  rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self (by
    rw [QuotientGroup.ker_mk']
    exact hZH)]

theorem nonempty_map_sup_mulEquiv (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    Nonempty (((Q ⊔ P₁).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) ≃*
      DihedralGroup 2 × DihedralGroup 2) :=
  hc.sup.nonempty_map_mulEquiv_dihedral φ rfl Z hZ

theorem card_map_sup (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    Nat.card ((Q ⊔ P₁).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) = 16 := by
  obtain ⟨θ⟩ := hc.nonempty_map_sup_mulEquiv Z φ hZ
  rw [Nat.card_congr θ.toEquiv, Nat.card_prod, DihedralGroup.nat_card]

theorem dihedralTwo_prod_pow_two : ∀ x : DihedralGroup 2 × DihedralGroup 2, x ^ 2 = 1 := by
  decide

theorem pow_two_eq_one_of_mem_map_sup (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {w : G ⧸ Z}
    (hw : w ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) : w ^ 2 = 1 := by
  obtain ⟨θ⟩ := hc.nonempty_map_sup_mulEquiv Z φ hZ
  have h1 : (⟨w, hw⟩ : ((Q ⊔ P₁).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z))) ^ 2 = 1 :=
    θ.injective (by rw [map_pow, dihedralTwo_prod_pow_two, map_one])
  simpa using congrArg Subtype.val h1

theorem relIndex_map_sup (hc : PartC T Q P₁ e u) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) :
    ((Q ⊔ P₁).map (QuotientGroup.mk' Z)).relIndex (T.map (QuotientGroup.mk' Z)) = 2 := by
  have hZW := hc.le_sup_of_mem_iff Z hZ
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨(y : G ⧸ Z), Subgroup.mem_map_of_mem _ hyT⟩, fun b => ?_⟩
  obtain ⟨b, hb⟩ := b
  obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hb
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, QuotientGroup.mk'_apply,
    ← QuotientGroup.mk_mul, mk_mem_map_iff_of_le Z hZW]
  by_cases ht : t ∈ Q ⊔ P₁
  · exact Or.inr ⟨ht, fun h => hy (by simpa using (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem ht) h)⟩
  · refine Or.inl ⟨?_, ht⟩
    have := hc.inv_mul_mem t⁻¹ (T.inv_mem htT) y hyT
      (fun h => ht (by simpa using (Q ⊔ P₁).inv_mem h)) hy
    rwa [inv_inv] at this

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
