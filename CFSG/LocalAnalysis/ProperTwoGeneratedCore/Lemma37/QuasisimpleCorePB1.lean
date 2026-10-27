module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePB1Char

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup CFSG.Semidihedral.CentralQuotients

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u : G} {M : ℕ}

@[expose] noncomputable def prodHom (hc : PartC T Q P₁ e u) (φQ : Q ≃* QuaternionGroup 2)
    (φ : P₁ ≃* QuaternionGroup M) : QuaternionGroup 2 × QuaternionGroup M →* G :=
  MonoidHom.noncommCoprod (Q.subtype.comp φQ.symm.toMonoidHom)
    (P₁.subtype.comp φ.symm.toMonoidHom) fun x y => hc.commute _ (φQ.symm x).2 _ (φ.symm y).2

theorem prodHom_apply (hc : PartC T Q P₁ e u) (φQ : Q ≃* QuaternionGroup 2)
    (φ : P₁ ≃* QuaternionGroup M) (xy : QuaternionGroup 2 × QuaternionGroup M) :
    hc.prodHom φQ φ xy = ((φQ.symm xy.1 : Q) : G) * ((φ.symm xy.2 : P₁) : G) := rfl

theorem range_prodHom (hc : PartC T Q P₁ e u) (φQ : Q ≃* QuaternionGroup 2)
    (φ : P₁ ≃* QuaternionGroup M) : (hc.prodHom φQ φ).range = Q ⊔ P₁ := by
  ext x
  rw [MonoidHom.mem_range, hc.mem_sup_iff]
  constructor
  · rintro ⟨xy, rfl⟩
    exact ⟨_, (φQ.symm xy.1).2, _, (φ.symm xy.2).2, rfl⟩
  · rintro ⟨q, hq, p, hp, rfl⟩
    exact ⟨(φQ ⟨q, hq⟩, φ ⟨p, hp⟩), by simp [prodHom_apply]⟩

theorem symm_mem_iff_left (hc : PartC T Q P₁ e u) (φQ : Q ≃* QuaternionGroup 2)
    (x : QuaternionGroup 2) :
    (((φQ.symm x : Q) : G) = 1 ∨ ((φQ.symm x : Q) : G) = e) ↔ x ∈ nativeQuaternionZ 2 := by
  rw [mem_nativeQuaternionZ_iff (by norm_num), Nat.cast_ofNat,
    ← quaternion_map_eq φQ hc.mem_left hc.order]
  constructor
  · rintro (h | h)
    · left
      rw [← φQ.apply_symm_apply x, show φQ.symm x = 1 from Subtype.ext h, map_one]
    · right
      rw [← φQ.apply_symm_apply x, show φQ.symm x = ⟨e, hc.mem_left⟩ from Subtype.ext h]
  · rintro (rfl | rfl)
    · left
      rw [map_one]
      rfl
    · right
      rw [MulEquiv.symm_apply_apply]

theorem symm_mem_iff_right [NeZero M] (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup M)
    (y : QuaternionGroup M) :
    (((φ.symm y : P₁) : G) = 1 ∨ ((φ.symm y : P₁) : G) = e) ↔ y ∈ nativeQuaternionZ M := by
  rw [mem_nativeQuaternionZ_iff (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)),
    ← hc.map_centralElt_right φ]
  constructor
  · rintro (h | h)
    · left
      rw [← φ.apply_symm_apply y, show φ.symm y = 1 from Subtype.ext h, map_one]
    · right
      rw [← φ.apply_symm_apply y, show φ.symm y = ⟨e, hc.mem_right⟩ from Subtype.ext h]
  · rintro (rfl | rfl)
    · left
      rw [map_one]
      rfl
    · right
      rw [MulEquiv.symm_apply_apply]

theorem ker_mk_comp_prodHom [NeZero M] (hc : PartC T Q P₁ e u) (φQ : Q ≃* QuaternionGroup 2)
    (φ : P₁ ≃* QuaternionGroup M) (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    ((QuotientGroup.mk' Z).comp (hc.prodHom φQ φ)).ker =
      (nativeQuaternionZ 2).prod (nativeQuaternionZ M) := by
  ext ⟨x, y⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    hZ, prodHom_apply, Subgroup.mem_prod, ← hc.symm_mem_iff_left φQ, ← hc.symm_mem_iff_right φ]
  set q := ((φQ.symm x : Q) : G)
  set p := ((φ.symm y : P₁) : G)
  have hq : q ∈ Q := (φQ.symm x).2
  have hp : p ∈ P₁ := (φ.symm y).2
  have he := hc.centralElt_inv
  constructor
  · intro h
    have hqP : q ∈ P₁ := by
      rcases h with h | h
      · rw [eq_inv_of_mul_eq_one_left h]
        exact P₁.inv_mem hp
      · rw [show q = e * p⁻¹ by rw [← h]; group]
        exact P₁.mul_mem hc.mem_right (P₁.inv_mem hp)
    have hq' := hc.mem_inf q hq hqP
    refine ⟨hq', ?_⟩
    rcases h with h | h <;> rcases hq' with hq' | hq'
    · left
      rw [hq', one_mul] at h
      exact h
    · right
      rw [hq'] at h
      calc p = e⁻¹ * (e * p) := by group
        _ = e := by rw [h, he, mul_one]
    · right
      rw [hq', one_mul] at h
      exact h
    · left
      rw [hq'] at h
      calc p = e⁻¹ * (e * p) := by group
        _ = 1 := by rw [h, he, hc.centralElt_mul_self]
  · rintro ⟨hq' | hq', hp' | hp'⟩ <;> rw [hq', hp']
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul e)
    · exact Or.inr (mul_one e)
    · exact Or.inl hc.centralElt_mul_self

theorem nonempty_map_mulEquiv_dihedral [NeZero M] (hc : PartC T Q P₁ e u)
    (φ : P₁ ≃* QuaternionGroup M) (hT : T = Q ⊔ P₁) (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    Nonempty ((T.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) ≃*
      DihedralGroup 2 × DihedralGroup M) := by
  obtain ⟨φQ⟩ := hc.quaternion
  set θ := (QuotientGroup.mk' Z).comp (hc.prodHom φQ φ) with hθ
  have hrange : θ.range = T.map (QuotientGroup.mk' Z) := by
    rw [hθ, MonoidHom.range_comp, range_prodHom, hT]
  set π₂ := (quaternionToDihedral 2).prodMap (quaternionToDihedral M) with hπ₂
  have hsurj : Function.Surjective π₂ := fun ⟨d₁, d₂⟩ => by
    obtain ⟨x, hx⟩ := quaternionToDihedral_surjective 2 d₁
    obtain ⟨y, hy⟩ := quaternionToDihedral_surjective M d₂
    exact ⟨(x, y), by simp [hπ₂, hx, hy]⟩
  have hker : θ.ker = π₂.ker := by
    rw [hθ, hc.ker_mk_comp_prodHom φQ φ Z hZ, hπ₂, MonoidHom.ker_prodMap,
      quaternionToDihedral_ker, quaternionToDihedral_ker]
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange θ).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective π₂ hsurj))⟩

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
