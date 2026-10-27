module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.CGT.Foote81L6.Normalizer

private theorem dihedralEight_pair_aux : ∀ x y : DihedralGroup 4, x ≠ y → x * x = 1 → x ≠ 1 →
    y * y = 1 → y ≠ 1 →
    (∀ c : DihedralGroup 4, c * x * c⁻¹ = x ∨ c * x * c⁻¹ = y) →
    (∀ c : DihedralGroup 4, c * y * c⁻¹ = x ∨ c * y * c⁻¹ = y) →
    x * y = y * x ∧ (∀ c : DihedralGroup 4, c * (x * y) = x * y * c) ∧ x * y ≠ 1 ∧
      x * y ≠ x ∧ x * y ≠ y ∧ (∃ c : DihedralGroup 4, c * x * c⁻¹ = y) ∧
      (∀ c : DihedralGroup 4, c * x = x * c → c * y = y * c →
        c = 1 ∨ c = x ∨ c = y ∨ c = x * y) ∧
      (∃ e : DihedralGroup 4, x * e ≠ e * x ∧ y * e ≠ e * y ∧
        ∀ b : DihedralGroup 4, Xor (b * x * e = e * (b * x)) (b * e = e * b)) := by
  decide

theorem dihedralEight_pair {H : Type*} [Group H] (ψ : H ≃* DihedralGroup 4) {x y : H}
    (hxy : x ≠ y) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hcx : ∀ c : H, c * x * c⁻¹ = x ∨ c * x * c⁻¹ = y)
    (hcy : ∀ c : H, c * y * c⁻¹ = x ∨ c * y * c⁻¹ = y) :
    x * y = y * x ∧ (∀ c : H, c * (x * y) = x * y * c) ∧ x * y ≠ 1 ∧ x * y ≠ x ∧ x * y ≠ y ∧
      (∃ c : H, c * x * c⁻¹ = y) ∧
      (∀ c : H, c * x = x * c → c * y = y * c → c = 1 ∨ c = x ∨ c = y ∨ c = x * y) ∧
      (∃ e : H, x * e ≠ e * x ∧ y * e ≠ e * y ∧
        ∀ b : H, Xor (b * x * e = e * (b * x)) (b * e = e * b)) := by
  have hinj := ψ.injective
  have key := dihedralEight_pair_aux (ψ x) (ψ y) (hinj.ne hxy)
    (by rw [← map_mul, hx2, map_one]) (fun h => hx1 (hinj (h.trans (map_one ψ).symm)))
    (by rw [← map_mul, hy2, map_one]) (fun h => hy1 (hinj (h.trans (map_one ψ).symm)))
    (fun c => by
      obtain ⟨c, rfl⟩ := ψ.surjective c
      rcases hcx c with h | h
      · exact Or.inl (by rw [← map_inv, ← map_mul, ← map_mul, h])
      · exact Or.inr (by rw [← map_inv, ← map_mul, ← map_mul, h]))
    (fun c => by
      obtain ⟨c, rfl⟩ := ψ.surjective c
      rcases hcy c with h | h
      · exact Or.inl (by rw [← map_inv, ← map_mul, ← map_mul, h])
      · exact Or.inr (by rw [← map_inv, ← map_mul, ← map_mul, h]))
  obtain ⟨h1, h2, h3, h4, h5, ⟨c, hc⟩, h7, ⟨e, he1, he2, he3⟩⟩ := key
  have hmul : ∀ a b : H, ψ a * ψ b = ψ (a * b) := fun a b => (map_mul ψ a b).symm
  refine ⟨hinj (by rw [map_mul, map_mul, h1]), fun c => hinj (by
      simp only [map_mul]; exact h2 (ψ c)), fun h => h3 (by rw [hmul, h, map_one]),
    fun h => h4 (by rw [hmul, h]), fun h => h5 (by rw [hmul, h]),
    ⟨ψ.symm c, hinj (by rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc])⟩,
    fun c hcx' hcy' => ?_, ⟨ψ.symm e, ?_, ?_, fun b => ?_⟩⟩
  · rcases h7 (ψ c) (by rw [hmul, hcx', ← hmul]) (by rw [hmul, hcy', ← hmul]) with
      h | h | h | h
    · exact Or.inl (hinj (by rw [h, map_one]))
    · exact Or.inr (Or.inl (hinj h))
    · exact Or.inr (Or.inr (Or.inl (hinj h)))
    · exact Or.inr (Or.inr (Or.inr (hinj (by rw [h, map_mul]))))
  · intro h
    apply he1
    rw [← MulEquiv.apply_symm_apply ψ e, hmul, h, ← hmul]
  · intro h
    apply he2
    rw [← MulEquiv.apply_symm_apply ψ e, hmul, h, ← hmul]
  · have hiff1 : b * x * ψ.symm e = ψ.symm e * (b * x) ↔ ψ b * ψ x * e = e * (ψ b * ψ x) := by
      rw [← hinj.eq_iff, map_mul, map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply]
    have hiff2 : b * ψ.symm e = ψ.symm e * b ↔ ψ b * e = e * ψ b := by
      rw [← hinj.eq_iff, map_mul, map_mul, MulEquiv.apply_symm_apply]
    have := he3 (ψ b)
    unfold Xor at this ⊢
    rw [hiff1, hiff2]
    exact this

theorem dihedralEight_fusion {X : Type*} [Group X] {D : Subgroup X} (ψ : D ≃* DihedralGroup 4)
    {d₀ d₁ : X} (hd₀ : d₀ ∈ D) (hd₁ : d₁ ∈ D) (hne : d₀ ≠ d₁) (h02 : d₀ * d₀ = 1) (h01 : d₀ ≠ 1)
    (h12 : d₁ * d₁ = 1) (h11 : d₁ ≠ 1)
    (hc₀ : ∀ c ∈ D, c * d₀ * c⁻¹ = d₀ ∨ c * d₀ * c⁻¹ = d₁)
    (hc₁ : ∀ c ∈ D, c * d₁ * c⁻¹ = d₀ ∨ c * d₁ * c⁻¹ = d₁) :
    d₀ * d₁ = d₁ * d₀ ∧ (∀ c ∈ D, c * (d₀ * d₁) = d₀ * d₁ * c) ∧ d₀ * d₁ ≠ 1 ∧
      d₀ * d₁ ≠ d₀ ∧ d₀ * d₁ ≠ d₁ ∧ (∃ c ∈ D, c * d₀ * c⁻¹ = d₁) ∧
      (∀ c ∈ D, c * d₀ = d₀ * c → c * d₁ = d₁ * c → c = 1 ∨ c = d₀ ∨ c = d₁ ∨ c = d₀ * d₁) ∧
      ∃ Q : Subgroup X, Q ≤ D ∧ Q.relIndex D = 2 ∧ d₀ ∉ Q ∧ d₁ ∉ Q := by
  set x : D := ⟨d₀, hd₀⟩
  set y : D := ⟨d₁, hd₁⟩
  have hval : ∀ a b : D, a = b ↔ (a : X) = b := fun a b => Subtype.ext_iff
  obtain ⟨h1, h2, h3, h4, h5, ⟨c, hc⟩, h7, ⟨e, he1, he2, he3⟩⟩ := dihedralEight_pair ψ
    (x := x) (y := y) (fun h => hne (congrArg Subtype.val h)) (Subtype.ext h02)
    (fun h => h01 (congrArg Subtype.val h)) (Subtype.ext h12)
    (fun h => h11 (congrArg Subtype.val h))
    (fun c => by
      rcases hc₀ c c.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h))
    (fun c => by
      rcases hc₁ c c.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h))
  refine ⟨congrArg Subtype.val h1, fun c hc' => congrArg Subtype.val (h2 ⟨c, hc'⟩),
    fun h => h3 (Subtype.ext h), fun h => h4 (Subtype.ext h), fun h => h5 (Subtype.ext h),
    ⟨c, c.2, congrArg Subtype.val hc⟩, fun c hc' hcx hcy => ?_, ?_⟩
  · rcases h7 ⟨c, hc'⟩ (Subtype.ext hcx) (Subtype.ext hcy) with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  · set QH : Subgroup D := Subgroup.centralizer {e}
    have hQH : QH.index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨x, fun b => ?_⟩
      simp only [QH, Subgroup.mem_centralizer_singleton_iff]
      exact he3 b
    refine ⟨QH.map D.subtype, Subgroup.map_subtype_le QH, ?_, ?_, ?_⟩
    · rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
      exact hQH
    · rintro ⟨b, hb, hbx⟩
      have hbx' : b = x := Subtype.ext hbx
      have hxQ : x ∈ QH := hbx' ▸ hb
      exact he1 (Subgroup.mem_centralizer_singleton_iff.mp hxQ)
    · rintro ⟨b, hb, hby⟩
      have hby' : b = y := Subtype.ext hby
      have hyQ : y ∈ QH := hby' ▸ hb
      exact he2 (Subgroup.mem_centralizer_singleton_iff.mp hyQ)

end CFSG.CGT.Foote81L6.Normalizer
