module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin.Q8Pair

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem mem_sup {H H' : Subgroup G} (h : Commutes H H') {x : G} (hx : x ∈ H ⊔ H') :
    ∃ l ∈ H, ∃ l' ∈ H', x = l * l' := by
  let T : Subgroup G :=
    { carrier := {x | ∃ l ∈ H, ∃ l' ∈ H', x = l * l'}
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, l₁', hl₁', rfl⟩ ⟨l₂, hl₂, l₂', hl₂', rfl⟩
        refine ⟨l₁ * l₂, H.mul_mem hl₁ hl₂, l₁' * l₂', H'.mul_mem hl₁' hl₂', ?_⟩
        calc l₁ * l₁' * (l₂ * l₂') = l₁ * (l₁' * l₂) * l₂' := by group
          _ = l₁ * (l₂ * l₁') * l₂' := by rw [← h l₂ hl₂ l₁' hl₁']
          _ = l₁ * l₂ * (l₁' * l₂') := by group
      one_mem' := ⟨1, H.one_mem, 1, H'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨l, hl, l', hl', rfl⟩
        refine ⟨l⁻¹, H.inv_mem hl, l'⁻¹, H'.inv_mem hl', ?_⟩
        calc (l * l')⁻¹ = l'⁻¹ * l⁻¹ := by group
          _ = l⁻¹ * l'⁻¹ := by
            have := h l⁻¹ (H.inv_mem hl) l'⁻¹ (H'.inv_mem hl')
            exact this.symm }
  have hle : H ⊔ H' ≤ T := sup_le (fun l hl => ⟨l, hl, 1, H'.one_mem, by simp⟩)
    (fun l' hl' => ⟨1, H.one_mem, l', hl', by simp⟩)
  exact hle hx

theorem comm_sq {L : Subgroup G} (e : ↥L ≃* QuaternionGroup 2) {a b : G} (ha : a ∈ L) (hb : b ∈ L) :
    (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
  have h4 : ∀ x y : QuaternionGroup 2, (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) = 1 := by decide
  have h3 := h4 (e ⟨a, ha⟩) (e ⟨b, hb⟩)
  have h5 : ((⟨a, ha⟩ : ↥L) * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) *
      ((⟨a, ha⟩ : ↥L) * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
    apply e.injective
    simp only [map_mul, map_inv, map_one]
    exact h3
  exact congrArg Subtype.val h5

theorem sq_mem_member {L : Subgroup G} {zL : G} (hz : IsUniqueInvolution L zL)
    (e : ↥L ≃* QuaternionGroup 2) {l : G} (hl : l ∈ L) : l * l = 1 ∨ l * l = zL := by
  have h4 : ∀ q : QuaternionGroup 2, q * q * (q * q) = 1 := by decide
  have h3 := h4 (e ⟨l, hl⟩)
  have h5 : (⟨l, hl⟩ : ↥L) * ⟨l, hl⟩ * (⟨l, hl⟩ * ⟨l, hl⟩) = 1 := by
    apply e.injective
    rw [map_mul, map_mul, map_one]
    exact h3
  exact hz.unique (l * l) (L.mul_mem hl hl) (congrArg Subtype.val h5)

variable {Lp Lm : Subgroup G} {zL : G}

theorem sq_mem (hp : IsUniqueInvolution Lp zL) (hm : IsUniqueInvolution Lm zL)
    (hc : Commutes Lp Lm) (ep : ↥Lp ≃* QuaternionGroup 2) (em : ↥Lm ≃* QuaternionGroup 2)
    {x : G} (hx : x ∈ Lp ⊔ Lm) : x * x = 1 ∨ x * x = zL := by
  obtain ⟨l, hl, l', hl', rfl⟩ := mem_sup hc hx
  have e1 : l * l' * (l * l') = (l * l) * (l' * l') := by
    calc l * l' * (l * l') = l * (l' * l) * l' := by group
      _ = l * (l * l') * l' := by rw [← hc l hl l' hl']
      _ = (l * l) * (l' * l') := by group
  rw [e1]
  rcases sq_mem_member hp ep hl with h1 | h1 <;> rcases sq_mem_member hm em hl' with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; rw [h1, h2, one_mul]
  · right; rw [h1, h2, mul_one]
  · left; rw [h1, h2, hp.sq]

theorem comm_mem (hp : IsUniqueInvolution Lp zL) (hm : IsUniqueInvolution Lm zL)
    (hc : Commutes Lp Lm) (ep : ↥Lp ≃* QuaternionGroup 2) (em : ↥Lm ≃* QuaternionGroup 2)
    {x y : G} (hx : x ∈ Lp ⊔ Lm) (hy : y ∈ Lp ⊔ Lm) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = zL := by
  obtain ⟨a, ha, a', ha', rfl⟩ := mem_sup hc hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_sup hc hy
  have hP : (a * b * a⁻¹ * b⁻¹) ∈ Lp :=
    Lp.mul_mem (Lp.mul_mem (Lp.mul_mem ha hb) (Lp.inv_mem ha)) (Lp.inv_mem hb)
  have hR : (a' * b' * a'⁻¹ * b'⁻¹) ∈ Lm :=
    Lm.mul_mem (Lm.mul_mem (Lm.mul_mem ha' hb') (Lm.inv_mem ha')) (Lm.inv_mem hb')
  have e1 : a * a' * (b * b') * (a * a')⁻¹ * (b * b')⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (a' * b' * a'⁻¹ * b'⁻¹) := by
    have c1 : a' * b = b * a' := (hc b hb a' ha').symm
    have c2 : a⁻¹ * (a' * b' * a'⁻¹) = (a' * b' * a'⁻¹) * a⁻¹ :=
      hc _ (Lp.inv_mem ha) _ (Lm.mul_mem (Lm.mul_mem ha' hb') (Lm.inv_mem ha'))
    have c3 : (a' * b' * a'⁻¹ * b'⁻¹) * b⁻¹ = b⁻¹ * (a' * b' * a'⁻¹ * b'⁻¹) :=
      (hc _ (Lp.inv_mem hb) _ hR).symm
    calc a * a' * (b * b') * (a * a')⁻¹ * (b * b')⁻¹
        = a * (a' * b) * b' * a'⁻¹ * a⁻¹ * b'⁻¹ * b⁻¹ := by group
      _ = a * (b * a') * b' * a'⁻¹ * a⁻¹ * b'⁻¹ * b⁻¹ := by rw [c1]
      _ = a * b * (a' * b' * a'⁻¹) * a⁻¹ * b'⁻¹ * b⁻¹ := by group
      _ = a * b * ((a' * b' * a'⁻¹) * a⁻¹) * b'⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * (a' * b' * a'⁻¹)) * b'⁻¹ * b⁻¹ := by rw [c2]
      _ = a * b * a⁻¹ * (a' * b' * a'⁻¹ * b'⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * (b⁻¹ * (a' * b' * a'⁻¹ * b'⁻¹)) := by rw [mul_assoc (a * b * a⁻¹), c3]
      _ = (a * b * a⁻¹ * b⁻¹) * (a' * b' * a'⁻¹ * b'⁻¹) := by group
  rw [e1]
  have hP2 := comm_sq ep ha hb
  have hR2 := comm_sq em ha' hb'
  rcases hp.unique _ hP hP2 with h1 | h1 <;> rcases hm.unique _ hR hR2 with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; rw [h1, h2, one_mul]
  · right; rw [h1, h2, mul_one]
  · left; rw [h1, h2, hp.sq]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin.Q8Pair
