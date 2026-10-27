module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Data

public section

namespace CFSG.EvenSporadicStandard.Solomon78

@[expose] def CenterInvAt {Y : Type*} [Group Y] (r : Y) : Prop :=
  ∀ z : Y, z * z = 1 → (∀ y : Y, y * r = r * y → z * y = y * z) → z = 1 ∨ z = r

theorem CenterInvAt.of_isConj {Y : Type*} [Group Y] {w r : Y} (h : IsConj w r)
    (hr : CenterInvAt r) : CenterInvAt w := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  intro z hz2 hzc
  have hw : w = c⁻¹ * r * c := by rw [← hc]; group
  have h1 := hr (c * z * c⁻¹) (by
      calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
        _ = 1 := by rw [hz2]; group) (by
      intro y hy
      have hy' : (c⁻¹ * y * c) * w = w * (c⁻¹ * y * c) := by
        calc c⁻¹ * y * c * w = c⁻¹ * (y * r) * c := by rw [hw]; group
          _ = c⁻¹ * (r * y) * c := by rw [hy]
          _ = w * (c⁻¹ * y * c) := by rw [hw]; group
      have h2 := hzc _ hy'
      calc c * z * c⁻¹ * y = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by rw [h2]
        _ = y * (c * z * c⁻¹) := by group)
  rcases h1 with h1 | h1
  · left
    have : z = c⁻¹ * (c * z * c⁻¹) * c := by group
    rw [this, h1]
    group
  · right
    have : z = c⁻¹ * (c * z * c⁻¹) * c := by group
    rw [this, h1, hw]

theorem commute_coe_of_central {M : Type*} [Group M] {H : Subgroup M} {a z : H}
    (hzc : ∀ y : H, y * a = a * y → z * y = y * z) {g : M} (hg : g ∈ H)
    (hga : g * (a : M) = (a : M) * g) : (z : M) * g = g * (z : M) := by
  have h := congrArg Subtype.val (hzc ⟨g, hg⟩ (Subtype.ext (by simpa using hga)))
  simpa using h

theorem pow_four_eq_one_of_mul_self {M : Type*} [Group M] {H : Subgroup M} {z : H}
    (h : z * z = 1) : (z : M) ^ 4 = 1 := by
  have h2 : z ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp only [sq]
    rw [h, one_mul]
  have := congrArg Subtype.val h2
  simpa using this

theorem CenterInvolutions.of_classes {Y : Type} [Group Y] (reps : List Y)
    (hcov : ∀ s : Y, orderOf s = 2 → ∃ r ∈ reps, IsConj s r)
    (hreps : ∀ r ∈ reps, CenterInvAt r) : CenterInvolutions Y := by
  intro a z ha hz2 _ hzc
  obtain ⟨r, hr, hconj⟩ := hcov a ha
  exact CenterInvAt.of_isConj hconj (hreps r hr) z hz2 hzc

theorem CenterInvolutions.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CenterInvolutions X) : CenterInvolutions Y := by
  intro a z ha hz2 hza hzc
  have ha' : orderOf (e.symm a) = 2 :=
    (orderOf_injective e.symm.toMonoidHom e.symm.injective a).trans ha
  have h1 := h (e.symm a) (e.symm z) ha' (by rw [← map_mul, hz2, map_one]) (by
      rw [← map_mul, ← map_mul, hza]) (by
      intro y hy
      apply e.injective
      rw [map_mul, map_mul]
      have := hzc (e y) (by
        apply e.symm.injective
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
        exact hy)
      simpa using this)
  rcases h1 with h1 | h1
  · left
    have := congrArg e h1
    simpa using this
  · right
    have := congrArg e h1
    simpa using this

end CFSG.EvenSporadicStandard.Solomon78
