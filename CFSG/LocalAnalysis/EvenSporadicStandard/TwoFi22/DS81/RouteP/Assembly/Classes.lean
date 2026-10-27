module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem isConj_or_isConj_of_two_classes {M : Type*} [Group M] {u v t z : M}
    (huv : ∀ a : M, a * a = 1 → a ≠ 1 → IsConj a u ∨ IsConj a v) (ht : t * t = 1) (ht1 : t ≠ 1)
    (hz : z * z = 1) (hz1 : z ≠ 1) (htz : ¬ IsConj t z) :
    ∀ a : M, a * a = 1 → a ≠ 1 → IsConj a t ∨ IsConj a z := by
  intro a ha ha1
  rcases huv t ht ht1 with htu | htv <;> rcases huv z hz hz1 with hzu | hzv
  · exact absurd (htu.trans hzu.symm) htz
  · rcases huv a ha ha1 with hau | hav
    · exact Or.inl (hau.trans htu.symm)
    · exact Or.inr (hav.trans hzv.symm)
  · rcases huv a ha ha1 with hau | hav
    · exact Or.inr (hau.trans hzu.symm)
    · exact Or.inl (hav.trans htv.symm)
  · exact absurd (htv.trans hzv.symm) htz

theorem _root_.MulEquiv.isConj_or_isConj_of_two_classes {M J : Type*} [Group M] [Group J]
    (θ : M ≃* J) {u v : J} (huv : ∀ a : J, a * a = 1 → a ≠ 1 → IsConj a u ∨ IsConj a v) :
    ∀ a : M, a * a = 1 → a ≠ 1 → IsConj a (θ.symm u) ∨ IsConj a (θ.symm v) := by
  intro a ha ha1
  have h2 : θ a * θ a = 1 := by rw [← map_mul, ha, map_one]
  have h1 : θ a ≠ 1 := by simpa using ha1
  have key : ∀ {w : J}, IsConj (θ a) w → IsConj a (θ.symm w) := fun {w} hw => by
    simpa using θ.symm.toMonoidHom.map_isConj hw
  rcases huv (θ a) h2 h1 with h | h
  · exact Or.inl (key h)
  · exact Or.inr (key h)

theorem exists_mem_conj_or_exists_mem_conj_of_two_classes {G : Type*} [Group G] (M : Subgroup G)
    {u v : M} (huv : ∀ a : M, a * a = 1 → a ≠ 1 → IsConj a u ∨ IsConj a v)
    {t z : G} (htM : t ∈ M) (hzM : z ∈ M) (ht : orderOf t = 2) (hz : orderOf z = 2)
    (htz : ¬ IsConj t z) :
    ∀ a ∈ M, orderOf a = 2 →
      (∃ m ∈ M, m * t * m⁻¹ = a) ∨ (∃ m ∈ M, m * z * m⁻¹ = a) := by
  have hsq : ∀ {x : G}, orderOf x = 2 → x * x = 1 ∧ x ≠ 1 := fun {x} hx => by
    rw [orderOf_eq_prime_iff, sq] at hx
    exact hx
  obtain ⟨ht2, ht1⟩ := hsq ht
  obtain ⟨hz2, hz1⟩ := hsq hz
  have hcls := isConj_or_isConj_of_two_classes (t := (⟨t, htM⟩ : M)) (z := (⟨z, hzM⟩ : M)) huv
    (Subtype.ext ht2) (fun h => ht1 (congrArg Subtype.val h))
    (Subtype.ext hz2) (fun h => hz1 (congrArg Subtype.val h))
    (fun h => htz (by simpa using M.subtype.map_isConj h))
  intro a haM hord
  obtain ⟨ha2, ha1⟩ := hsq hord
  have key : ∀ {x : G} (hx : x ∈ M), IsConj (⟨a, haM⟩ : M) ⟨x, hx⟩ →
      ∃ m ∈ M, m * x * m⁻¹ = a := by
    intro x hx h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine ⟨(c : G)⁻¹, M.inv_mem c.2, ?_⟩
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc (c : G)⁻¹ * x * (c : G)⁻¹⁻¹ = (c : G)⁻¹ * (c * a * (c : G)⁻¹) * ((c : G)⁻¹)⁻¹ := by
          rw [this]
      _ = a := by group
  rcases hcls ⟨a, haM⟩ (Subtype.ext ha2) (fun h => ha1 (congrArg Subtype.val h)) with h | h
  · exact Or.inl (key htM h)
  · exact Or.inr (key hzM h)

theorem exists_mem_conj_or_exists_mem_conj_of_mulEquiv {G J : Type*} [Group G] [Group J]
    (M : Subgroup G) (θ : M ≃* J) {u v : J}
    (huv : ∀ a : J, a * a = 1 → a ≠ 1 → IsConj a u ∨ IsConj a v)
    {t z : G} (htM : t ∈ M) (hzM : z ∈ M) (ht : orderOf t = 2) (hz : orderOf z = 2)
    (htz : ¬ IsConj t z) :
    ∀ a ∈ M, orderOf a = 2 →
      (∃ m ∈ M, m * t * m⁻¹ = a) ∨ (∃ m ∈ M, m * z * m⁻¹ = a) :=
  exists_mem_conj_or_exists_mem_conj_of_two_classes M (θ.isConj_or_isConj_of_two_classes huv)
    htM hzM ht hz htz

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
