module

public import CFSG.Goldschmidt.Steps.StrongEmb

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.BenderSuzuki

section Emb

variable {C : Type*} [Group C]

theorem orderOf_conj_eq (g a : C) : orderOf (g * a * g⁻¹) = orderOf a := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) a
  rwa [MulAut.conj_apply] at this

theorem card_centralizer_conj (c a : C) :
    Nat.card (Subgroup.centralizer ({c * a * c⁻¹} : Set C)) =
      Nat.card (Subgroup.centralizer ({a} : Set C)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨c⁻¹ * g * c, ?_⟩
      invFun := fun g => ⟨c * g * c⁻¹, ?_⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] }
  · have hg := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * g * c * a = c⁻¹ * (g * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * g) * c := by rw [hg]
      _ = a * (c⁻¹ * g * c) := by group
  · have hg := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * g * c⁻¹ * (c * a * c⁻¹) = c * (g * a) * c⁻¹ := by group
      _ = c * (a * g) * c⁻¹ := by rw [hg]
      _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group

theorem card_centralizer_eq_of_isConj {a b : C} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set C)) =
      Nat.card (Subgroup.centralizer ({b} : Set C)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (card_centralizer_conj c a).symm

theorem exists_involution_mem_of_even [Finite C] {K : Subgroup C} (h : Even (Nat.card K)) :
    ∃ u ∈ K, orderOf u = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (even_iff_two_dvd.1 h)
  exact ⟨u, u.2, by rw [Subgroup.orderOf_coe]; exact hu⟩

theorem mem_map_conj_iff (D : Subgroup C) (g y : C) :
    y ∈ D.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ D := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem eq_top_of_involutions [Finite C] {D : Subgroup C}
    (hcent : ∀ t ∈ D, orderOf t = 2 → Subgroup.centralizer ({t} : Set C) ≤ D)
    (hconj : ∀ t ∈ D, ∀ u ∈ D, orderOf t = 2 → orderOf u = 2 →
      Nat.card (Subgroup.centralizer ({t} : Set C)) =
        Nat.card (Subgroup.centralizer ({u} : Set C)) → ∃ k ∈ D, k * u * k⁻¹ = t)
    {t₀ t₁ : C} (ht₀ : t₀ ∈ D) (ht₁ : t₁ ∈ D) (ho₀ : orderOf t₀ = 2) (ho₁ : orderOf t₁ = 2)
    (hne : Nat.card (Subgroup.centralizer ({t₀} : Set C)) ≠
      Nat.card (Subgroup.centralizer ({t₁} : Set C))) : D = ⊤ := by
  by_contra hD
  have hodd : ∀ g ∉ D, Odd (Nat.card (D ⊓ D.map (MulAut.conj g).toMonoidHom : Subgroup C)) := by
    intro g hg
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨u, hu, hu2⟩ := exists_involution_mem_of_even hev
    obtain ⟨huD, huDg⟩ := Subgroup.mem_inf.1 hu
    have hd : g⁻¹ * u * g ∈ D := (mem_map_conj_iff D g u).1 huDg
    have hd2 : orderOf (g⁻¹ * u * g) = 2 := by
      have := orderOf_conj_eq g⁻¹ u
      rw [inv_inv] at this
      rw [this, hu2]
    have hcard : Nat.card (Subgroup.centralizer ({g⁻¹ * u * g} : Set C)) =
        Nat.card (Subgroup.centralizer ({u} : Set C)) := by
      have := card_centralizer_conj g⁻¹ u
      rwa [inv_inv] at this
    obtain ⟨k, hk, hku⟩ := hconj _ hd u huD hd2 hu2 hcard
    have hgk : g * k ∈ Subgroup.centralizer ({u} : Set C) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * k * u = g * (k * u * k⁻¹) * k := by group
        _ = g * (g⁻¹ * u * g) * k := by rw [hku]
        _ = u * (g * k) := by group
    have h1 := D.mul_mem (hcent u huD hu2 hgk) (D.inv_mem hk)
    rw [mul_inv_cancel_right] at h1
    exact hg h1
  have hev : Even (Nat.card D) := by
    have := Subgroup.orderOf_dvd_natCard D ht₀
    rw [ho₀] at this
    exact even_iff_two_dvd.2 this
  have hSE : IsStronglyEmbeddedOrder D := ⟨hD, hev, hodd⟩
  by_cases hout : ∃ v : C, orderOf v = 2 ∧ v ∉ D
  · obtain ⟨v, hv, hvD⟩ := hout
    have h0 := CFSG.Goldschmidt.isConj_of_mem_of_not_mem hSE ho₀ hv ht₀ hvD
    have h1 := CFSG.Goldschmidt.isConj_of_mem_of_not_mem hSE ho₁ hv ht₁ hvD
    exact hne ((card_centralizer_eq_of_isConj h0).trans (card_centralizer_eq_of_isConj h1).symm)
  · push Not at hout
    obtain ⟨g, hg⟩ : ∃ g : C, g ∉ D := by
      by_contra h
      push Not at h
      exact hD (eq_top_iff.2 fun g _ => h g)
    have ht₀g : t₀ ∈ D.map (MulAut.conj g).toMonoidHom := by
      rw [mem_map_conj_iff]
      refine hout _ ?_
      have := orderOf_conj_eq g⁻¹ t₀
      rw [inv_inv] at this
      rw [this, ho₀]
    have h2 := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.2 ⟨ht₀, ht₀g⟩)
    rw [ho₀] at h2
    exact (Nat.not_even_iff_odd.2 (hodd g hg)) (even_iff_two_dvd.2 h2)

end Emb

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
