module

public import CFSG.LargeExtraspecial.AS35GCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.SignalizerFunctor.Helpers

namespace AschTI

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem conj_eq_inv_of_commutator_mem (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M)
    (hPab : ∀ a ∈ S.tiP g, ∀ b ∈ S.tiP g, a * b = b * a) {x : G} (hx : x ∈ S.QG)
    (hxR : x ∉ S.tiR g) (hcom : ∀ p ∈ S.tiP g, x * p * x⁻¹ * p⁻¹ ∈ S.tiR g) :
    ∀ r ∈ S.tiR g, x * r * x⁻¹ = r⁻¹ := by
  let φ : S.tiP g → S.tiR g := fun p => ⟨x * p * x⁻¹ * (p : G)⁻¹, hcom p p.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    have h : x * p * x⁻¹ * p⁻¹ = x * q * x⁻¹ * q⁻¹ := congrArg Subtype.val hpq
    by_contra hne
    have hpq1 : p⁻¹ * q ≠ 1 := fun h1 => hne (Subtype.ext (by
      calc p = p * (p⁻¹ * q) := by rw [h1, mul_one]
        _ = q := by group))
    have hcomm : x * (p⁻¹ * q) = p⁻¹ * q * x := by
      calc x * (p⁻¹ * q) = ((x * p * x⁻¹ * p⁻¹) * p)⁻¹ * ((x * q * x⁻¹ * q⁻¹) * q) * x := by
            group
        _ = ((x * q * x⁻¹ * q⁻¹) * p)⁻¹ * ((x * q * x⁻¹ * q⁻¹) * q) * x := by rw [h]
        _ = p⁻¹ * q * x := by group
    have hxt := centralizer_le_of_mem_tiP S hTI (mul_mem (inv_mem hp) hq) hpq1
      (mem_centralizer_singleton_iff.mpr hcomm)
    exact hxR ⟨hx, hxt⟩
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [card_tiR_eq_card_tiP S hTI hgM hgz])
  have hxx : x * x ∈ S.tiR g := by
    rcases S.sq_eq_one_or_z hx with h | h
    · rw [← pow_two, h]
      exact one_mem _
    · rw [← pow_two, h]
      exact z_mem_tiR S hgz
  obtain ⟨⟨p₀, hp₀P⟩, hp₀⟩ := hbij.2 ⟨x * x, hxx⟩
  have hp₀' : x * p₀ * x⁻¹ * p₀⁻¹ = x * x := congrArg Subtype.val hp₀
  have hinvx : p₀ * x * p₀⁻¹ = x⁻¹ := by
    have h1 : p₀ * x⁻¹ * p₀⁻¹ = x := by
      calc p₀ * x⁻¹ * p₀⁻¹ = x⁻¹ * (x * p₀ * x⁻¹ * p₀⁻¹) := by group
        _ = x := by rw [hp₀']; group
    calc p₀ * x * p₀⁻¹ = (p₀ * x⁻¹ * p₀⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [h1]
  intro r hr
  obtain ⟨⟨p, hpP⟩, hp⟩ := hbij.2 ⟨r, hr⟩
  have hp' : x * p * x⁻¹ * p⁻¹ = r := congrArg Subtype.val hp
  have hp₀p : p₀ * p * p₀⁻¹ = p := by
    rw [hPab _ hp₀P _ hpP]
    group
  have hp₀r : p₀ * r * p₀⁻¹ = r := by
    rw [← commute_of_mem_tiR_of_mem_tiP S hTI hgM hr hp₀P]
    group
  have hr' : r = x⁻¹ * p * x * p⁻¹ := by
    calc r = p₀ * r * p₀⁻¹ := hp₀r.symm
      _ = p₀ * (x * p * x⁻¹ * p⁻¹) * p₀⁻¹ := by rw [hp']
      _ = (p₀ * x * p₀⁻¹) * (p₀ * p * p₀⁻¹) * (p₀ * x * p₀⁻¹)⁻¹ * (p₀ * p * p₀⁻¹)⁻¹ := by
          group
      _ = x⁻¹ * p * x * p⁻¹ := by rw [hinvx, hp₀p]; group
  calc x * r * x⁻¹ = x * (x⁻¹ * p * x * p⁻¹) * x⁻¹ := by rw [hr']
    _ = (x * p * x⁻¹ * p⁻¹)⁻¹ := by group
    _ = r⁻¹ := by rw [hp']

theorem false_of_isMulCommutative (hn : 3 ≤ S.width)
    (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G} (hgM : g ∉ S.M)
    (hgz : g * S.z * g⁻¹ ∈ S.M)
    (hW : IsMulCommutative (relativeWeakClosure S.QG (S.tiP g) (S.QG ⊔ S.tiP g))) : False := by
  set W := relativeWeakClosure S.QG (S.tiP g) (S.QG ⊔ S.tiP g) with hWdef
  have hWc : W ≤ centralizer (W : Set G) := le_centralizer_iff_isMulCommutative.mpr hW
  have hPW : S.tiP g ≤ W := subgroup_le_relative_weak_closure _ _ _ le_sup_right
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.mp (hWc hb) a ha
  have hPab : ∀ a ∈ S.tiP g, ∀ b ∈ S.tiP g, a * b = b * a := fun a ha b hb =>
    hcomm a (hPW ha) b (hPW hb)
  have hcom : ∀ x ∈ S.QG, ∀ p ∈ S.tiP g, x * p * x⁻¹ * p⁻¹ ∈ S.tiR g := by
    intro x hx p hp
    have h1 : x * p * x⁻¹ * p⁻¹ ∈ W :=
      W.mul_mem (conj_mem_relativeWeakClosure S hx hp) (W.inv_mem (hPW hp))
    exact ⟨commutator_mem_QG S hx hp.2,
      mem_centralizer_singleton_iff.mpr (hcomm _ h1 _ (hPW (t_mem_tiP S hgz)))⟩
  have hinv : ∀ x ∈ S.QG, x ∉ S.tiR g → ∀ r ∈ S.tiR g, x * r * x⁻¹ = r⁻¹ := fun x hx hxR =>
    conj_eq_inv_of_commutator_mem S hTI hgM hgz hPab hx hxR (hcom x hx)
  obtain ⟨x₁, hx₁, hx₁R⟩ := Set.not_subset.mp (not_QG_le_tiR S hgM hgz)
  have hRab : ∀ a ∈ S.tiR g, ∀ b ∈ S.tiR g, a * b = b * a := by
    intro a ha b hb
    have h1 := hinv x₁ hx₁ hx₁R (a * b) (mul_mem ha hb)
    have h2 : x₁ * (a * b) * x₁⁻¹ = (x₁ * a * x₁⁻¹) * (x₁ * b * x₁⁻¹) := by group
    rw [h2, hinv x₁ hx₁ hx₁R a ha, hinv x₁ hx₁ hx₁R b hb, mul_inv_rev] at h1
    have h3 := congrArg (fun w => w⁻¹) h1
    simpa only [mul_inv_rev, inv_inv] using h3.symm
  have hsq : ∀ r ∈ S.tiR g, r * r = 1 := by
    intro r hr
    by_cases hr1 : r = 1
    · rw [hr1, mul_one]
    by_cases hrz : r = S.z
    · rw [hrz, S.z_mul_z]
    by_cases hD : S.QG ⊓ centralizer ({r} : Set G) ≤ S.tiR g
    · exfalso
      have hsub : (S.tiR g : Set G) ⊆ {1, S.z, r, r * S.z} := by
        intro a ha
        have haC : a ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({r} : Set G) : Subgroup G) :
            Set G) :=
          ⟨ha.1, mem_centralizer_iff.mpr fun d hd => (hRab a ha d (hD hd)).symm⟩
        rcases (S.mem_centralizer_centralizer_iff hr.1).mp haC with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      have h4 := card_le_four_of_subset hsub
      have h8 := eight_le_card_tiR S hn hgz
      omega
    · obtain ⟨y, hyD, hyR⟩ := Set.not_subset.mp hD
      have h1 := hinv y hyD.1 hyR r hr
      have h2 : y * r * y⁻¹ = r := by
        rw [mem_centralizer_singleton_iff.mp hyD.2]
        group
      rw [h2] at h1
      exact mul_eq_one_iff_eq_inv.mpr h1
  have hcen : ∀ r ∈ S.tiR g, ∀ y ∈ S.QG, r * y = y * r := by
    intro r hr y hy
    by_cases hyR : y ∈ S.tiR g
    · exact hRab r hr y hyR
    · have h1 := hinv y hy hyR r hr
      rw [inv_eq_of_mul_eq_one_right (hsq r hr)] at h1
      calc r * y = (y * r * y⁻¹) * y := by rw [h1]
        _ = y * r := by group
  have hsub : (S.tiR g : Set G) ⊆ {1, S.z, 1, S.z} := by
    intro r hr
    rcases S.eq_one_or_z_of_commute hr.1 (hcen r hr) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have h4 := card_le_four_of_subset hsub
  have h8 := eight_le_card_tiR S hn hgz
  omega

end AschTI

end CFSG.LargeExtraspecial
