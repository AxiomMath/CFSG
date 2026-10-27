module

public import CFSG.RankThree.Transfer.FixedPoints
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.GH74.Generic.S3

open Subgroup MulAction CFSG.RankThree.Transfer

section Transfer

variable {G : Type*} [Group G]

theorem transfer_eq_prod_of_forall_smul_eq [Finite G] {H : Subgroup G} {A : Type*}
    [CommGroup A] (ϕ : H →* A) (g : G) [Fintype (G ⧸ H)]
    (hg : ∀ X : G ⧸ H, g • X = X) :
    ϕ.transfer g = ∏ X : G ⧸ H, cosetValue ϕ g X := by
  classical
  have : Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H))) := Fintype.ofFinite _
  rw [ϕ.transfer_eq_prod_quotient_orbitRel_zpowers_quot g,
    ← Finset.prod_fiberwise Finset.univ
      (fun X : G ⧸ H => (Quotient.mk'' X : Quotient (orbitRel (zpowers g) (G ⧸ H))))]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hfib : ∀ X : G ⧸ H,
      (Quotient.mk'' X : Quotient (orbitRel (zpowers g) (G ⧸ H))) = q ↔
        X ∈ orbit (zpowers g) (Quotient.out q) := by
    intro X
    conv_lhs => rw [← Quotient.out_eq q]
    rw [Quotient.mk''_eq_mk, Quotient.eq, orbitRel_apply]
  have hX₀ : g • Quotient.out q = Quotient.out q := hg _
  have hper : Function.minimalPeriod (fun x => g • x) (Quotient.out q) = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hX₀
  have hfiber : (Finset.univ.filter fun X : G ⧸ H =>
      (Quotient.mk'' X : Quotient (orbitRel (zpowers g) (G ⧸ H))) = q) =
        {Quotient.out q} := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hfib]
    exact ⟨fun h => eq_of_mem_orbit_zpowers h hX₀, fun h => h ▸ mem_orbit_self _⟩
  rw [hfiber, Finset.prod_singleton]
  have h1 : (Quotient.out (Quotient.out q))⁻¹ * g * Quotient.out (Quotient.out q) ∈ H := by
    rw [← smul_coe_eq_iff, QuotientGroup.out_eq']
    exact hX₀
  have e : cosetValue ϕ g (Quotient.out q) = ϕ ⟨_, h1⟩ := by
    have := cosetValue_coe ϕ h1
    rwa [QuotientGroup.out_eq'] at this
  rw [e]
  congr 2
  rw [hper, pow_one]

end Transfer

theorem not_mem_commutator_of_conj_actions {X : Type*} [Group X] [Finite X] (X₁ : Subgroup X)
    (N₁ : Subgroup (MulAut ↥X₁)) (hN₁ : commutator (MulAut ↥X₁) ≤ N₁) (x : X)
    (hx : ∀ c : X, c⁻¹ * x * c ∈ normalizer (X₁ : Set X))
    (hx1 : x ∈ normalizer (X₁ : Set X)) (hx₁ : X₁.normalizerMonoidHom ⟨x, hx1⟩ ∉ N₁)
    (hxi : ∀ (c : X) (hc : c⁻¹ * x * c ∈ normalizer (X₁ : Set X)),
      c ∉ normalizer (X₁ : Set X) → X₁.normalizerMonoidHom ⟨c⁻¹ * x * c, hc⟩ ∈ N₁) :
    x ∉ commutator X := by
  classical
  set H : Subgroup X := normalizer (X₁ : Set X) with hH
  have : H.FiniteIndex := inferInstance
  have : Fintype (X ⧸ H) := Fintype.ofFinite _
  let ab : MulAut ↥X₁ →* Abelianization (MulAut ↥X₁) := Abelianization.of
  let N' : Subgroup (Abelianization (MulAut ↥X₁)) := N₁.map ab
  let q : Abelianization (MulAut ↥X₁) →* (Abelianization (MulAut ↥X₁) ⧸ N') :=
    QuotientGroup.mk' N'
  let ϕ : H →* (Abelianization (MulAut ↥X₁) ⧸ N') := (q.comp ab).comp X₁.normalizerMonoidHom
  intro hxc
  have hV : ϕ.transfer x = 1 := Abelianization.commutator_subset_ker (ϕ.transfer) hxc
  have hfix : ∀ Y : X ⧸ H, x • Y = Y := by
    intro Y
    rw [smul_eq_self_iff_out]
    exact hx _
  rw [transfer_eq_prod_of_forall_smul_eq ϕ x hfix] at hV
  have key : ∀ Y : X ⧸ H, Y ≠ ((1 : X) : X ⧸ H) → cosetValue ϕ x Y = 1 := by
    intro Y hY
    rw [cosetValue_of_mem ϕ (hx _)]
    have hc : (Quotient.out Y) ∉ H := by
      intro hmem
      apply hY
      rw [← QuotientGroup.out_eq' Y]
      rw [QuotientGroup.eq]
      simpa using H.inv_mem hmem
    have h1 := hxi (Quotient.out Y) (hx _) hc
    simp only [ϕ, MonoidHom.comp_apply]
    show q (ab _) = 1
    rw [QuotientGroup.mk'_apply]
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨_, h1, rfl⟩
  rw [Finset.prod_eq_single ((1 : X) : X ⧸ H) (fun Y _ hY => key Y hY)
    (fun h => absurd (Finset.mem_univ _) h)] at hV
  have h0 : cosetValue ϕ x ((1 : X) : X ⧸ H) = ϕ ⟨x, hx1⟩ := by
    have := cosetValue_coe ϕ (g := x) (x := (1 : X)) (by simpa using hx1)
    rw [this]
    congr 1
    apply Subtype.ext
    simp
  rw [h0] at hV
  simp only [ϕ, MonoidHom.comp_apply] at hV
  have hmem : ab (X₁.normalizerMonoidHom ⟨x, hx1⟩) ∈ N' := (QuotientGroup.eq_one_iff _).1 hV
  obtain ⟨n, hn, hn'⟩ := hmem
  apply hx₁
  have hker : X₁.normalizerMonoidHom ⟨x, hx1⟩ * n⁻¹ ∈ ab.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hn', mul_inv_cancel]
  rw [Abelianization.ker_of] at hker
  have := N₁.mul_mem (hN₁ hker) hn
  simpa using this

theorem not_mem_commutator_of_normalizer_or_conj_le {X : Type*} [Group X] [Finite X]
    (X₁ X₂ : Subgroup X) (N₁ : Subgroup (MulAut ↥X₁)) (hN₁ : commutator (MulAut ↥X₁) ≤ N₁) (x : X)
    (hx1 : x ∈ normalizer (X₁ : Set X)) (hx₂ : ∀ y ∈ X₂, y * x = x * y)
    (hconj : ∀ c : X, c ∈ normalizer (X₁ : Set X) ∨ ∀ y ∈ X₁, c * y * c⁻¹ ∈ X₂)
    (hx₁ : X₁.normalizerMonoidHom ⟨x, hx1⟩ ∉ N₁) : x ∉ commutator X := by
  have hcent : ∀ c : X, c ∉ normalizer (X₁ : Set X) → c⁻¹ * x * c ∈ centralizer (X₁ : Set X) := by
    intro c hc
    apply mem_centralizer_iff.2
    intro y hy
    rcases hconj c with h | h
    · exact absurd h hc
    · have hy' : c * y * c⁻¹ ∈ X₂ := h y hy
      have := hx₂ _ hy'
      calc y * (c⁻¹ * x * c) = c⁻¹ * ((c * y * c⁻¹) * x) * c := by group
        _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [this]
        _ = c⁻¹ * x * c * y := by group
  have hx : ∀ c : X, c⁻¹ * x * c ∈ normalizer (X₁ : Set X) := by
    intro c
    by_cases hc : c ∈ normalizer (X₁ : Set X)
    · exact (normalizer (X₁ : Set X)).mul_mem
        ((normalizer (X₁ : Set X)).mul_mem ((normalizer (X₁ : Set X)).inv_mem hc) hx1) hc
    · exact Subgroup.centralizer_le_normalizer (X₁ : Set X) (hcent c hc)
  refine not_mem_commutator_of_conj_actions X₁ N₁ hN₁ x hx hx1 hx₁ fun c hc hcn => ?_
  have h1 : X₁.normalizerMonoidHom ⟨c⁻¹ * x * c, hc⟩ = 1 := by
    ext y
    have hyc : (c⁻¹ * x * c) * (y : X) = (y : X) * (c⁻¹ * x * c) :=
      (mem_centralizer_iff.1 (hcent c hcn) y y.2).symm
    show (c⁻¹ * x * c) * (y : X) * (c⁻¹ * x * c)⁻¹ = (y : X)
    rw [hyc]
    group
  rw [h1]
  exact N₁.one_mem

end CFSG.GH74.Generic.S3
