module

public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

theorem cp_klein_quot {X : Type} [Group X] {P D : Subgroup X} [Finite P] (hDP : D ≤ P)
    (hDn : ∀ p ∈ P, ∀ d ∈ D, p * d * p⁻¹ ∈ D) {s r : X} (hs : s * s = 1) (hr : r * r = 1)
    (hsP : ∀ p ∈ P, s * p * s⁻¹ ∈ P) (hrP : ∀ p ∈ P, r * p * r⁻¹ ∈ P)
    (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D) (hrD : ∀ d ∈ D, r * d * r⁻¹ ∈ D)
    (h1 : ∀ p ∈ P, p⁻¹ * (s * p * s⁻¹) ∈ D → p ∈ D)
    (h2 : ∀ p ∈ P, p⁻¹ * (r * p * r⁻¹) ∈ D → p ∈ D)
    (h3 : ∀ p ∈ P, p⁻¹ * (s * (r * p * r⁻¹) * s⁻¹) ∈ D → p ∈ D) : P ≤ D := by
  let Q := ↥P
  let D' : Subgroup Q := D.subgroupOf P
  haveI hDnorm : D'.Normal := ⟨fun d hd p => by
    have hd' : (d : X) ∈ D := Subgroup.mem_subgroupOf.mp hd
    rw [Subgroup.mem_subgroupOf]
    change (p : X) * (d : X) * (p : X)⁻¹ ∈ D
    exact hDn (p : X) p.2 (d : X) hd'⟩
  let σfun : Q → Q := fun q => ⟨s * (q : X) * s⁻¹, hsP (q : X) q.2⟩
  let σ₀ : Q →* Q := MonoidHom.mk' σfun (by
    intro a b
    ext
    change s * ((a * b : Q) : X) * s⁻¹
      = (s * (a : X) * s⁻¹) * (s * (b : X) * s⁻¹)
    rw [Subgroup.coe_mul]
    group)
  have hσ₀ : ∀ q : Q, ((σ₀ q : Q) : X) = s * (q : X) * s⁻¹ := fun _ => rfl
  let τfun : Q → Q := fun q => ⟨r * (q : X) * r⁻¹, hrP (q : X) q.2⟩
  let τ₀ : Q →* Q := MonoidHom.mk' τfun (by
    intro a b
    ext
    change r * ((a * b : Q) : X) * r⁻¹
      = (r * (a : X) * r⁻¹) * (r * (b : X) * r⁻¹)
    rw [Subgroup.coe_mul]
    group)
  have hτ₀ : ∀ q : Q, ((τ₀ q : Q) : X) = r * (q : X) * r⁻¹ := fun _ => rfl
  let ρ₀ : Q →* Q := σ₀.comp τ₀
  have hρ₀ : ∀ q : Q, ((ρ₀ q : Q) : X) = s * (r * (q : X) * r⁻¹) * s⁻¹ := by
    intro q
    simp only [ρ₀, MonoidHom.comp_apply, hσ₀, hτ₀]
  have hσD : D' ≤ D'.comap σ₀ := fun d hd => by
    have hd' : (d : X) ∈ D := Subgroup.mem_subgroupOf.mp hd
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hσ₀]
    exact hsD (d : X) hd'
  have hτD : D' ≤ D'.comap τ₀ := fun d hd => by
    have hd' : (d : X) ∈ D := Subgroup.mem_subgroupOf.mp hd
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hτ₀]
    exact hrD (d : X) hd'
  have hρD : D' ≤ D'.comap ρ₀ := fun d hd => by
    have hd' : (d : X) ∈ D := Subgroup.mem_subgroupOf.mp hd
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hρ₀]
    exact hsD _ (hrD (d : X) hd')
  let E := Q ⧸ D'
  let σ : E →* E := QuotientGroup.map D' D' σ₀ hσD
  let τ : E →* E := QuotientGroup.map D' D' τ₀ hτD
  let ρ : E →* E := QuotientGroup.map D' D' ρ₀ hρD
  have hσinv : Function.Involutive σ := by
    intro e
    refine QuotientGroup.induction_on e ?_
    intro q
    change QuotientGroup.mk (σ₀ (σ₀ q)) = QuotientGroup.mk q
    congr 1
    ext
    rw [hσ₀, hσ₀]
    have hs' : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs, inv_one]
    calc s * (s * (q : X) * s⁻¹) * s⁻¹
        = (s * s) * (q : X) * (s⁻¹ * s⁻¹) := by group
      _ = (q : X) := by rw [hs, hs']; group
  have hτinv : Function.Involutive τ := by
    intro e
    refine QuotientGroup.induction_on e ?_
    intro q
    change QuotientGroup.mk (τ₀ (τ₀ q)) = QuotientGroup.mk q
    congr 1
    ext
    rw [hτ₀, hτ₀]
    have hr' : r⁻¹ * r⁻¹ = 1 := by rw [← mul_inv_rev, hr, inv_one]
    calc r * (r * (q : X) * r⁻¹) * r⁻¹
        = (r * r) * (q : X) * (r⁻¹ * r⁻¹) := by group
      _ = (q : X) := by rw [hr, hr']; group
  have hσfix : ∀ e : E, σ e = e → e = 1 := by
    intro e
    refine QuotientGroup.induction_on e ?_
    intro q he
    change QuotientGroup.mk (σ₀ q) = QuotientGroup.mk q at he
    have hmem : (q : Q)⁻¹ * σ₀ q ∈ D' := QuotientGroup.eq.mp he.symm
    have hXD : (q : X)⁻¹ * (s * (q : X) * s⁻¹) ∈ D := by
      have h' := Subgroup.mem_subgroupOf.mp hmem
      change (q : X)⁻¹ * ((σ₀ q : Q) : X) ∈ D at h'
      rwa [hσ₀] at h'
    exact (QuotientGroup.eq_one_iff q).mpr
      (Subgroup.mem_subgroupOf.mpr (h1 (q : X) q.2 hXD))
  have hτfix : ∀ e : E, τ e = e → e = 1 := by
    intro e
    refine QuotientGroup.induction_on e ?_
    intro q he
    change QuotientGroup.mk (τ₀ q) = QuotientGroup.mk q at he
    have hmem : (q : Q)⁻¹ * τ₀ q ∈ D' := QuotientGroup.eq.mp he.symm
    have hXD : (q : X)⁻¹ * (r * (q : X) * r⁻¹) ∈ D := by
      have h' := Subgroup.mem_subgroupOf.mp hmem
      change (q : X)⁻¹ * ((τ₀ q : Q) : X) ∈ D at h'
      rwa [hτ₀] at h'
    exact (QuotientGroup.eq_one_iff q).mpr
      (Subgroup.mem_subgroupOf.mpr (h2 (q : X) q.2 hXD))
  have hσ_inv : ∀ e : E, σ e = e⁻¹ := by
    have h := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hσfix hσinv
    intro e
    exact congrFun h e
  have hτ_inv : ∀ e : E, τ e = e⁻¹ := by
    have h := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hτfix hτinv
    intro e
    exact congrFun h e
  have hρeq : ∀ e : E, ρ e = σ (τ e) := by
    intro e
    refine QuotientGroup.induction_on e ?_
    intro q
    rfl
  have hρid : ∀ e : E, ρ e = e := by
    intro e
    rw [hρeq e, hτ_inv e, hσ_inv (e⁻¹)]
    exact inv_inv e
  have hρfix : ∀ e : E, ρ e = e → e = 1 := by
    intro e
    refine QuotientGroup.induction_on e ?_
    intro q he
    change QuotientGroup.mk (ρ₀ q) = QuotientGroup.mk q at he
    have hmem : (q : Q)⁻¹ * ρ₀ q ∈ D' := QuotientGroup.eq.mp he.symm
    have hXD : (q : X)⁻¹ * (s * (r * (q : X) * r⁻¹) * s⁻¹) ∈ D := by
      have h' := Subgroup.mem_subgroupOf.mp hmem
      change (q : X)⁻¹ * ((ρ₀ q : Q) : X) ∈ D at h'
      rwa [hρ₀] at h'
    exact (QuotientGroup.eq_one_iff q).mpr
      (Subgroup.mem_subgroupOf.mpr (h3 (q : X) q.2 hXD))
  have hsub : Subsingleton E := ⟨fun e f => by
    rw [hρfix e (hρid e), hρfix f (hρid f)]⟩
  have htop : D' = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton D' hsub
  intro p hp
  have hp' : (⟨p, hp⟩ : Q) ∈ D' := by
    rw [htop]
    exact Subgroup.mem_top _
  simpa using Subgroup.mem_subgroupOf.mp hp'

end CFSG.EvenSporadicStandard.HNRecog.Section4
