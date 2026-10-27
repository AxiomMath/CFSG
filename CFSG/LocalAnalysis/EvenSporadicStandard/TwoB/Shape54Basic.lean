module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.K54Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem Level55.false_of_invariant_sup_zpowers (d : Level55 G t z) {y : G}
    (hyY : y ∈ O2In (centPair z t)) (hyp : y ∉ pair z t)
    (hWinv : ∀ k ∈ centPair z t, ∀ w ∈ pair z t ⊔ zpowers y,
      k * w * k⁻¹ ∈ pair z t ⊔ zpowers y) : False := by
  have hWY : pair z t ⊔ zpowers y ≤ O2In (centPair z t) :=
    sup_le d.pair_le_O2K (zpowers_le.2 hyY)
  rcases d.irred _ le_sup_left hWY hWinv with h | h
  · exact hyp (h ▸ mem_sup_right (mem_zpowers y))
  · obtain ⟨a, ha, b, hb, hab⟩ := d.exists_noncomm_O2K
    have hcen : pair z t ≤ centralizer ((zpowers y : Subgroup G) : Set G) := by
      intro p hp
      rw [mem_centralizer_iff]
      intro u hu
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu
      exact (Commute.zpow_left (show Commute y p from (Act55.O2In_centPair_comm hp hyY).symm) j).eq
    have hdec : ∀ x ∈ O2In (centPair z t), ∃ u ∈ zpowers y, ∃ p ∈ pair z t, x = u * p := by
      intro x hx
      rw [← h, sup_comm] at hx
      exact exists_mul_of_mem_sup_of_le_centralizer hcen hx
    obtain ⟨u, hu, p, hp, rfl⟩ := hdec a ha
    obtain ⟨u', hu', p', hp', rfl⟩ := hdec b hb
    apply hab
    have hup : u * u' = u' * u := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu'
      exact (Commute.zpow_zpow_self y i j).eq
    have hpu : p * u' = u' * p := (mem_centralizer_iff.1 (hcen hp) u' hu').symm
    have hp'u : p' * u = u * p' := (mem_centralizer_iff.1 (hcen hp') u hu).symm
    calc u * p * (u' * p') = u * (p * u') * p' := by group
      _ = u * (u' * p) * p' := by rw [hpu]
      _ = (u * u') * (p * p') := by group
      _ = (u' * u) * (p' * p) := by rw [hup, d.pair_comm hp hp']
      _ = u' * (u * p') * p := by group
      _ = u' * (p' * u) * p := by rw [hp'u]
      _ = u' * p' * (u * p) := by group

section Certified


theorem Level55.mem_O2K_of_comm_mem_zpowers (d : Level55 G t z) {k : G}
    (hk : k ∈ centPair z t)
    (h : ∀ y ∈ O2In (centPair z t), k * y * k⁻¹ * y⁻¹ ∈ zpowers z) :
    k ∈ O2In (centPair z t) := by
  by_contra hkY
  let N : Subgroup G :=
    { carrier := {n | n ∈ centPair z t ∧
        ∀ y ∈ O2In (centPair z t), n * y * n⁻¹ * y⁻¹ ∈ zpowers z}
      mul_mem' := by
        rintro n₁ n₂ ⟨hn₁, h₁⟩ ⟨hn₂, h₂⟩
        refine ⟨mul_mem hn₁ hn₂, fun y hy => ?_⟩
        have e : n₁ * n₂ * y * (n₁ * n₂)⁻¹ * y⁻¹ =
            (n₁ * (n₂ * y * n₂⁻¹ * y⁻¹) * n₁⁻¹) * (n₁ * y * n₁⁻¹ * y⁻¹) := by group
        rw [e]
        exact mul_mem (d.conj_zpowers_z hn₁ _ (h₂ y hy)) (h₁ y hy)
      one_mem' := ⟨one_mem _, fun y hy => by simp⟩
      inv_mem' := by
        rintro n ⟨hn, hn'⟩
        refine ⟨inv_mem hn, fun y hy => ?_⟩
        have e : n⁻¹ * y * n⁻¹⁻¹ * y⁻¹ = n⁻¹ * (n * y * n⁻¹ * y⁻¹)⁻¹ * n⁻¹⁻¹ := by group
        rw [e]
        exact d.conj_zpowers_z (inv_mem hn) _ (inv_mem (hn' y hy)) }
  have hNK : ∀ g ∈ centPair z t, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    refine ⟨mul_mem (mul_mem hg hn.1) (inv_mem hg), fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ O2In (centPair z t) := by
      have := d.conj_O2K (inv_mem hg) y hy
      rwa [inv_inv] at this
    have e : g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹ * y⁻¹ =
        g * (n * (g⁻¹ * y * g) * n⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact d.conj_zpowers_z hg _ (hn.2 _ hy')
  have hnle : ¬ N ≤ O2In (centPair z t) := fun hle => hkY (hle (show k ∈ N from ⟨hk, h⟩))
  have hNeq : N = centPair z t := d.eq_K_of_not_le_O2K (fun n hn => hn.1) hNK hnle
  obtain ⟨y, hyY, hyp⟩ := d.exists_mem_O2K_not_mem_pair
  refine d.false_of_invariant_sup_zpowers hyY hyp fun k' hk' => ?_
  have hk'N : k' ∈ N := by rw [hNeq]; exact hk'
  refine conj_mem_sup_of_conj_mem (fun a ha => mem_sup_left (d.conj_pair hk' a ha))
    (conj_mem_zpowers_of_conj_mem ?_)
  have hc := hk'N.2 y hyY
  have e : k' * y * k'⁻¹ = (k' * y * k'⁻¹ * y⁻¹) * y := by group
  rw [e]
  exact Subgroup.mul_mem_sup (mem_sup_left hc) (mem_zpowers y)

end Certified

end CFSG.EvenSporadicStandard.TwoB
