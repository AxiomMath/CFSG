module


public import CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

public section

namespace CFSG.LinearAlgebra.CoprimeActions.OddFixedSpaceCentralizerCommutator

theorem centralizes {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : H →* (V ≃ₗ[ZMod 2] V)) (S R B : Subgroup H)
    (hS : IsPGroup 2 S) (hR : Odd (Nat.card R))
    (hBR : B ≤ Subgroup.normalizer (R : Set H))
    (hRS : R ≤ Subgroup.centralizer (S : Set H))
    (hfaith : ∀ r ∈ R, (∀ v, σ r v = v) → r = 1)
    (hB : ∀ b ∈ B, ∀ v : V, (∀ s ∈ S, σ s v = v) → σ b v = v) :
    B ≤ Subgroup.centralizer (R : Set H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hk : r * (b * r⁻¹ * b⁻¹) ∈ R := by
    have h1 : b * r⁻¹ * b⁻¹ ∈ R := by
      have := (Subgroup.mem_normalizer_iff.1 (hBR hb) r⁻¹).1 (R.inv_mem hr)
      simpa using this
    exact R.mul_mem hr h1
  let ρ : R →* (V ≃ₗ[ZMod 2] V) := σ.comp R.subtype
  let σS : S →* (V ≃ₗ[ZMod 2] V) := σ.comp S.subtype
  have hcomm : ∀ (g : R) (x : S) (u : V), ρ g (σS x u) = σS x (ρ g u) := by
    intro g x u
    have hc : (g : H) * x = x * g := by
      have := Subgroup.mem_centralizer_iff.1 (hRS g.2) x x.2
      exact this.symm
    show σ g (σ x u) = σ x (σ g u)
    rw [← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul, ← hc]
  have hSfix : IsPGroup 2 S := hS
  have hpres : ∀ (g : H), g ∈ R → ∀ v : V, (∀ s ∈ S, σ s v = v) → ∀ s ∈ S, σ s (σ g v) = σ g v := by
    intro g hg v hv s hs
    have hc : g * s = s * g := (Subgroup.mem_centralizer_iff.1 (hRS hg) s hs).symm
    rw [← LinearEquiv.mul_apply, ← map_mul, ← hc, map_mul, LinearEquiv.mul_apply, hv s hs]
  set k : H := r * (b * r⁻¹ * b⁻¹) with hkdef
  have hkfix : (⟨k, hk⟩ : R) ∈ CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.fixedKernel ρ σS := by
    rw [CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.mem_fixedKernel]
    intro u hu
    have hu' : ∀ s ∈ S, σ s u = u := fun s hs => hu ⟨s, hs⟩
    have hbi : b⁻¹ ∈ B := B.inv_mem hb
    have step1 : σ b⁻¹ u = u := hB b⁻¹ hbi u hu'
    have step2 : σ r⁻¹ u ∈ {v : V | ∀ s ∈ S, σ s v = v} := hpres r⁻¹ (R.inv_mem hr) u hu'
    show σ (r * (b * r⁻¹ * b⁻¹)) u = u
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [step1]
    have h3 : σ b (σ r⁻¹ u) = σ r⁻¹ u := hB b hb _ step2
    rw [h3]
    have : σ r (σ r⁻¹ u) = u := by
      rw [← LinearEquiv.mul_apply, ← map_mul]; simp
    exact this
  have hord : Nat.Coprime (orderOf (ρ ⟨k, hk⟩)) 2 := by
    have hdvd : orderOf (ρ ⟨k, hk⟩) ∣ Nat.card R :=
      (orderOf_map_dvd ρ _).trans (orderOf_dvd_natCard _)
    exact (Nat.coprime_two_right).2 (Odd.of_dvd_nat hR hdvd)
  have hall := fun u =>
    CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.eq_of_coprime_of_mem_fixedKernel
      hSfix hcomm hkfix hord u
  have : k = 1 := hfaith k hk (fun v => hall v)
  have h2 : r * (b * r⁻¹ * b⁻¹) = 1 := this
  have h4 : r * b = b * r := by
    have : r * b * r⁻¹ * b⁻¹ = 1 := by simpa [mul_assoc] using h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  exact h4

end CFSG.LinearAlgebra.CoprimeActions.OddFixedSpaceCentralizerCommutator

end
