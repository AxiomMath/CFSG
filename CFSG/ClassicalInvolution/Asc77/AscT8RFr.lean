module

public import CFSG.ClassicalInvolution.Asc77.AscT8RX

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8R

section Odd

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mul_mem_odd {P N : Subgroup G} (hP : IsPGroup 2 ↥P) {u v : G} (hu : u ∈ P)
    (hv : v ∈ P) (hN : Odd (Nat.card ↥N)) (h : u⁻¹ * v ∈ N) : u = v := by
  have h1 : u⁻¹ * v ∈ P := P.mul_mem (P.inv_mem hu) hv
  have h2 : u⁻¹ * v = 1 :=
    eq_one_of_isPGroup_of_mem_odd hN h (hP.to_le (Subgroup.zpowers_le.mpr h1))
  calc u = u * (u⁻¹ * v) := by rw [h2, mul_one]
    _ = v := by group

theorem eq_of_conj_mem_oddCoreOf {P : Subgroup G} (hP : IsPGroup 2 ↥P) {u v : G} (hu : u ∈ P)
    (hv : v ∈ P) (Y : Subgroup G) (g : G) (h : g * (u⁻¹ * v) * g⁻¹ ∈ oddCoreOf Y) : u = v := by
  refine eq_of_mul_mem_odd hP hu hv (oddCoreOf_odd_natCard (conjSub g⁻¹ Y)) ?_
  rw [oddCoreOf_conjSub_eq]
  have := conj_mem_conjSub (n := g⁻¹) h
  simpa [mul_assoc] using this

end Odd

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem conj_zt_mul_inv_mem_of_conj (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n : G}
    (hn : conjSub n K = K ∨ conjSub n J = K) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  rcases hn with hn | hn
  · refine conj_zt_mul_inv_mem_oddCoreOf hs hX ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hs.hz.conj_eq hn
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h1]
  · have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
    have hNΩ : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK
    have hKN : K ∈ omegaNbr Ω (conjSub n K) := by
      have := omegaNbr_conj hΩ.conjInvariant hs.hJ n
      rwa [hn] at this
    have hN : conjSub n K ∈ omegaNbr Ω K :=
      T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hNΩ hK hKN
    have hy : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) := hs.hz.conj n
    have h1 := mul_inv_mem_oddCoreOf_of_mem_omegaNbr hs hX hN hy
    have hnt : n * t * n⁻¹ = z := by
      have := hs.ht.conj n
      rw [hn] at this
      exact (hs.hz.eq this).symm
    have e : n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * t⁻¹ := by
      calc n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) * (z * t)⁻¹ := by group
        _ = (n * z * n⁻¹) * z * (t⁻¹ * z⁻¹) := by rw [hnt]; group
        _ = (n * z * n⁻¹) * (z * t⁻¹ * z⁻¹) := by group
        _ = (n * z * n⁻¹) * t⁻¹ := by
          have : z * t⁻¹ * z⁻¹ = t⁻¹ := by
            have h2 : z * t⁻¹ = t⁻¹ * z := by
              have h3 : t * z = z * t := hzt.symm
              calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
                _ = t⁻¹ * (z * t) * t⁻¹ := by rw [h3]
                _ = t⁻¹ * z := by group
            rw [h2]; group
          rw [this]
    rw [e]
    exact h1

end Cert

end T8R

end CFSG.ClassicalInvolution.Asc77
