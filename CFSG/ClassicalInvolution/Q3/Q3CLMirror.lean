module

public import CFSG.ClassicalInvolution.Q3.Q3CLFrame

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

namespace T8R.Loc

open CFSG.ClassicalInvolution.Asc77.T8R.Loc
  CFSG.ClassicalInvolution.Asc77.T8R
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

theorem eq_of_mem_conj_sylow_of (hs : Std8Frame Ω K J S R T W z t) {n : G}
    (hs' : Std8Frame Ω (conjSub n K) (conjSub n J) (conjSylow n S) (conjSub n R) (conjSub n T)
      (conjSub n W) (n * z * n⁻¹) (n * t * n⁻¹))
    (hRT : conjSub n R ≠ conjSub n T)
    (hfs : ∀ {s : G}, s ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) →
      (conjSub s (conjSub n R) = conjSub n R ∧ conjSub s (conjSub n T) = conjSub n T) ∨
        (conjSub s (conjSub n R) = conjSub n T ∧ conjSub s (conjSub n T) = conjSub n R))
    (hsw : ∀ {g : G},
      g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) →
        conjSub (g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g) (conjSub n R) = conjSub n T →
          g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g = n * z * n⁻¹ * (n * t * n⁻¹))
    (hc4 : ∀ {g x : G},
      g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g ∈ ((conjSylow n S : Sylow 2 G) : Subgroup G) →
        x ∈ conjSub n K → orderOf x = 4 →
          x * (g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g) =
              (g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g) * x →
            g⁻¹ * (n * z * n⁻¹ * (n * t * n⁻¹)) * g = n * z * n⁻¹ * (n * t * n⁻¹))
    (hzO : ∀ {y : G}, y ∈ Subgroup.centralizer ({z} : Set G) →
      ∃ O : Subgroup G, Odd (Nat.card O) ∧ y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ O)
    (htO : ∀ {y : G}, y ∈ Subgroup.centralizer ({t} : Set G) →
      ∃ O : Subgroup G, Odd (Nat.card O) ∧ y * (t * z) * y⁻¹ * (t * z)⁻¹ ∈ O)
    (h93 : ∀ K₀ ∈ Ω, ∀ z₀ : G, IsUniqueInvolution K₀ z₀ →
      ∀ S₀ : Subgroup G, IsSylow2In S₀ (Subgroup.centralizer ({z₀} : Set G)) →
        ∀ U : Subgroup G, U ≤ S₀ → IsElemAbelian2 U 2 → ∀ d ∈ U, d ≠ 1 →
          gamma1 U (S₀ ⊓ ⨆ L ∈ twinSet Ω K₀, L) ≤ Subgroup.centralizer ({d} : Set G) →
            ∃ x ∈ K₀, orderOf x = 4 ∧ x * d = d * x)
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  exact CFSG.ClassicalInvolution.Asc77.T8R.eq_of_mem_conj_sylow_gen hs.hyp hs.hz hs.ht hs.hJ
    hs.noTwins (T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht) hs'.mem hs'.hJ.1 hs'.hz hs'.ht
    hs'.hR hs'.hT
    (Q3CP.l67Gen G Ω hs.hyp (conjSylow n S) (conjSub n R) hs'.hR.1 (conjSub n T) hs'.hT.1
      hs'.hR.2.2 hs'.hT.2.2 hRT)
    hfs hsw hc4 hzO htO h93 hzP htP

theorem outerFusion_of (hs : Std8Frame Ω K J S R T W z t)
    (hcz : ∀ {s : G}, s ∈ (S : Subgroup G) → s * (z * t) * s⁻¹ = z * t)
    (hmir : ∀ {n : G}, z ∈ conjSub n (S : Subgroup G) → t ∈ conjSub n (S : Subgroup G) →
      n * (z * t) * n⁻¹ = z * t) :
    OuterFusion K J S R T z t := by
  intro g hbS hbR hbT _ _
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hTΩ hTJ
  have h8R := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have h8T := Sec6Gen.eight_le_of_mem_RSet hΩ hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  have hzRu : IsUniqueInvolution R z := uniqueInvolution_restrict hs.hz hRK hzR
  have htTu : IsUniqueInvolution T t := uniqueInvolution_restrict hs.ht hTJ htT
  have hz2 : z * z = 1 := hs.hz.sq
  have ht2 : t * t = 1 := hs.ht.sq
  have hz1 : z ≠ 1 := hs.hz.ne_one
  have ht1 : t ≠ 1 := hs.ht.ne_one
  have hzt : z ≠ t := by
    intro h'
    exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
  have hztc : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hbz : (g⁻¹ * (z * t) * g) * z = z * (g⁻¹ * (z * t) * g) := by
    have h : IsUniqueInvolution R ((g⁻¹ * (z * t) * g) * z * (g⁻¹ * (z * t) * g)⁻¹) := by
      have := hzRu.conj (g⁻¹ * (z * t) * g)
      rwa [hbR] at this
    have h' := hzRu.eq h
    calc (g⁻¹ * (z * t) * g) * z
        = ((g⁻¹ * (z * t) * g) * z * (g⁻¹ * (z * t) * g)⁻¹) * (g⁻¹ * (z * t) * g) := by group
      _ = z * (g⁻¹ * (z * t) * g) := by rw [← h']
  have hbt : (g⁻¹ * (z * t) * g) * t = t * (g⁻¹ * (z * t) * g) := by
    have h : IsUniqueInvolution T ((g⁻¹ * (z * t) * g) * t * (g⁻¹ * (z * t) * g)⁻¹) := by
      have := htTu.conj (g⁻¹ * (z * t) * g)
      rwa [hbT] at this
    have h' := htTu.eq h
    calc (g⁻¹ * (z * t) * g) * t
        = ((g⁻¹ * (z * t) * g) * t * (g⁻¹ * (z * t) * g)⁻¹) * (g⁻¹ * (z * t) * g) := by group
      _ = t * (g⁻¹ * (z * t) * g) := by rw [← h']
  obtain ⟨U, hUel, hzU, htU, hUenum⟩ := exists_fourGroup hz2 ht2 hz1 ht1 hzt hztc
  have hU2 : IsPGroup 2 ↥U := IsPGroup.of_card (n := 2) hUel.1
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := hcz hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  have hQC : ∀ y ∈ U, y * (g⁻¹ * (z * t) * (g⁻¹)⁻¹) = (g⁻¹ * (z * t) * (g⁻¹)⁻¹) * y := by
    intro y hy
    rw [inv_inv]
    rcases hUenum y hy with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      exact hbz.symm
    · rw [h]
      exact hbt.symm
    · rw [h]
      exact Commute.mul_left (a := z) (b := t) (c := g⁻¹ * (z * t) * g) hbz.symm hbt.symm
  obtain ⟨n', hn', hUn'⟩ := exists_conj_sylow_of_le_centralizer S haS hU2 hQC
  have key := hmir (hUn' hzU) (hUn' htU)
  rw [inv_inv] at hn'
  rw [← hn']
  exact key

end T8R.Loc

end CFSG.ClassicalInvolution.Q3.Q3CL
