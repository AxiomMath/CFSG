module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB10
public import CFSG.ClassicalInvolution.Q3.Q3AMDB01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

theorem normalizes_of_commutes_sylow [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod Ω)
    {A R V : Subgroup G} (hA : A ∈ Ω) (hR : IsSylow2In R A) (hRΩ : R ∈ RSet Ω)
    (hc : Commutes V R) : ∀ y ∈ V, conjSub y A = A := by
  intro y hy
  have hAy : conjSub y A ∈ Ω := hΩ.conjInvariant y A hA
  have hRy : R ≤ conjSub y A := by
    intro x hx
    rw [mem_conjSub_iff]
    have hxy : y⁻¹ * x * y = x := by
      have := hc y hy x hx
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [this]
        _ = x := by group
    rw [hxy]
    exact hR.1 hx
  have h4 : 4 ≤ Nat.card R := by have := hΩ.eight_le_of_mem_RSet hRΩ; omega
  exact (hΩ.eq_of_le_of_le hA hAy hR.2.1 h4 hR.1 hRy).symm

theorem conj_mem_oddCoreOf_conjSub {H : Subgroup G} {g o : G} (ho : o ∈ oddCoreOf H) :
    g * o * g⁻¹ ∈ oddCoreOf (conjSub g H) := by
  rw [Thompson.oddCoreOf_conjSub_eq]
  exact conj_mem_conjSub ho

theorem conjSub_oddCoreOf_inf (g : G) (J K' : Subgroup G) :
    conjSub g (oddCoreOf J ⊓ oddCoreOf K') =
      oddCoreOf (conjSub g J) ⊓ oddCoreOf (conjSub g K') := by
  rw [Thompson.oddCoreOf_conjSub_eq, Thompson.oddCoreOf_conjSub_eq]
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_inf]

theorem mem_normalizer_oddCoreOf_inf {g : G} {J K' : Subgroup G}
    (h : (conjSub g J = J ∧ conjSub g K' = K') ∨ (conjSub g J = K' ∧ conjSub g K' = J)) :
    g ∈ Subgroup.normalizer ((oddCoreOf J ⊓ oddCoreOf K' : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq, conjSub_oddCoreOf_inf]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, inf_comm]

theorem odd_natCard_oddCoreOf_inf [Finite G] (J K' : Subgroup G) :
    Odd (Nat.card ↥(oddCoreOf J ⊓ oddCoreOf K')) :=
  (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

end Elementary

section Swap


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem PspSetting.conjSub_swap (hset : PspSetting Ω K J S R T W z t K') {e : G}
    (hsw : e * t * e⁻¹ = z * t) : conjSub e J = K' := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt := hset.noTwins_all hset.nbrK.1
  exact hnt (conjSub e J) ⟨hΩ.conjInvariant e J hstd.hJ.1, z * t, hset.uniq_mul,
    hsw ▸ hstd.ht.conj e⟩

theorem PspSetting.cross_mem_oddCore (hset : PspSetting Ω K J S R T W z t K') {t₁ t₂ t₃ : G}
    {R₁ R₂ R₃ : Subgroup G} (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃) {e : G}
    (hee : e * e = 1) (hsw : e * t * e⁻¹ = z * t) :
    ∀ x ∈ R₂, ∀ y ∈ R₂, ⁅x, e * y * e⁻¹⁆ ∈ oddCoreOf J ⊓ oddCoreOf K' := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hK'Ω : K' ∈ Ω := hset.nbrK.1
  have hJe : conjSub e J = K' := hset.conjSub_swap hsw
  have hK'e : conjSub e K' = J := by
    rw [← hJe, ← conjSub_mul, hee, conjSub_one]
  obtain ⟨eK'⟩ := hset.exists_iso_of_mem hK'Ω
  have hR₃Ω : R₃ ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hax.syl₃
  have hR₂K' : ∀ y ∈ R₂, conjSub y K' = K' :=
    normalizes_of_commutes_sylow hΩ hK'Ω hax.syl₃ hR₃Ω hax.comm₂₃
  have key : ∀ x ∈ R₂, ∀ k ∈ K', ⁅x, k⁆ ∈ oddCoreOf K' := by
    intro x hx k hk
    refine badEdge_centSylow_three_modOdd eK' hax.syl₃ hR₂K' ?_ k hk x hx
    intro r hr v hv
    have : v * r = r * v := hax.comm₂₃ v hv r hr
    rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
    exact (oddCoreOf K').one_mem
  have hconj : ∀ y ∈ R₂, e * y * e⁻¹ ∈ K' := fun y hy =>
    hJe ▸ conj_mem_conjSub (hax.syl₂.1 hy)
  intro x hx y hy
  refine ⟨?_, key x hx _ (hconj y hy)⟩
  have h1 : ⁅y, e * x * e⁻¹⁆ ∈ oddCoreOf K' := key y hy _ (hconj x hx)
  have h2 : e * ⁅y, e * x * e⁻¹⁆ * e⁻¹ ∈ oddCoreOf J := by
    have := conj_mem_oddCoreOf_conjSub (g := e) h1
    rwa [hK'e] at this
  have h3 : e * ⁅y, e * x * e⁻¹⁆ * e⁻¹ = ⁅e * y * e⁻¹, x⁆ := by
    have hee' : e⁻¹ * e⁻¹ = 1 := by rw [← mul_inv_rev, hee, inv_one]
    have e1 : e * (e * x * e⁻¹) * e⁻¹ = x := by
      rw [show e * (e * x * e⁻¹) * e⁻¹ = (e * e) * x * (e⁻¹ * e⁻¹) by group, hee, hee', one_mul,
        mul_one]
    calc e * ⁅y, e * x * e⁻¹⁆ * e⁻¹ = ⁅e * y * e⁻¹, e * (e * x * e⁻¹) * e⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅e * y * e⁻¹, x⁆ := by rw [e1]
  rw [h3] at h2
  have h4 : ⁅x, e * y * e⁻¹⁆ = (⁅e * y * e⁻¹, x⁆)⁻¹ := (commutatorElement_inv _ _).symm
  rw [h4]
  exact (oddCoreOf J).inv_mem h2

end Swap

end CFSG.ClassicalInvolution.Q3.Q3AM
